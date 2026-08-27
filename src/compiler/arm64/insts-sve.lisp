;;; SVE, SVE2, SME, SME2

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB-ARM64-ASM")

(define-arg-type predicate :printer #'print-predicate)
(define-arg-type sve-reg :printer #'print-sve-reg)
(define-arg-type sve-reg-half :printer #'print-sve-reg-half)
(define-arg-type sve-reg-d :printer #'print-sve-reg-d)
(define-arg-type imm9 :printer #'print-imm9)
(define-arg-type sve-shift-imm :printer #'print-sve-shift-imm)
(define-arg-type sve-unpred-shift-imm :printer #'print-sve-unpred-shift-imm)
(define-arg-type sve-shift-reg :printer #'print-sve-shift-reg)
(define-arg-type sve-imm13-reg :printer #'print-sve-imm13-reg)
(define-arg-type sve-imm13-const :printer #'print-sve-imm13-const)
(define-arg-type sve-dup-imm :printer #'print-sve-dup-imm)
(define-arg-type imm8-ext :printer #'print-imm8-ext)
(define-arg-type sve-reg-pair :printer #'print-sve-reg-consecutive-pair)
(define-arg-type sve-shift-insert-imm :printer #'print-sve-shift-insert-imm)
(define-arg-type sve-indexed-reg :printer #'print-sve-indexed-reg)
(define-arg-type sve-indexed-target-reg :printer #'print-sve-indexed-target-reg)

;; define-instruction-format + def-emitter
(defmacro def-instruction-format (name print &body arg-specs)
  (let* ((arg-specs (loop for spec in arg-specs
                          for i from 0
                          collect (if (symbolp (car spec))
                                      spec
                                      (destructuring-bind (size pos name &rest options)
                                          spec
                                          (if (integerp name)
                                              (list* (symbolicate "VALUE-" i)
                                                     :value name
                                                     :field `(byte ,size ,pos)
                                                     options)
                                              (list* name
                                                     :field `(byte ,size ,pos)
                                                     options))))))
         (emitter-clauses
           (loop for (name . plist) in arg-specs
                 for field = (getf plist :field)
                 for value = (getf plist :value)
                 when (and (typep field '(cons (eql byte))))
                 collect (list (or value name)
                               (second field)
                               (third field)))))
    `(progn
       (def-emitter ,name
         ,@emitter-clauses)
       (define-instruction-format (,name 32 :default-printer '(:name :tab ,@print))
         ,@(loop for (name . plist) in arg-specs
                 for print-fields = (loop for p in (getf plist :print-fields) collect `(byte ,@p))
                 for field = (getf plist :field)
                 collect (if print-fields
                             `(,name :fields
                                     (list ,@(if field (list field))
                                           ,@print-fields)
                                     ,@(sb-vm::remove-keywords plist '(:field :print-fields)))
                             `(,name ,@plist)))))))

;;; Reconcile name clashes between neon and sve by adding sve- to the
;;; name and a :print-name without it.
;;; inst* will call sve-intercept to decide between the two.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (dolist (alias '(ldr str and ands bic bics orr eor lsl lsr asr dup ext
                   sli sri tbl tbx cls clz cnt fabs fneg not
                   mul pmul smulh umulh sub add))
    (setf (get alias :intercept)
          (cons 'sve-intercept (symbolicate 'sve- alias)))))

(defun sve-intercept (mnemonic alternative &rest args)
  (#-sb-xc-host do-rest-arg #-sb-xc-host ((arg) args 0 mnemonic)
   #+sb-xc-host dolist #+sb-xc-host (arg args mnemonic)
    (when (or (predicate-p arg)
              (sve-reg-p arg))
      (return alternative))))

(defmacro def-sve-alias (&whole whole name lambda-list &body body)
  (if (get name :intercept)
      (let* ((transformed-body
               (mapcar
                (lambda (clause)
                  (if (typep clause '(cons (eql :printer)))
                      (destructuring-bind (format fields &optional (fmt nil fmt-p) &rest rest)
                          (cdr clause)
                        `(:printer ,format ,fields
                                   ,@(if fmt-p (list fmt) '(:default))
                                   ,@rest
                                   :print-name ',name))
                      clause))
                body)))
        `(define-instruction ,(symbolicate 'sve- name) ,lambda-list
           ,@transformed-body))
      `(define-instruction ,@(cdr whole))))

(defun predicate-p (thing)
  (and (tn-p thing)
       (eq (sb-name (sc-sb (tn-sc thing))) 'sb-vm::predicate-registers)))

(defun sve-reg-p (thing)
  (and (tn-p thing)
       (eq (sc-name (tn-sc thing)) 'sb-vm::sve-reg)))

(defun predicate-offset (tn)
  (aver (predicate-p tn))
  (tn-offset tn))

(defun lane-size (lane)
  (or (position lane '(:b :h :s :d))
      (error "Bad lane size: ~a, should be one of :b :h :s :d" lane)))

(defun lane-size-sans-b (lane)
  (ecase lane
    (:h 1)
    (:s 2)
    (:d 3)))

(defun lane-size-sans-d (lane)
  (ecase lane
    (:b 0)
    (:h 1)
    (:s 2)))

(defun encode-pattern (pattern)
  (or (getf '(:all   #b11111 :pow2  #b00000 :vl1   #b00001 :vl2   #b00010 :vl3   #b00011
              :vl4   #b00100 :vl5   #b00101 :vl6   #b00110 :vl7   #b00111 :vl8   #b01000
              :vl16  #b01001 :vl32  #b01010 :vl64  #b01011 :vl128 #b01100 :vl256 #b01101
              :mul4  #b11101 :mul3  #b11110)
            pattern)
      (error "Unknown pattern ~a" pattern)))

(defun encode-shift-imm (size shift direction)
  (let ((esize (ecase size
                 (:b 8)
                 (:h 16)
                 (:s 32)
                 (:d 64))))
    (ecase direction
      (:left
       (assert (<= 0 shift (1- esize)) (shift)
               "Left shift ~a out of range [0, ~a]" shift (1- esize))
       (+ esize shift))
      (:right
       (assert (<= 1 shift esize) (shift)
               "Right shift ~a out of range [1, ~a]" shift esize)
       (- (* 2 esize) shift)))))

(defun sve-element-size (size)
  (ecase size
    ((:b 0 8) 8)
    ((:h 1 16) 16)
    ((:s 2 32) 32)
    ((:d 3 64) 64)))

(defun encode-sve-logical-immediate (val size)
  (let* ((esize (sve-element-size size))
         (val (ldb (byte esize 0) val)))
    (when (or (zerop val) (= val (1- (ash 1 esize))))
      (error "Cannot encode 0 or all-ones as SVE logical immediate: #x~x" val))
    ;; smallest repeating power-of-2 sub-element length
    (let ((len (loop for l in '(2 4 8 16 32 64)
                     when (and (<= l esize)
                               (loop for pos from l below esize by l
                                     always (= (ldb (byte l 0) val)
                                               (ldb (byte l pos) val))))
                     return l)))
      (unless len
        (error "Invalid SVE logical immediate: #x~x is not a repeating pattern for size ~a" val size))

      (let* ((pattern (ldb (byte len 0) val))
             (doubled (logior pattern (ash pattern len)))
             (run-length (logcount pattern))
             ;; rotation amount r
             (r (loop for rot below len
                      when (= (ldb (byte len rot) doubled)
                              (1- (ash 1 run-length)))
                      return (mod (- len rot) len))))
        (unless r
          (error "Pattern #x~x is not a valid rotated contiguous run of 1s" pattern))
        (let* ((s (1- run-length))
               (n (if (= len 64) 1 0))
               (prefix (ecase len
                         (64 #b000000)
                         (32 #b000000)
                         (16 #b100000)
                         (8  #b110000)
                         (4  #b111000)
                         (2  #b111100)))
               (imms (logior prefix s)))
          (dpb n (byte 1 12) (dpb r (byte 6 6) imms)))))))

(defun encode-sve-mul-indexed (size zm index)
  (let ((zm-offset (reg-offset zm)))
    (case size
      (:h
       (assert (and (<= 0 index 7) (<= 0 zm-offset 7)) (index zm)
               "Index [0..7] and Zm [Z0..Z7] required for .H indexed multiply")
       (values (ldb (byte 1 2) index)
               (logior (ash (ldb (byte 2 0) index) 3) zm-offset)))
      (:s
       (assert (and (<= 0 index 3) (<= 0 zm-offset 7)) (index zm)
               "Index [0..3] and Zm [Z0..Z7] required for .S indexed multiply")
       (values #b10
               (logior (ash (ldb (byte 2 0) index) 3) zm-offset)))
      (:d
       (assert (and (<= 0 index 1) (<= 0 zm-offset 15)) (index zm)
               "Index [0..1] and Zm [Z0..Z15] required for .D indexed multiply")
       (values #b11
               (logior (ash (ldb (byte 1 0) index) 4) zm-offset)))
      (t (error "Indexed multiply does not support size ~a" size)))))


(def-instruction-format sve-predicate-initialize (pd pattern)
  (8 24 #b00100101)
  (2 22 size)
  (5 17 #b01100)
  (1 16 s)
  (6 10 #b111000)
  (5 5 pattern :printer #'print-pattern)
  (5 0 pd :print-fields ((2 22)) :type 'predicate))

(define-instruction ptrue (segment pd size &optional (pattern :all))
  (:printer sve-predicate-initialize ((s 0)))
  (:emitter
   ;; TODO: handle "predicate as counter"
   (emit-sve-predicate-initialize segment (lane-size size) 0 (encode-pattern pattern) (predicate-offset pd))))

(define-instruction ptrues (segment pd size &optional (pattern :all))
  (:printer sve-predicate-initialize ((s 1)))
  (:emitter
   (emit-sve-predicate-initialize segment (lane-size size) 1 (encode-pattern pattern) (predicate-offset pd))))

(def-instruction-format sve-stack-frame-size (rd ", " imm)
  (9 23 #b000001001)
  (1 22 op)
  (1 21 #b1)
  (5 16 opc2)
  (4 12 #b0101)
  (1 11 stream)
  (6 5 imm :type 'immediate)
  (5 0 rd :type 'x-reg))

(define-instruction rdvl (segment rd multiplier)
  (:printer sve-stack-frame-size ((op 0) (opc2 #b11111) (stream 0)))
  (:emitter
   (emit-sve-stack-frame-size segment 0 #b11111 0 multiplier (reg-offset rd))))

(def-instruction-format sve-while (pd ", " rn ", " rm)
  (8 24 #b00100101)
  (2 22 size)
  (1 21  #b1)
  (5 16 rm :print-fields ((1 12)) :type 'sized-reg)
  (3 13 #b0)
  (1 12 sf)
  (1 11 u)
  (1 10 lt)
  (5 5 rn :print-fields ((1 12)) :type 'sized-reg)
  (1 4 eq)
  (4 0 pd :print-fields ((2 22)) :type 'predicate))

(make-defs ((($name $u $lt $eq)
             (whilege 0 0 0)
             (whilegt 0 0 1)
             (whilelt 0 1 0)
             (whilele 0 1 1)
             (whilehs 1 0 0)
             (whilehi 1 0 1)
             (whilelo 1 1 0)
             (whilels 1 1 1)))
  (define-instruction $name (segment pd rn rm size)
    (:printer sve-while ((u $u) (lt $lt) (eq $eq)))
    (:emitter
     (emit-sve-while segment
                     (lane-size size)
                     (reg-offset rm)
                     (reg-size rn)
                     $u $lt
                     (reg-offset rn)
                     $eq
                     (predicate-offset pd)))))

(def-instruction-format sve-predicate-count (rd ", " pg ", " pn)
  (8 24 #b00100101)
  (2 22 size)
  (3 19 #b100)
  (3 16 opc)
  (2 14 #b10)
  (4 10 pg :type 'predicate)
  (1 9 #b0)
  (4 5 pn :print-fields ((2 22)) :type 'predicate)
  (5 0 rd :type 'x-reg))

(make-defs ((($name $opc)
             (cntp   #b000)
             (firstp #b001)
             (lastp  #b010)))
  (define-instruction $name (segment rd pg pn size)
    (:printer sve-predicate-count ((opc $opc)))
    (:emitter
     (emit-sve-predicate-count segment
                               (lane-size size)
                               $opc
                               (predicate-offset pg)
                               (predicate-offset pn)
                               (reg-offset rd)))))

(def-instruction-format sve-element-count (rd pattern (:unless (imm :constant 0) ", MUL #" (+ imm 1)))
  (8 24 #b00000100)
  (2 22 size)
  (2 20 #b10)
  (4 16 imm)
  (6 10 #b111000)
  (5 5  pattern :printer #'print-pattern)
  (5 0  rd :type 'x-reg))

(make-defs ((($name $size)
             (cntb #b00)
             (cnth #b01)
             (cntw #b10)
             (cntd #b11)))
  (define-instruction $name (segment rd &optional (pattern :all) (multiplier 1))
    (:printer sve-element-count ((size $size)))
    (:emitter
     (emit-sve-element-count segment
                             $size
                             (1- multiplier)
                             (encode-pattern pattern)
                             (gpr-offset rd)))))

(def-instruction-format sve-compare-signed-imm (pd ", " pg "/Z, " zn ", " imm)
  (8 24 #b00100101)
  (2 22 size)
  (1 21 #b0)
  (5 16 imm :type 'immediate)
  (1 15 op)
  (1 14 #b0)
  (1 13 o4)
  (3 10 pg :type 'predicate)
  (5 5 zn :print-fields ((2 22)) :type 'sve-reg)
  (1 4 ne)
  (4 0 pd :print-fields ((2 22)) :type 'predicate))

(def-instruction-format sve-compare-unsigned-imm (pd ", " pg "/Z, " zn ", " imm)
  (8 24 #b00100100)
  (2 22 size)
  (1 21 #b1)
  (7 14 imm :type 'unsigned-immediate)
  (1 13 lt)
  (3 10 pg :type 'predicate)
  (5 5 zn  :print-fields ((2 22)) :type 'sve-reg)
  (1 4 ne)
  (4 0 pd  :print-fields ((2 22)) :type 'predicate))

(def-instruction-format sve-compare-vectors (pd ", " pg "/Z, " zn ", " zm)
  (8 24 #b00100100)
  (2 22 size)
  (1 21 #b0)
  (5 16 zm :print-fields ((2 22)) :type 'sve-reg)
  (3 13 opc)
  (3 10 pg :type 'predicate)
  (5 5 zn  :print-fields ((2 22)) :type 'sve-reg)
  (1 4 ne)
  (4 0 pd  :print-fields ((2 22)) :type 'predicate))


(make-defs ((($name $imm $imm-o4 $opc $wide $ne)
             (cmpeq   1 0 #b101 #b001 0)
             (cmpne   1 0 #b101 #b001 1)
             (cmpge   0 0 #b100 #b010 0)
             (cmpgt   0 0 #b100 #b010 1)
             (cmplt   0 1 nil   #b011 0)
             (cmple   0 1 nil   #b011 1)))
  (define-instruction $name (segment pd pg zn zn-size zm &optional (zm-size zn-size))
    (:printer sve-compare-signed-imm ((op $imm) (o4 $imm-o4) (ne $ne)))
    (:printer sve-compare-vectors ((opc $wide) (ne $ne)))
    ($when $opc
           (:printer sve-compare-vectors ((opc $opc) (ne $ne))))
    (:emitter
     (if (integerp zm)
         (emit-sve-compare-signed-imm segment (lane-size zn-size) zm
                                      $imm $imm-o4 (predicate-offset pg)
                                      (reg-offset zn) $ne (predicate-offset pd))
         (let ((wide-p (not (eq zn-size zm-size))))
           (if wide-p
               (if (and (member zm-size '(:d))
                        (member zn-size '(:b :h :s)))
                   (emit-sve-compare-vectors segment (lane-size zn-size) (reg-offset zm)
                                             $wide
                                             (predicate-offset pg) (reg-offset zn)
                                             $ne (predicate-offset pd))
                   (error "Invalid wide sizes: ~a vs ~a" zn-size zm-size))
               ($when $opc
                      (emit-sve-compare-vectors segment (lane-size zn-size) (reg-offset zm)
                                                $opc
                                                (predicate-offset pg) (reg-offset zn)
                                                $ne (predicate-offset pd)))))))))

(make-defs ((($name $lt $opc $wide $ne)
             (cmphs   0 #b000 #b110 0)
             (cmphi   0 #b000 #b110 1)
             (cmplo   1 nil   #b111 0)
             (cmpls   1 nil   #b111 1)))
  (define-instruction $name (segment pd pg zn zn-size zm &optional (zm-size zn-size))
    (:printer sve-compare-unsigned-imm ((lt $lt) (ne $ne)))
    (:printer sve-compare-vectors ((opc $wide) (ne $ne)))
    ($when $opc
           (:printer sve-compare-vectors ((opc $opc) (ne $ne))))
    (:emitter
     (if (integerp zm)
         (emit-sve-compare-unsigned-imm segment (lane-size zn-size)
                                        zm
                                        $lt (predicate-offset pg)
                                        (reg-offset zn) $ne (predicate-offset pd))
         (let ((wide-p (not (eq zn-size zm-size))))
           (if wide-p
               (if (and (member zm-size '(:d))
                        (member zn-size '(:b :h :s)))
                   (emit-sve-compare-vectors segment (lane-size zn-size) (reg-offset zm)
                                             $wide
                                             (predicate-offset pg) (reg-offset zn)
                                             $ne (predicate-offset pd))
                   (error "Invalid wide sizes: ~a vs ~a" zn-size zm-size))
               ($when $opc
                      (emit-sve-compare-vectors segment (lane-size zn-size) (reg-offset zm)
                                                $opc
                                                (predicate-offset pg) (reg-offset zn)
                                                $ne (predicate-offset pd)))))))))

(def-instruction-format sve-contiguous-mem-imm (zt ", " pg ", [" rn (:unless (:constant 0) imm ", MUL VL") "]")
  (1 31 #b1)
  (1 30 st)
  (5 25 #b10010)
  (2 23 msz)
  (2 21 esize)
  (1 20 #b0)
  (4 16 imm :type 'immediate)
  (1 15 #b1)
  (1 14 st2)
  (1 13 #b1)
  (3 10 pg :type 'predicate)
  (5 5 rn  :type 'x-reg)
  (5 0 zt  :print-fields ((2 21)) :type 'sve-reg))

(def-instruction-format sve-contiguous-mem-reg (zt ", " pg ", [" rn ", " rm "]")
  (1 31 #b1)
  (1 30 st)
  (5 25 #b10010)
  (2 23 msz)
  (2 21 esize)
  (5 16 rm :type 'x-reg)
  (3 13 #b010)
  (3 10 pg :type 'predicate)
  (5 5 rn :type 'x-reg)
  (5 0 zt :print-fields ((2 21)) :type 'sve-reg))

(make-defs ((($name $st $msz)
             (ld1b 0 #b00)
             (ld1h 0 #b01)
             (ld1w 0 #b10)
             (ld1d 0 #b11)
             (st1b 1 #b00)
             (st1h 1 #b01)
             (st1w 1 #b10)
             (st1d 1 #b11)))
  (define-instruction $name (segment zt pg address size)
    (:printer sve-contiguous-mem-imm ((st $st) (msz $msz) (st2 $st)))
    (:printer sve-contiguous-mem-reg ((st $st) (msz $msz)))
    (:emitter
     (let ((base (memory-operand-base address))
           (offset (memory-operand-offset address)))
       (cond
         ;; [Rn, #imm4, MUL VL]
         ((integerp offset)
          (emit-sve-contiguous-mem-imm segment
                                       $st
                                       $msz
                                       (lane-size size)
                                       offset
                                       $st
                                       (predicate-offset pg)
                                       (gpr-offset base)
                                       (reg-offset zt)))

         ;; [Rn, Rm]
         ((register-p offset)
          (emit-sve-contiguous-mem-reg segment
                                       $st
                                       $msz
                                       (lane-size size)
                                       (reg-offset offset)
                                       (predicate-offset pg)
                                       (gpr-offset base)
                                       (reg-offset zt)))
         (t
          (error "Invalid SVE memory address: ~s" address)))))))

(def-instruction-format sve-ldr-str-vector (zt ", [" base ", "  imm ", MUL VL]")
  (7 25 o1)
  (3 22 #b110)
  (6 16 imm9h)
  (3 13 #b010)
  (3 10 imm9l)
  (5 5 base  :type 'x-reg)
  (5 0 zt  :type 'sve-reg)
  (imm :print-fields ((6 16) (3 10)) :type 'imm9))

(def-instruction-format sve-ldr-str-predicate (pt ", [" base ", " imm ", MUL VL]")
  (7 25 o1)
  (3 22 #b110)
  (6 16 imm9h)
  (3 13 #b000)
  (3 10 imm9l)
  (5 5 base  :type 'x-reg)
  (1 4 #b0)
  (4 0 pt :type 'predicate)
  (imm :print-fields ((6 16) (3 10)) :type 'imm9))

(make-defs ((($name $o1)
             (ldr #b1000010)
             (str #b1110010)))

  (def-sve-alias $name (segment reg address)
    (:printer sve-ldr-str-vector    ((o1 $o1)))
    (:printer sve-ldr-str-predicate ((o1 $o1)))
    (:emitter
     (let* ((base   (memory-operand-base address))
            (offset (or (memory-operand-offset address) 0))
            (imm9h  (ldb (byte 6 3) offset))
            (imm9l  (ldb (byte 3 0) offset)))
       (if (predicate-p reg)
           (emit-sve-ldr-str-predicate segment
                                       $o1
                                       imm9h
                                       imm9l
                                       (gpr-offset base)
                                       (predicate-offset reg))
           (emit-sve-ldr-str-vector segment
                                    $o1
                                    imm9h
                                    imm9l
                                    (gpr-offset base)
                                    (reg-offset reg)))))))

(def-instruction-format sve-unpack-vector (zd ", " zn)
  (8 24 #b00000101)
  (2 22 size)
  (4 18 #b1100)
  (2 16 uh)
  (6 10 #b001110)
  (5 5 zn :print-fields ((2 22)) :type 'sve-reg-half)
  (5 0 zd :print-fields ((2 22)) :type 'sve-reg))

(make-defs ((($name $uh)
             (sunpklo #b00)
             (sunpkhi #b01)
             (uunpklo #b10)
             (uunpkhi #b11)))
  (define-instruction $name (segment zd size zn)
    (:printer sve-unpack-vector ((uh $uh)))
    (:emitter
     (emit-sve-unpack-vector segment
                             (lane-size-sans-b size)
                             $uh
                             (reg-offset zn)
                             (reg-offset zd)))))

(def-instruction-format sve-unpack-predicate (pd ", " pn)
  (15 17 #b000001010011000)
  (1 16 h)
  (7 9 #b0100000)
  (4 5 pn :type 'predicate)
  (1 4 #b0)
  (4 0 pd :type 'predicate))

(make-defs ((($name $h)
             (punpklo 0)
             (punpkhi 1)))
  (define-instruction $name (segment pd pn)
    (:printer sve-unpack-predicate ((h $h)))
    (:emitter
     (emit-sve-unpack-predicate segment
                                $h
                                (predicate-offset pn)
                                (predicate-offset pd)))))

(def-instruction-format sve-inc-dec-vector (zdn pattern (:unless (:constant 0) ", MUL " imm))
  (8 24 #b00000100)
  (2 22 size)
  (2 20 #b11)
  (4 16 imm  :type 'immediate)
  (5 11 #b11000)
  (1 10 d)
  (5 5 pattern  :printer #'print-pattern)
  (5 0 zdn  :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-inc-dec-scalar (rdn pattern (:unless (:constant 0) ", MUL " imm))
  (8 24 #b00000100)
  (2 22 size)
  (2 20 #b11)
  (4 16 imm :type 'immediate)
  (5 11 #b11100)
  (1 10 d)
  (5 5 pattern :printer #'print-pattern)
  (5 0 rdn :type 'x-reg))

(make-defs ((($name $d $size $vector-p)
             (incb 0 #b00 nil)
             (decb 1 #b00 nil)
             (inch 0 #b01 t)
             (dech 1 #b01 t)
             (incw 0 #b10 t)
             (decw 1 #b10 t)
             (incd 0 #b11 t)
             (decd 1 #b11 t)))
  (define-instruction $name (segment reg &optional (pattern :all) (multiplier 1))
    ($when $vector-p
           (:printer sve-inc-dec-vector ((size $size) (d $d))))
    (:printer sve-inc-dec-scalar ((size $size) (d $d)))
    (:emitter
     (check-type multiplier (integer 1 16))
     (let ((imm (1- multiplier))
           (pat (encode-pattern pattern)))
       (cond ($when $vector-p
              ((sve-reg-p reg)
               (emit-sve-inc-dec-vector segment
                                        $size
                                        imm
                                        $d
                                        pat
                                        (reg-offset reg))))
             (t

              (emit-sve-inc-dec-scalar segment
                                       $size
                                       imm
                                       $d
                                       pat
                                       (gpr-offset reg))))))))

(def-instruction-format sve-predicate-logical (pd ", " pg "/Z, " pn ", " pm)
  (9 23 #b001001010)
  (1 22 s)
  (2 20 #b00)
  (4 16 pm :type 'predicate)
  (2 14 #b01)
  (4 10 pg :type 'predicate)
  (1 9 o2)
  (4 5 pn :type 'predicate)
  (1 4 o3)
  (4 0 pd :type 'predicate))

(def-instruction-format sve-bitwise-predicated (zdn ", " pg "/M, " zdn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (3 19 #b011)
  (3 16 opc)
  (3 13 #b000)
  (3 10 pg :type 'predicate)
  (5 5 zm :print-fields ((2 22)) :type 'sve-reg)
  (5 0 zdn :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-bitwise-unpredicated (zd ", " zn ", " zm)
  (8 24 #b00000100)
  (2 22 opc)
  (1 21 #b1)
  (5 16 zm :type 'sve-reg)
  (3 13 #b001)
  (3 10 #b100)
  (5 5 zn  :type 'sve-reg)
  (5 0 zd  :type 'sve-reg))

(def-instruction-format sve-bitwise-imm (zdn ", " zdn ", #" imm)
  (8 24 #b00000101)
  (2 22 opc)
  (4 18 #b0000)
  (13 5 imm :type 'sve-imm13-const)
  (5  0 zdn :print-fields ((13 5)) :type 'sve-imm13-reg))

(make-defs ((($name   $pred      $unpred      $imm     $p-o2  $p-o3)
             (and #b010      #b00         #b10      0         0)
             (bic #b011      #b11         nil       0         1)
             (eor #b001      #b10         #b01      1         0)
             (orr #b000      #b01         #b00      nil       nil)))
  (def-sve-alias $name (segment arg1 arg2 &optional arg3 arg4)
    (:printer sve-bitwise-predicated   ((opc $pred)))
    (:printer sve-bitwise-unpredicated ((opc $unpred)))
    ($when $imm
      (:printer sve-bitwise-imm ((opc $imm))))
    ($when $p-o2
      (:printer sve-predicate-logical ((s 0) (o2 $p-o2) (o3 $p-o3))))
    (:emitter
     (cond
       ($when $p-o2
        ((predicate-p arg1)
         (emit-sve-predicate-logical segment
                                     0
                                     (predicate-offset arg4) ; Pm
                                     (predicate-offset arg2) ; Pg
                                     $p-o2
                                     (predicate-offset arg3) ; Pn
                                     $p-o3
                                     (predicate-offset arg1)))) ; Pd
       ($when $imm
        ((integerp arg3)
         (emit-sve-bitwise-imm segment
                               $imm
                               (encode-sve-logical-immediate arg3 (lane-size arg4))
                               (reg-offset arg1))))  ; Zd
       ((and (sve-reg-p arg1)
             (sve-reg-p arg2)
             (sve-reg-p arg3))
        (emit-sve-bitwise-unpredicated segment
                                       $unpred
                                       (reg-offset arg3)    ; Zm
                                       (reg-offset arg2)    ; Zn
                                       (reg-offset arg1)))
       ((and (sve-reg-p arg1) (predicate-p arg3) arg4)
        (emit-sve-bitwise-predicated segment
                                     (lane-size arg2)
                                     $pred
                                     (predicate-offset arg3) ; Pg
                                     (reg-offset arg4)       ; Zm
                                     (reg-offset arg1)))     ; Zdn

       (t
        (error "Invalid arguments for ~a: ~s ~s ~s ~s" '$name arg1 arg2 arg3 arg4))))))

(make-defs ((($name $s $o2 $o3)
             (ands  1 0 0)
             (bics  1 0 1)
             (eors  1 1 0)))
  (def-sve-alias $name (segment pd pg pn pm)
    (:printer sve-predicate-logical ((s $s) (o2 $o2) (o3 $o3)))
    (:emitter
     (emit-sve-predicate-logical segment
                                 $s
                                 (predicate-offset pm)
                                 (predicate-offset pg)
                                 $o2
                                 (predicate-offset pn)
                                 $o3
                                 (predicate-offset pd)))))

(def-instruction-format sve-sel-vectors (zd ", " pg ", " zn ", " zm)
  (8 24 #b00000101)
  (2 22 size)
  (1 21 #b1)
  (5 16 zm :type 'sve-reg)
  (2 14 #b11)
  (4 10 pg :type 'predicate)
  (5 5  zn :type 'sve-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-reg))

(define-instruction sel (segment arg1 arg2 arg3 arg4 &optional arg5)
  (:printer sve-sel-vectors ())
  (:printer sve-predicate-logical ((s 0) (o2 1) (o3 1)))
  (:emitter
   (cond
     ((and (predicate-p arg1) (null arg5))
      (emit-sve-predicate-logical segment
                                  0                       ; s = 0 (non-flag-setting)
                                  (predicate-offset arg4) ; pm
                                  (predicate-offset arg2) ; pg
                                  1                       ; o2 = 1
                                  (predicate-offset arg3) ; pn
                                  1                       ; o3 = 1
                                  (predicate-offset arg1))) ; pd
     ((and (sve-reg-p arg1) arg5)
      (emit-sve-sel-vectors segment
                            (lane-size arg2)
                            (reg-offset arg5)             ; zm
                            (predicate-offset arg3)       ; pg
                            (reg-offset arg4)             ; zn
                            (reg-offset arg1)))           ; zd

     (t
      (error "Invalid arguments for sel: ~s ~s ~s ~s ~s"
             arg1 arg2 arg3 arg4 arg5)))))


(def-instruction-format sve-shift-imm-predicated (zdn ", " pg "/m, " zdn ", #" imm)
  (8 24 #b00000100)
  (2 22 tszh)
  (2 20 #b00)
  (2 18 opc)
  (1 17 l)
  (1 16 u)
  (3 13 #b100)
  (3 10 pg   :type 'predicate)
  (2 8  tszl)
  (3 5  imm3)
  (5 0  zdn :print-fields ((2 22) (2 8)) :type 'sve-shift-reg)
  (imm :print-fields ((2 22) (2 8) (3 5) (1 17)) :type 'sve-shift-imm))

(def-instruction-format sve-shift-vector-predicated (zdn ", " pg "/m, " zdn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (2 20 #b01)
  (1 19 wide)
  (1 18 r)
  (1 17 l)
  (1 16 u)
  (3 13 #b100)
  (3 10 pg   :type 'predicate)
  (5 5  zm   :type 'sve-reg)
  (5 0  zdn  :type 'sve-reg))

(def-instruction-format sve-shift-wide-unpredicated (zd ", " zn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (1 21 #b1)
  (5 16 zm   :type 'sve-reg)
  (3 13 #b100)
  (1 12 #b0)
  (2 10 opc)
  (5 5  zn   :type 'sve-reg)
  (5 0  zd   :type 'sve-reg))

(def-instruction-format sve-shift-imm-unpredicated (zd ", " zn ", #" imm)
  (8 24 #b00000100)
  (2 22 tszh)
  (1 21 #b1)
  (2 19 tszl)
  (3 16 imm3)
  (3 13 #b100)
  (1 12 #b1)
  (2 10 opc)
  (5 5  zn :print-fields ((2 22) (2 19)) :type 'sve-shift-reg)
  (5 0  zd :print-fields ((2 22) (2 19)) :type 'sve-shift-reg)
  (imm :print-fields ((2 22) (2 19) (3 16) (2 10)) :type 'sve-unpred-shift-imm))

(make-defs ((($name $imm $l $u $unpred $dir)
             (asr #b00 0 0 #b00 :right)
             (lsr #b00 0 1 #b01 :right)
             (lsl #b00 1 1 #b11 :left)))
  (def-sve-alias $name (segment arg1 arg2 arg3 &optional (size :s) (zm-size size))
    (:printer sve-shift-imm-predicated    ((opc $imm) (l $l) (u $u)))
    (:printer sve-shift-vector-predicated ((r 0) (l $l) (u $u)))
    (:printer sve-shift-imm-unpredicated  ((opc $unpred)))
    (:printer sve-shift-wide-unpredicated ((opc $unpred)))

    (:emitter
     (cond
       ((and (predicate-p arg2) (integerp arg3))
        (let ((enc (encode-shift-imm size arg3 $dir)))
          (emit-sve-shift-imm-predicated segment
                                         (ldb (byte 2 5) enc) ; tszh
                                         $imm
                                         $l $u
                                         (predicate-offset arg2)
                                         (ldb (byte 2 3) enc) ; tszl
                                         (ldb (byte 3 0) enc) ; imm3
                                         (reg-offset arg1))))

       ((and (predicate-p arg2) (register-p arg3))
        (let ((wide-p (not (eq size zm-size))))
          (when wide-p
            (unless (and (member zm-size '(:d :dword))
                         (member size '(:b :h :s :byte :half :word)))
              (error "Invalid wide sizes: ~a vs ~a" size zm-size)))
          (emit-sve-shift-vector-predicated segment
                                            (lane-size size)
                                            (if wide-p 1 0)
                                            0 ; r = 0
                                            $l $u
                                            (predicate-offset arg2) ; pg
                                            (reg-offset arg3)       ; zm
                                            (reg-offset arg1))))    ; zdn
       ((integerp arg3)
        (let ((enc (encode-shift-imm size arg3 $dir)))
          (emit-sve-shift-imm-unpredicated segment
                                           (ldb (byte 2 5) enc)
                                           (ldb (byte 2 3) enc)
                                           (ldb (byte 3 0) enc)
                                           $unpred
                                           (reg-offset arg2)        ; zn
                                           (reg-offset arg1))))     ; zd

       ((register-p arg3)
        (emit-sve-shift-wide-unpredicated segment
                                          (lane-size-sans-d size)
                                          (reg-offset arg3)        ; zm
                                          $unpred
                                          (reg-offset arg2)        ; zn
                                          (reg-offset arg1)))      ; zd

       (t
        (error "Invalid arguments for ~a: ~s ~s ~s ~s" '$name arg1 arg2 arg3 size))))))

(make-defs ((($name $opc $l $u $dir)
             (asrd   #b01 0 0 :right)
             (sve-sqshl  #b01 1 0 :left)
             (sve-uqshl  #b01 1 1 :left)
             (sve-srshr  #b11 0 0 :right)
             (sve-urshr  #b11 0 1 :right)
             (sve-sqshlu #b11 1 1 :left)))
  (define-instruction $name (segment zdn size pg shift)
    (:printer sve-shift-imm-predicated ((opc $opc) (l $l) (u $u)))
    (:emitter
     (let ((enc (encode-shift-imm size shift $dir)))
       (emit-sve-shift-imm-predicated segment
                                      (ldb (byte 2 5) enc)
                                      $opc
                                      $l $u
                                      (predicate-offset pg)
                                      (ldb (byte 2 3) enc)
                                      (ldb (byte 3 0) enc)
                                      (reg-offset zdn))))))

(def-instruction-format sve-compact (zd ", " pg ", " zn)
  (8 24 #b00000101)
  (2 22 size)
  (9 13 #b100001100)
  (3 10 pg :type 'predicate)
  (5 5  zn :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-reg))

(define-instruction compact (segment zd pg zn size)
  (:printer sve-compact ())
  (:emitter
   (emit-sve-compact segment
                     (lane-size size)
                     (predicate-offset pg)
                     (reg-offset zn)
                     (reg-offset zd))))

(def-instruction-format sve-permute-scalar (zd ", " rn)
  (8 24 #b00000101)
  (2 22 size)
  (1 21 #b1)
  (2 19 op0)
  (3 16 op1)
  (6 10 #b001110)
  (5 5  rn :type 'x-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-permute-fp-scalar (zd ", " vn)
  (8 24 #b00000101)
  (2 22 size)
  (1 21 #b1)
  (2 19 op0)
  (3 16 op1)
  (6 10 #b001110)
  (5 5  vn :print-fields ((2 22)) :type 'float-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-permute-vector (zd ", " zn)
  (8 24 #b00000101)
  (2 22 size)
  (1 21 #b1)
  (2 19 op0)
  (3 16 op1)
  (6 10 #b001110)
  (5 5  zn :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-dup-imm (zd ", #" imm)
  (8  24 #b00100101)
  (2  22 size)
  (8  14 #b11100011)
  (1  13 sh)
  (8  5  imm8)
  (5  0  zd :print-fields ((2 22)) :type 'sve-reg)
  (imm :print-fields ((1 13) (8 5)) :type 'sve-dup-imm))

(def-instruction-format sve-dupm (zd ", #" imm)
  (8  24 #b00000101)
  (6  18 #b110000)
  (13 5  imm :type 'sve-imm13-const)
  (5  0  zd  :print-fields ((13 5)) :type 'sve-imm13-reg))

(define-instruction insr (segment zd src size)
  (:printer sve-permute-scalar    ((op0 #b00) (op1 #b100)))
  (:printer sve-permute-fp-scalar ((op0 #b10) (op1 #b100)))
  (:emitter
   (if (fp-register-p src)
       (emit-sve-permute-fp-scalar segment
                                   (lane-size size)
                                   #b10
                                   #b100
                                   (reg-offset src)
                                   (reg-offset zd))
       (emit-sve-permute-scalar segment
                                (lane-size size)
                                #b00
                                #b100
                                (gpr-offset src)
                                (reg-offset zd)))))

(def-sve-alias dup (segment zd src size)
  (:printer sve-permute-scalar ((op0 #b00) (op1 #b000)))
  (:printer sve-dup-imm        ())
  (:emitter
   (cond
     ((register-p src)
      (emit-sve-permute-scalar segment
                               (lane-size size)
                               #b00
                               #b000
                               (gpr-offset src)
                               (reg-offset zd)))

     ((and (integerp src) (typep src '(signed-byte 8)))
      (emit-sve-dup-imm segment
                        (lane-size size)
                        0
                        (ldb (byte 8 0) src)
                        (reg-offset zd)))
     ((and (integerp src)
           (not (eq size :b))
           (zerop (ldb (byte 8 0) src))
           (typep (ash src -8) '(signed-byte 8)))
      (emit-sve-dup-imm segment
                        (lane-size size)
                        1
                        (ldb (byte 8 0) (ash src -8))
                        (reg-offset zd)))
     (t
      (error "Invalid arguments for dup: ~s ~s ~s" zd size src)))))

(define-instruction dupm (segment zd imm size)
  (:printer sve-dupm ())
  (:emitter
   (emit-sve-dupm segment
                  (encode-sve-logical-immediate imm size)
                  (reg-offset zd))))

(def-instruction-format sve-ext (zdn ".B, " zdn ".B, " zm ".B, #" imm)
  (8 24 #b00000101)
  (1 23 #b0)
  (1 22 op0)
  (1 21 #b1)
  (5 16 imm8h)
  (3 13 #b000)
  (3 10 imm8l)
  (5 5  zm  :type 'sve-reg)
  (5 0  zdn :type 'sve-reg)
  (imm :print-fields ((5 16) (3 10)) :type 'imm8-ext))

(def-sve-alias ext (segment zdn src imm size)
  (:printer sve-ext ((op0 0)))
  (:printer sve-ext ((op0 1) (zm nil :type 'sve-reg-pair))
            '(:name :tab zdn ".B, " zm ", #" imm))
  (:emitter
   (aver (eq size :b))
   (let* ((constructive-p (listp src))
          (op0 (if constructive-p 1 0))
          (zn-offset (if constructive-p
                         (destructuring-bind (zn1 zn2) src
                           (assert (= (reg-offset zn2) (mod (1+ (reg-offset zn1)) 32))
                                   (src)
                                   "EXT pair must be consecutive registers: ~a" src)
                           (reg-offset zn1))
                         (reg-offset src)))
          (imm8h (ldb (byte 5 3) imm))
          (imm8l (ldb (byte 3 0) imm)))
     (emit-sve-ext segment
                   op0
                   imm8h
                   imm8l
                   zn-offset
                   (reg-offset zdn)))))

(def-instruction-format sve-bitwise-permute (zd ", " zn ", " zm)
  (8 24 #b01000101)
  (2 22 size)
  (1 21 #b0)
  (5 16 zm :print-fields ((2 22)) :type 'sve-reg)
  (4 12 #b1011)
  (2 10 opc)
  (5 5  zn :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-reg))

(make-defs ((($name $opc)
             (bext #b00)
             (bdep #b01)
             (bgrp #b10)))
  (define-instruction $name (segment zd zn zm size)
    (:printer sve-bitwise-permute ((opc $opc)))
    (:emitter
     (emit-sve-bitwise-permute segment
                               (lane-size size)
                               (reg-offset zm)
                               $opc
                               (reg-offset zn)
                               (reg-offset zd)))))

(def-instruction-format sve-shift-and-insert (zd ", " zn ", #" imm)
  (8  24 #b01000101)
  (2  22 tszh)
  (1  21 #b0)
  (2  19 tszl)
  (3  16 imm3)
  (5  11 #b11110)
  (1  10 op)
  (5  5  zn  :print-fields ((2 22) (2 19)) :type 'sve-shift-reg)
  (5  0  zd  :print-fields ((2 22) (2 19)) :type 'sve-shift-reg)
  (imm :print-fields ((2 22) (2 19) (3 16) (1 10)) :type 'sve-shift-insert-imm))

(make-defs ((($name $op $dir)
             (sri 0 :right)
             (sli 1 :left)))

  (def-sve-alias $name (segment zd zn shift size)
    (:printer sve-shift-and-insert ((op $op)))
    (:emitter
     (let ((enc (encode-shift-imm size shift $dir)))
       (emit-sve-shift-and-insert segment
                                  (ldb (byte 2 5) enc)
                                  (ldb (byte 2 3) enc)
                                  (ldb (byte 3 0) enc)
                                  $op
                                  (reg-offset zn)
                                  (reg-offset zd))))))

(def-instruction-format sve-inc-dec-predicate-count (rdn ", " pm)
  (8 24 #b00100101)
  (2 22 size)
  (4 18 #b1011)
  (1 17 #b0)
  (1 16 d)
  (4 12 #b1000)
  (1 11 scalar)
  (2 9  #b00)
  (4 5 pm  :print-fields ((2 22)) :type 'predicate)
  (5 0 rdn :print-fields ((2 22)) :type 'sve-reg))

(make-defs ((($name $d)
             (incp 0)
             (decp 1)))
  (define-instruction $name (segment rdn pm &optional (size :d))
    (:printer sve-inc-dec-predicate-count ((d $d) (scalar 1) (rdn nil :field (byte 5 0) :type 'x-reg)))
    (:printer sve-inc-dec-predicate-count ((d $d) (scalar 0)))
    (:emitter
     (emit-sve-inc-dec-predicate-count segment
                                       (lane-size-sans-b size)
                                       $d
                                       (if (register-p rdn) 1 0)
                                       (predicate-offset pm)
                                       (reg-offset rdn)))))

(def-instruction-format sve-bitwise-unary-predicated (zd ", " pg "/M, " zn)
  (8 24 #b00000100)
  (2 22 size)
  (1 21 #b0)
  (1 20 m)
  (1 19 #b1)
  (3 16 opc)
  (3 13 #b101)
  (3 10 pg   :type 'predicate)
  (5 5  zn   :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd   :print-fields ((2 22)) :type 'sve-reg))

(make-defs ((($name $opc)
             (cls  #b000)
             (clz  #b001)
             (cnt  #b010)
             (cnot #b011)
             (fabs #b100)
             (fneg #b101)
             (not  #b110)))
  (def-sve-alias $name (segment zd pg zeroing zn &optional (size :s))
    (:printer sve-bitwise-unary-predicated ((opc $opc) (m 0)) '(:name :tab zd ", " pg "/Z, " zn))
    (:printer sve-bitwise-unary-predicated ((opc $opc) (m 1)) '(:name :tab zd ", " pg "/M, " zn))
    (:emitter
     (emit-sve-bitwise-unary-predicated segment
                                        (lane-size size)
                                        (ecase zeroing
                                          (:/z 0)
                                          (:/m 1))
                                        $opc
                                        (predicate-offset pg)
                                        (reg-offset zn)
                                        (reg-offset zd)))))

(def-instruction-format sve-tbl (zd ", {" zn "}, " zm)
  (8 24 #b00000101)
  (2 22 size)
  (1 21 #b1)
  (5 16 zm  :print-fields ((2 22)) :type 'sve-reg)
  (6 10 opc)
  (5 5  zn  :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd  :print-fields ((2 22)) :type 'sve-reg))

(def-sve-alias tbl (segment zd zn zm size)
  (:printer sve-tbl ((opc #b001100)))
  (:printer sve-tbl ((opc #b001010) (zn nil :fields (list (byte 5 5) (byte 2 22)) :type 'sve-reg-pair))
            '(:name :tab zd ", " zn ", " zm))
  (:emitter
   (let* ((two-reg-p (listp zn))
          (opc       (if two-reg-p #b001010 #b001100))
          (zn-offset (if two-reg-p
                         (destructuring-bind (zn1 zn2) zn
                           (assert (= (reg-offset zn2) (mod (1+ (reg-offset zn1)) 32)) (zn)
                                   "SVE2 TBL table pair must be consecutive registers: ~a" zn)
                           (reg-offset zn1))
                         (reg-offset zn))))
     (emit-sve-tbl segment
                   (lane-size size)
                   (reg-offset zm)
                   opc
                   zn-offset
                   (reg-offset zd)))))

(def-sve-alias tbx (segment zd zn zm &optional (size :b))
  (:printer sve-tbl ((opc #b001011))
            '(:name :tab zd ", " zn ", " zm))
  (:emitter
   (let ((zn (if (listp zn) (first zn) zn)))
     (emit-sve-tbl segment
                   (lane-size size)
                   (reg-offset zm)
                   #b001011
                   (reg-offset zn)
                   (reg-offset zd)))))
;;; 1. Predicated Vector Multiply: MUL/SMULH/UMULH Zdn.T, Pg/M, Zdn.T, Zm.T
(def-instruction-format sve-mul-predicated (zdn ", " pg "/m, " zdn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (4 18 #b0100)
  (2 16 hu)
  (3 13 #b000)
  (3 10 pg   :type 'predicate)
  (5 5  zm   :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zdn  :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-mul-unpredicated (zd ", " zn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (1 21 #b1)
  (5 16 zm  :print-fields ((2 22)) :type 'sve-reg)
  (4 12 #b0110)
  (2 10 opc)
  (5 5  zn  :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd  :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-mul-imm (zdn ", " zdn ", #" imm)
  (8 24 #b00100101)
  (2 22 size)
  (3 19 #b110)
  (3 16 #b000)
  (2 14 #b11)
  (1 13 #b0)
  (8 5  imm :type 'immediate)
  (5 0  zdn :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-mul-indexed (zd ", " zn ", " zm)
  (8 24 #b01000100)
  (2 22 size)
  (1 21 #b1)
  (5 16 zm :print-fields ((2 22)) :type 'sve-indexed-reg)
  (6 10 #b111110)
  (5 5  zn :print-fields ((2 22)) :type 'sve-indexed-target-reg)
  (5 0  zd :print-fields ((2 22)) :type 'sve-indexed-target-reg))

(def-sve-alias mul (segment arg1 arg2 &optional arg3 size)
  (:printer sve-mul-predicated   ((hu #b00)))
  (:printer sve-mul-unpredicated ((opc #b00)))
  (:printer sve-mul-imm          ())
  (:printer sve-mul-indexed      ())
  (:emitter
   (cond
     ((predicate-p arg2)
      (emit-sve-mul-predicated segment
                               (lane-size size)
                               #b00
                               (predicate-offset arg2)
                               (reg-offset arg3)
                               (reg-offset arg1)))
     ((integerp arg2)
      (emit-sve-mul-imm segment
                        (lane-size size)
                        (ldb (byte 8 0) (the (signed-byte 8) arg2))
                        (reg-offset arg1)))

     ((consp arg3)
      (destructuring-bind (zm index) arg3
        (multiple-value-bind (size-enc opc) (encode-sve-mul-indexed size zm index)
          (emit-sve-mul-indexed segment
                                size-enc
                                opc
                                (reg-offset arg2)
                                (reg-offset arg1)))))
     (arg3
      (emit-sve-mul-unpredicated segment
                                 (lane-size size)
                                 (reg-offset arg3)
                                 #b00
                                 (reg-offset arg2)
                                 (reg-offset arg1)))

     (t
      (error "Invalid arguments for sve-mul: ~s ~s ~s ~s" arg1 arg2 arg3 size)))))

(make-defs ((($name $hu $unpred-opc)
             (smulh #b10 #b10)
             (umulh #b11 #b11)))
  (def-sve-alias $name (segment arg1 arg2 arg3 size)
    (:printer sve-mul-predicated   ((hu $hu)))
    (:printer sve-mul-unpredicated ((opc $unpred-opc)))

    (:emitter
     (if (predicate-p arg2)
         (emit-sve-mul-predicated segment
                                  (lane-size size)
                                  $hu
                                  (predicate-offset arg2)
                                  (reg-offset arg3)
                                  (reg-offset arg1))
         (emit-sve-mul-unpredicated segment
                                    (lane-size size)
                                    (reg-offset arg3)
                                    $unpred-opc
                                    (reg-offset arg2)
                                    (reg-offset arg1))))))

(def-sve-alias pmul (segment zd zn zm size)
  (:printer sve-mul-unpredicated ((opc #b01) (size 0)))
  (:emitter
   (aver (eq size :b))
   (emit-sve-mul-unpredicated segment
                              0
                              (reg-offset zm)
                              #b01
                              (reg-offset zn)
                              (reg-offset zd))))

(def-instruction-format sve-add-sub-predicated (zdn ", " pg "/m, " zdn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (3 19 #b000)
  (3 16 opc)
  (3 13 #b000)
  (3 10 pg   :type 'predicate)
  (5 5  zm   :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zdn  :print-fields ((2 22)) :type 'sve-reg))


(def-instruction-format sve-add-sub-unpredicated (zd ", " zn ", " zm)
  (8 24 #b00000100)
  (2 22 size)
  (1 21 #b1)
  (5 16 zm  :print-fields ((2 22)) :type 'sve-reg)
  (3 13 #b000)
  (3 10 opc)
  (5 5  zn  :print-fields ((2 22)) :type 'sve-reg)
  (5 0  zd  :print-fields ((2 22)) :type 'sve-reg))

(def-instruction-format sve-add-sub-imm (zdn ", " zdn ", #" imm)
  (8  24 #b00100101)
  (2  22 size)
  (3  19 #b100)
  (3  16 opc)
  (2  14 #b11)
  (1  13 sh)
  (8  5  imm8)
  (5  0  zdn :print-fields ((2 22)) :type 'sve-reg)
  (imm :print-fields ((1 13) (8 5)) :type 'sve-dup-imm))

(make-defs ((($name $pred $unpred $imm)
             (add   #b000     #b000       #b000)
             (sub   #b001     #b001       #b001)
             (subr  #b011     nil         #b011)
             (sqadd nil       #b100       #b100)
             (uqadd nil       #b101       #b101)
             (sqsub nil       #b110       #b110)
             (uqsub nil       #b111       #b111)))
  (def-sve-alias $name (segment arg1 arg2 &optional arg3 size)
    ($when $pred
      (:printer sve-add-sub-predicated ((opc $pred))))
    ($when $unpred
      (:printer sve-add-sub-unpredicated ((opc $unpred))))
    (:printer sve-add-sub-imm ((opc $imm)))
    (:emitter
     (cond
       ($when $pred
              ((predicate-p arg2)
               (emit-sve-add-sub-predicated segment
                                            (lane-size size)
                                            $pred
                                            (predicate-offset arg2)
                                            (reg-offset arg3)
                                            (reg-offset arg1))))

       ((integerp arg2)
        (let ((sz (if (and arg3 (keywordp arg3)) arg3 size)))
          (multiple-value-bind (sh imm8)
              (cond
                ((and (not (member sz '(:b)))
                      (not (zerop arg2))
                      (zerop (ldb (byte 8 0) arg2))
                      (typep (ash arg2 -8) '(unsigned-byte 8)))
                 (values 1 (ash arg2 -8)))
                ((typep arg2 '(unsigned-byte 8))
                 (values 0 arg2))
                ((typep arg2 '(signed-byte 8))
                 (values 0 (ldb (byte 8 0) arg2)))
                (t
                 (error "Immediate ~a out of range for ~a" arg2 '$name)))
            (emit-sve-add-sub-imm segment
                                  (lane-size sz)
                                  $imm
                                  sh
                                  imm8
                                  (reg-offset arg1)))))
       ($when $unpred
        ((and (register-p arg2) (register-p arg3))
         (emit-sve-add-sub-unpredicated segment
                                        (lane-size size)
                                        (reg-offset arg3)
                                        $unpred
                                        (reg-offset arg2)
                                        (reg-offset arg1))))

       (t
        (error "Invalid arguments for ~a: ~s ~s ~s ~s" '$name arg1 arg2 arg3 size))))))
