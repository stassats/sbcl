(in-package "SB-ARM64-ASM")

(defun decode-lane-size (size)
  (aref #(:b :h :s :d) size))

(defun print-predicate (value stream dstate)
  (declare (ignore dstate))
  (if (consp value)
      (destructuring-bind (offset size) value
        (format stream "P~d.~a" offset (decode-lane-size size)))
      (format stream "P~d" value)))

(defun decode-pattern (pattern)
  (getf '(#b11111 :all    #b00000 :pow2   #b00001 :vl1    #b00010 :vl2    #b00011 :vl3
          #b00100 :vl4    #b00101 :vl5    #b00110 :vl6    #b00111 :vl7    #b01000 :vl8
          #b01001 :vl16   #b01010 :vl32   #b01011 :vl64   #b01100 :vl128  #b01101 :vl256
          #b11101 :mul4   #b11110 :mul3)
        pattern))

(defun print-pattern (value stream dstate)
  (declare (ignore dstate))
  (unless (eq value #b11111)
    (format stream ", ~a" (decode-pattern value))))

(defun print-sve-reg (value stream dstate)
  (declare (ignore dstate))
  (if (consp value)
      (destructuring-bind (offset size) value
        (format stream "Z~d.~a" offset (decode-lane-size size)))
      (format stream "Z~d" value)))

(defun print-sve-reg-half (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (offset size) value
    (format stream "Z~d.~a" offset (decode-lane-size (1- size)))))

(defun print-sve-reg-d (offset stream dstate)
  (declare (ignore dstate))
  (format stream "Z~d.d" offset))

(defun print-imm9 (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (imm9h imm9l) value
    (format stream "~d" (sign-extend (dpb imm9h (byte 6 3) imm9l) 9))))

(defun decode-shift-imm-and-size (tszh tszl imm3 &optional left-p)
  (let* ((tsize (logior (ash tszh 2) tszl))
         (size-code (1- (integer-length tsize)))
         (esize (ash 8 size-code))
         (val (logior (ash tsize 3) imm3))
         (shift (if left-p
                    (- val esize)
                    (- (* 2 esize) val))))
    (values shift size-code)))

(defun print-sve-shift-imm (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (tszh tszl imm3 l) value
    (let ((left-p (= l 1)))
      (multiple-value-bind (shift) (decode-shift-imm-and-size tszh tszl imm3 left-p)
        (format stream "~d" shift)))))

(defun print-sve-shift-reg (value stream dstate)
  (declare (ignore dstate))
  (if (consp value)
      (destructuring-bind (offset tszh tszl) value
        (let ((size-code (1- (integer-length (logior (ash tszh 2) tszl)))))
          (format stream "Z~d.~a" offset (decode-lane-size size-code))))
      (format stream "Z~d" value)))

(defun print-sve-unpred-shift-imm (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (tszh tszl imm3 opc) value
    (let ((left-p (= opc #b11)))
      (multiple-value-bind (shift) (decode-shift-imm-and-size tszh tszl imm3 left-p)
        (format stream "~d" shift)))))

(defun sve-imm13-lane-size (imm13)
  (let ((n    (ldb (byte 1 12) imm13))
        (imms (ldb (byte 6 0)  imm13)))
    (if (= n 1)
        3
        (cond
          ((not (logbitp 5 imms)) 2)
          ((not (logbitp 4 imms)) 1)
          (t 0)))))

(defun decode-sve-logical-immediate (imm13)
  (let* ((n    (ldb (byte 1 12) imm13))
         (immr (ldb (byte 6 6)  imm13))
         (imms (ldb (byte 6 0)  imm13))
         (len  (cond
                 ((= n 1) 64)
                 ((not (logbitp 5 imms)) 32)
                 ((not (logbitp 4 imms)) 16)
                 ((not (logbitp 3 imms)) 8)
                 ((not (logbitp 2 imms)) 4)
                 ((not (logbitp 1 imms)) 2)
                 (t (error "Reserved imm13 value: #x~x" imm13))))
         (s (mod imms len))
         (r (mod immr len))
         (mask (1- (ash 1 (1+ s))))
         (rotated (logior (ash (ldb (byte (- len r) 0) mask) r)
                          (ash mask (- r len))))
         (elem-mask (ldb (byte len 0) rotated))
         (result 0))
    (loop for pos from 0 below 64 by len
          do (setf result (logior result (ash elem-mask pos))))
    result))


(defun print-sve-imm13-reg (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (offset imm13) value
    (format stream "Z~d.~a" offset (decode-lane-size (sve-imm13-lane-size imm13)))))

(defun print-sve-imm13-const (value stream dstate)
  (declare (ignore dstate))
  (format stream "#x~x" (decode-sve-logical-immediate value)))

(defun print-sve-dup-imm (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (sh imm8) value
    (let ((val (sign-extend imm8 8)))
      (format stream "#~d" (if (= sh 1)
                               (ash val 8)
                               val)))))

(defun print-imm8-ext (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (imm8h imm8l) value
    (format stream "~d" (dpb imm8h (byte 5 3) imm8l))))

(defun print-sve-reg-consecutive-pair (value stream dstate)
  (declare (ignore dstate))
  (format stream "{Z~d.B, Z~d.B}" value (mod (1+ value) 32)))

(defun print-sve-shift-insert-imm (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (tszh tszl imm3 op) value
    (let ((left-p (= op 1)))
      (multiple-value-bind (shift) (decode-shift-imm-and-size tszh tszl imm3 left-p)
        (format stream "~d" shift)))))

(defun decode-indexed-size (size)
  (case size
    ((0 1) "H")
    (2 "S")
    (3 "D")))

(defun print-sve-indexed-reg (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (opc size) value
    (multiple-value-bind (zm-offset index size-name)
        (case size
          ((0 1)
           (let ((idx (logior (ash (ldb (byte 1 0) size) 2)
                              (ldb (byte 2 3) opc)))
                 (zm  (ldb (byte 3 0) opc)))
             (values zm idx "H")))
          (2
           (let ((idx (ldb (byte 2 3) opc))
                 (zm  (ldb (byte 3 0) opc)))
             (values zm idx "S")))
          (3
           (let ((idx (ldb (byte 1 4) opc))
                 (zm  (ldb (byte 4 0) opc)))
             (values zm idx "D"))))
      (format stream "Z~d.~a[~d]" zm-offset size-name index))))

(defun print-sve-indexed-target-reg (value stream dstate)
  (declare (ignore dstate))
  (destructuring-bind (offset size) value
    (format stream "Z~d.~a" offset (decode-indexed-size size))))

