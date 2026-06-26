;;;; AVX512 intrinsics support for x86-64

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

;; fixme512 - replace with correct instructions, offests etc for avx512

(in-package "SB-VM")

;; (eval-when (:compile-toplevel :load-toplevel :execute)
;;   (unless (member :avx512 *features*)
;;     ;; (error "AVX-512 feature NOT detected by cold compiler!")
;;     ;; I don't know why cold compiler does not seem to see AVX512;
;;     ;; I see it defined in features, and elsewhere.
;;     ;; This is wrong, but I need it to test things; somewhere more
;;     ;; clever than me should remove this and fix it properly
;;     (push :avx512 *features*)
;;     (pushnew :sb-simd-pack-512 *features*)))

;; should this be redefined as ea-for-avx512-stack ???
(defun ea-for-avx512-stack (tn &optional (base rbp-tn))
  (ea (frame-byte-offset (+ (tn-offset tn) 7)) base))

(defun float-avx512-p (tn)
  (sc-is tn single-avx512-reg single-avx512-stack single-avx512-immediate
            double-avx512-reg double-avx512-stack double-avx512-immediate))

(defun int-avx512-p (tn)
  (sc-is tn int-avx512-reg int-avx512-stack int-avx512-immediate))

#+sb-xc-host
(progn ; the host compiler will complain about absence of these
  (defun %simd-pack-512-0 (x) (error "Called %SIMD-PACK-512-0 ~S" x))
  (defun %simd-pack-512-1 (x) (error "Called %SIMD-PACK-512-1 ~S" x))
  (defun %simd-pack-512-2 (x) (error "Called %SIMD-PACK-512-2 ~S" x))
  (defun %simd-pack-512-3 (x) (error "Called %SIMD-PACK-512-3 ~S" x))
  (defun %simd-pack-512-4 (x) (error "Called %SIMD-PACK-512-4 ~S" x))
  (defun %simd-pack-512-5 (x) (error "Called %SIMD-PACK-512-5 ~S" x))
  (defun %simd-pack-512-6 (x) (error "Called %SIMD-PACK-512-6 ~S" x))
  (defun %simd-pack-512-7 (x) (error "Called %SIMD-PACK-512-7 ~S" x)))

(define-move-fun (load-int-avx512-immediate 1) (vop x y)
                 ((int-avx512-immediate) (int-avx512-reg))
  (let* ((x  (tn-value x))
         (p0 (%simd-pack-512-0 x))
         (p1 (%simd-pack-512-1 x))
         (p2 (%simd-pack-512-2 x))
         (p3 (%simd-pack-512-3 x))
         (p4 (%simd-pack-512-4 x))
         (p5 (%simd-pack-512-5 x))
         (p6 (%simd-pack-512-6 x))
         (p7 (%simd-pack-512-7 x)))
    (cond ((= p0 p1 p2 p3 p4 p5 p6 p7 0)
           (inst vpxor y y y))
          ((= p0 p1 p2 p3 p4 p5 p6 p7 (ldb (byte 64 0) -1))
           ;; don't think this is recognized as dependency breaking...
           (inst vpcmpeqd y y y))
          (t
           (inst vmovdqu y (register-inline-constant x))))))

(define-move-fun (load-float-avx512-immediate 1) (vop x y)
  ((single-avx512-immediate double-avx512-immediate)
   (single-avx512-reg double-avx512-reg))
  (let* ((x  (tn-value x))
         (p0 (%simd-pack-512-0 x))
         (p1 (%simd-pack-512-1 x))
         (p2 (%simd-pack-512-2 x))
         (p3 (%simd-pack-512-3 x))
         (p4 (%simd-pack-512-4 x))
         (p5 (%simd-pack-512-5 x))
         (p6 (%simd-pack-512-6 x))
         (p7 (%simd-pack-512-7 x)))
    (cond ((= p0 p1 p2 p3 p4 p5 p6 p7 0)
           ;; in 512 it works on zmm regs; we good
           (inst vxorps y y y))
          ((= p0 p1 p2 p3 p4 p5 p6 p7 (ldb (byte 64 0) -1))
           (inst vpcmpeqd 0 y y)) ;; fixme512 ???
          (t
           (inst vmovdqu64 y (register-inline-constant x))))))

(define-move-fun (load-int-avx512 2) (vop x y)
  ((int-avx512-stack) (int-avx512-reg))
  (inst vmovdqu64 y (ea-for-avx512-stack x)))

(define-move-fun (load-float-avx512 2) (vop x y)
  ((single-avx512-stack double-avx512-stack) (single-avx512-reg double-avx512-reg))
  (inst vmovups y (ea-for-avx512-stack x)))

(define-move-fun (store-int-avx512 2) (vop x y)
  ((int-avx512-reg) (int-avx512-stack))
  (inst vmovdqu64 (ea-for-avx512-stack y) x))

(define-move-fun (store-float-avx512 2) (vop x y)
  ((double-avx512-reg single-avx512-reg) (double-avx512-stack single-avx512-stack))
  (inst vmovups (ea-for-avx512-stack y) x))

(define-vop (avx512-move)
  (:args (x :scs (single-avx512-reg double-avx512-reg int-avx512-reg)
            :target y
            :load-if (not (location= x y))))
  (:results (y :scs (single-avx512-reg double-avx512-reg int-avx512-reg)
               :load-if (not (location= x y))))
  (:note "AVX512 move")
  (:generator 0
              (move y x)))

(define-move-vop avx512-move :move
  (int-avx512-reg single-avx512-reg double-avx512-reg)
  (int-avx512-reg single-avx512-reg double-avx512-reg))

(macrolet ((define-move-from-avx512 (type tag &rest scs)
             (let ((name (symbolicate "MOVE-FROM-AVX512/" type)))
               `(progn
                  (define-allocator (,name)
                    (:args (x :scs ,scs))
                    (:results (y :scs (descriptor-reg)))
                    (:arg-types ,type)
                    (:note "AVX512 to pointer coercion")
                    ;; fixme512 below is definitely wrong for avx512
                    (:generator 13
                      (alloc-other simd-pack-512-widetag simd-pack-512-size y)
                      (storew (fixnumize ,tag)
                              y simd-pack-512-tag-slot other-pointer-lowtag)
                      (let ((ea (object-slot-ea
                                 y simd-pack-512-p0-slot other-pointer-lowtag)))
                        (if (float-avx512-p x)
                            (inst vmovups ea x)
                            (inst vmovdqu ea x)))))
                  (define-move-vop ,name :move
                    ,scs (descriptor-reg))))))
  ;; see +simd-pack-element-types+
  (define-move-from-avx512 simd-pack-512-single 0 single-avx512-reg)
  (define-move-from-avx512 simd-pack-512-double 1 double-avx512-reg)
  (define-move-from-avx512 simd-pack-512-ub8    2 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-ub16   3 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-ub32   4 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-ub64   5 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-sb8    6 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-sb16   7 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-sb32   8 int-avx512-reg)
  (define-move-from-avx512 simd-pack-512-sb64   9 int-avx512-reg))

(define-vop (move-to-avx512)
  (:args (x :scs (descriptor-reg)))
  (:results (y :scs (int-avx512-reg double-avx512-reg single-avx512-reg)))
  (:note "pointer to AVX512 coercion")
  (:generator 2
    (let ((ea (object-slot-ea x simd-pack-512-p0-slot other-pointer-lowtag)))
      (if (float-avx512-p y)
          (inst vmovups y ea)
          (inst vmovdqu64 y ea)))))

(define-move-vop move-to-avx512 :move
  (descriptor-reg)
  (int-avx512-reg double-avx512-reg single-avx512-reg))

(define-vop (move-avx512-arg)
  (:args (x :scs (int-avx512-reg double-avx512-reg single-avx512-reg) :target y)
         (fp :scs (any-reg)
             :load-if (not (sc-is y int-avx512-reg double-avx512-reg single-avx512-reg))))
  (:results (y))
  (:note "AVX512 argument move")
  (:generator 4
     (sc-case y
       ((int-avx512-reg double-avx512-reg single-avx512-reg)
        (unless (location= x y)
          (if (or (float-avx512-p x)
                  (float-avx512-p y))
              (inst vmovups y x)
              (inst vmovdqu64 y x))))
       ((int-avx512-stack double-avx512-stack single-avx512-stack)
        (if (float-avx512-p x)
            (inst vmovups (ea-for-avx512-stack y fp) x)
            (inst vmovdqu64 (ea-for-avx512-stack y fp) x))))))

(define-move-vop move-avx512-arg :move-arg
  (int-avx512-reg double-avx512-reg single-avx512-reg descriptor-reg)
  (int-avx512-reg double-avx512-reg single-avx512-reg))

(define-move-vop move-arg :move-arg
  (int-avx512-reg double-avx512-reg single-avx512-reg)
  (descriptor-reg))


(define-vop (%simd-pack-512-0)
  (:translate %simd-pack-512-0)
  (:args (x :scs (descriptor-reg)))
  (:arg-types simd-pack-512)
  (:results (dst :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:policy :fast-safe)
  (:generator 3
    (loadw dst x simd-pack-512-p0-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-1 %simd-pack-512-0)
  (:translate %simd-pack-512-1)
  (:generator 3
    (loadw dst x simd-pack-512-p1-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-2 %simd-pack-512-0)
  (:translate %simd-pack-512-2)
  (:generator 3
    (loadw dst x simd-pack-512-p2-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-3 %simd-pack-512-0)
  (:translate %simd-pack-512-3)
  (:generator 3
    (loadw dst x simd-pack-512-p3-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-4 %simd-pack-512-0)
  (:translate %simd-pack-512-4)
  (:generator 3
    (loadw dst x simd-pack-512-p4-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-5 %simd-pack-512-0)
  (:translate %simd-pack-512-5)
  (:generator 3
    (loadw dst x simd-pack-512-p5-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-6 %simd-pack-512-0)
  (:translate %simd-pack-512-6)
  (:generator 3
    (loadw dst x simd-pack-512-p6-slot other-pointer-lowtag)))

(define-vop (%simd-pack-512-7 %simd-pack-512-0)
  (:translate %simd-pack-512-7)
  (:generator 3
    (loadw dst x simd-pack-512-p7-slot other-pointer-lowtag)))

(define-allocator (%make-simd-pack-512)
  (:translate %make-simd-pack-512)
  (:policy :fast-safe)
  (:args (tag :scs (any-reg))
         (p0 :scs (unsigned-reg))
         (p1 :scs (unsigned-reg))
         (p2 :scs (unsigned-reg))
         (p3 :scs (unsigned-reg))
         (p4 :scs (unsigned-reg))
         (p5 :scs (unsigned-reg))
         (p6 :scs (unsigned-reg))
         (p7 :scs (unsigned-reg)))
  (:arg-types tagged-num
              unsigned-num unsigned-num unsigned-num unsigned-num
              unsigned-num unsigned-num unsigned-num unsigned-num)
  (:results (dst :scs (descriptor-reg) :from :load))
  (:result-types t)
  (:generator 13
    (alloc-other simd-pack-512-widetag simd-pack-512-size dst)
    ;; see +simd-pack-element-types+
    (storew tag dst simd-pack-512-tag-slot other-pointer-lowtag)
    (storew p0 dst simd-pack-512-p0-slot other-pointer-lowtag)
    (storew p1 dst simd-pack-512-p1-slot other-pointer-lowtag)
    (storew p2 dst simd-pack-512-p2-slot other-pointer-lowtag)
    (storew p3 dst simd-pack-512-p3-slot other-pointer-lowtag)
    (storew p4 dst simd-pack-512-p4-slot other-pointer-lowtag)
    (storew p5 dst simd-pack-512-p5-slot other-pointer-lowtag)
    (storew p6 dst simd-pack-512-p6-slot other-pointer-lowtag)
    (storew p7 dst simd-pack-512-p7-slot other-pointer-lowtag)))

(define-vop (%make-simd-pack-512-ub64)
    (:translate %make-simd-pack-512-ub64)
  (:policy :fast-safe)
  (:args (p0 :scs (unsigned-reg))
         (p1 :scs (unsigned-reg))
         (p2 :scs (unsigned-reg))
         (p3 :scs (unsigned-reg))
         (p4 :scs (unsigned-reg))
         (p5 :scs (unsigned-reg))
         (p6 :scs (unsigned-reg))
         (p7 :scs (unsigned-reg)))
  (:arg-types unsigned-num unsigned-num unsigned-num unsigned-num
              unsigned-num unsigned-num unsigned-num unsigned-num)
  (:results (dst :scs (int-avx512-reg)))
  (:result-types simd-pack-512-ub64)
  ;; Explicitly request a temporary XMM register to build 128-bit chunks safely
  (:temporary (:sc double-reg) tmp)
  ;; this one builds in chunks in a temporary register, and swaps in bytes
  ;; in the correct place in result; I think there is more efficient way to do
  ;; this but I don't know it for now. I am happy if someone reworks it
  (:generator 20
     ;; a "xmm view" of dst register
     (let ((xmm (sb-c:make-random-tn
                     (sb-c:sc-or-lose 'sb-vm::double-reg) (sb-c:tn-offset dst))))

       (inst vpxor dst dst dst)
       (inst vpxor tmp tmp tmp)

       (inst vpinsrq xmm xmm p0 0)
       (inst vpinsrq xmm xmm p1 1)

       (inst vpinsrq tmp tmp p2 0)
       (inst vpinsrq tmp tmp p3 1)
       (inst vinserti64x2 dst dst tmp 1)

       (inst vpinsrq tmp tmp p4 0)
       (inst vpinsrq tmp tmp p5 1)
       (inst vinserti64x2 dst dst tmp 2)

       (inst vpinsrq tmp tmp p6 0)
       (inst vpinsrq tmp tmp p7 1)
       (inst vinserti64x2 dst dst tmp 3))))


(defmacro simd-pack-512-dispatch (pack &body body)
  (check-type pack symbol)
  `(let ((,pack ,pack))
     (etypecase ,pack
       ,@(map 'list (lambda (eltype)
                   `((simd-pack-512 ,eltype) ,@body))
          +simd-pack-element-types+))))

#-sb-xc-host
(macrolet ((unpack-unsigned (pack bits)
             `(simd-pack-512-dispatch ,pack
                (let ((a (%simd-pack-512-0 ,pack))
                      (b (%simd-pack-512-1 ,pack))
                      (c (%simd-pack-512-2 ,pack))
                      (d (%simd-pack-512-3 ,pack))
                      (e (%simd-pack-512-4 ,pack))
                      (f (%simd-pack-512-5 ,pack))
                      (g (%simd-pack-512-6 ,pack))
                      (h (%simd-pack-512-7 ,pack)))
                  (values
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos a))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos b))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos c))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos d))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos e))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos f))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos g))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-unsigned-1 ,bits ,pos h))))))
           (unpack-unsigned-1 (bits position ub64)
             `(ldb (byte ,bits ,position) ,ub64)))
  (declaim (inline %simd-pack-512-ub8s))
  (defun %simd-pack-512-ub8s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-unsigned pack 8))

  (declaim (inline %simd-pack-512-ub16s))
  (defun %simd-pack-512-ub16s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-unsigned pack 16))

  (declaim (inline %simd-pack-512-ub32s))
  (defun %simd-pack-512-ub32s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-unsigned pack 32))

  (declaim (inline %simd-pack-512-ub64s))
  (defun %simd-pack-512-ub64s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-unsigned pack 64)))

#-sb-xc-host
(macrolet ((unpack-signed (pack bits)
             `(simd-pack-512-dispatch ,pack
                (let ((a (%simd-pack-512-0 ,pack))
                      (b (%simd-pack-512-1 ,pack))
                      (c (%simd-pack-512-2 ,pack))
                      (d (%simd-pack-512-3 ,pack))
                      (e (%simd-pack-512-4 ,pack))
                      (f (%simd-pack-512-5 ,pack))
                      (g (%simd-pack-512-6 ,pack))
                      (h (%simd-pack-512-7 ,pack)))
                  (values
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos a))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos b))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos c))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos d))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos e))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos f))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos g))
                   ,@(loop for pos by bits below 64 collect
                           `(unpack-signed-1 ,bits ,pos h))))))
           (unpack-signed-1 (bits position ub64)
             `(- (mod (+ (ldb (byte ,bits ,position) ,ub64)
                         ,(expt 2 (1- bits)))
                      ,(expt 2 bits))
                 ,(expt 2 (1- bits)))))
  (declaim (inline %simd-pack-512-sb8s))
  (defun %simd-pack-512-sb8s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-signed pack 8))

  (declaim (inline %simd-pack-512-sb16s))
  (defun %simd-pack-512-sb16s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-signed pack 16))

  (declaim (inline %simd-pack-512-sb32s))
  (defun %simd-pack-512-sb32s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-signed pack 32))

  (declaim (inline %simd-pack-512-sb64s))
  (defun %simd-pack-512-sb64s (pack)
    (declare (type simd-pack-512 pack))
    (unpack-signed pack 64)))

#-sb-xc-host
(progn
  ;; (defun %make-simd-pack-512-ub64 (p0 p1 p2 p3 p4 p5 p6 p7)
  ;;   (declare (type (unsigned-byte 64) p0 p1 p2 p3 p4 p5 p6 p7))
  ;;   (%make-simd-pack-512 0 p0 p1 p2 p3 p4 p5 p6 p7))

  (defun %make-simd-pack-512-ub32 (p0 p1 p2 p3 p4 p5 p6 p7 p8
                                   p9 p10 p11 p12 p13 p14 p15)
    (declare (type (unsigned-byte 32) p0 p1 p2 p3 p4 p5 p6 p7 p8
                                      p9 p10 p11 p12 p13 p14 p15))
    (%make-simd-pack-512
     #.(position '(unsigned-byte 32) +simd-pack-element-types+ :test #'equal)
     (logior p0 (ash p1 32))
     (logior p2 (ash p3 32))
     (logior p4 (ash p5 32))
     (logior p6 (ash p7 32))
     (logior p8 (ash p9 32))
     (logior p10 (ash p11 32))
     (logior p12 (ash p13 32))
     (logior p14 (ash p15 32)))))

(define-vop (%make-simd-pack-512-double)
  (:translate %make-simd-pack-512-double)
  (:policy :fast-safe)
  (:args (p0 :scs (double-reg) :target dst)
         (p1 :scs (double-reg))
         (p2 :scs (double-reg))
         (p3 :scs (double-reg))
         (p4 :scs (double-reg))
         (p5 :scs (double-reg))
         (p6 :scs (double-reg))
         (p7 :scs (double-reg)))
  (:arg-types double-float double-float double-float double-float
              double-float double-float double-float double-float)
  (:temporary (:sc int-avx512-reg) tmp)
  (:results (dst :scs (double-avx512-reg) :from (:argument 0)))
  (:result-types simd-pack-512-double)
  (:generator 5
   ;; fixme512 ???
   ;; (format *error-output* "emit double i: ~a ~a ~%" dst tmp)
   (inst vunpcklpd dst p0 p1)
   (inst vunpcklpd tmp p2 p3)
   (inst vinsertf64x2 dst dst tmp #x1)
   (inst vunpcklpd tmp p4 p5)
   (inst vinsertf64x2 dst dst tmp #x2)
   (inst vunpcklpd tmp p6 p7)
   (inst vinsertf64x2 dst dst tmp #x3)))

(define-vop (%make-simd-pack-512-single)
  (:translate %make-simd-pack-512-single)
  (:policy :fast-safe)
  (:args (p0 :scs (single-reg) :target dst)
         (p1 :scs (single-reg))
         (p2 :scs (single-reg))
         (p3 :scs (single-reg))
         (p4 :scs (single-reg))
         (p5 :scs (single-reg))
         (p6 :scs (single-reg))
         (p7 :scs (single-reg))
         (p8 :scs (single-reg))
         (p9 :scs (single-reg))
         (p10 :scs (single-reg))
         (p11 :scs (single-reg))
         (p12 :scs (single-reg))
         (p13 :scs (single-reg))
         (p14 :scs (single-reg))
         (p15 :scs (single-reg)))
  (:arg-types single-float single-float single-float single-float
              single-float single-float single-float single-float
              single-float single-float single-float single-float
              single-float single-float single-float single-float)
  ;;(:temporary (:sc single-avx512-reg  :from (:argument 3)) tmp)
  (:results (dst :scs (single-avx512-reg) :from (:argument 0)))
  (:result-types simd-pack-512-single)
  (:generator 10
  ;; allocate 16 floats on the stack.
  (inst sub rsp-tn 64)

  ;; move all 16 scalar floats to sequential memory addresses.
  (inst movss (ea 0 rsp-tn) p0)
  (inst movss (ea 4 rsp-tn) p1)
  (inst movss (ea 8 rsp-tn) p2)
  (inst movss (ea 12 rsp-tn) p3)
  (inst movss (ea 16 rsp-tn) p4)
  (inst movss (ea 20 rsp-tn) p5)
  (inst movss (ea 24 rsp-tn) p6)
  (inst movss (ea 28 rsp-tn) p7)
  (inst movss (ea 32 rsp-tn) p8)
  (inst movss (ea 36 rsp-tn) p9)
  (inst movss (ea 40 rsp-tn) p10)
  (inst movss (ea 44 rsp-tn) p11)
  (inst movss (ea 48 rsp-tn) p12)
  (inst movss (ea 52 rsp-tn) p13)
  (inst movss (ea 56 rsp-tn) p14)
  (inst movss (ea 60 rsp-tn) p15)

  ;; load the entire 512-bit chunk into the destination register.
  (inst vmovups dst (ea 0 rsp-tn))

  ;; restore the stack pointer.
  (inst add rsp-tn 64)))

(defknown %simd-pack-512-single-item
  (simd-pack-512 (integer 0 15)) single-float (flushable))

(define-vop (%simd-pack-512-single-item)
  (:translate %simd-pack-512-single-item)
  (:args (x :scs (int-avx512-reg double-avx512-reg single-avx512-reg)
            :target dst))
  (:info index)
  (:arg-types simd-pack-512 (:constant t))
  (:results (dst :scs (single-reg)))
  (:result-types single-float)
  (:temporary (:sc single-reg :from (:argument 0)) tmp)
  (:policy :fast-safe)
  (:generator 3
    (multiple-value-bind (lane idx) (floor index 4)
      ;; extract the correct 128-bit lane (0-3) into temporary XMM register
      (inst vextractf32x4 tmp x lane)
      (cond ((zerop idx)
             (inst vmovss dst tmp))
            (t
             (inst vshufps dst tmp tmp idx))))))

(defknown %simd-pack-512-double-item
  (simd-pack-512 (integer 0 7)) double-float (flushable))

(define-vop (%simd-pack-512-double-item)
  (:translate %simd-pack-512-double-item)
  (:args (x :scs (int-avx512-reg double-avx512-reg single-avx512-reg)
            :target dst))
  (:info index)
  (:arg-types simd-pack-512 (:constant t))
  (:results (dst :scs (double-reg)))
  (:result-types double-float)
  (:temporary (:sc double-reg :from (:argument 0)) tmp)
  (:policy :fast-safe)
  (:generator 3
    (multiple-value-bind (lane idx) (floor index 2)
      ;; Extract the correct 128-bit lane (0, 1, 2, or 3) into the XMM temporary
      (inst vextractf64x2 tmp x lane)
      (cond ((zerop idx)
             ;; Element 0 of the lane: move lower 64-bits directly to dst
             (inst vmovsd dst tmp))
            (t
             ;; Element 1 of the lane: shift lane right by 8 bytes (64 bits)
             (inst vpsrldq dst tmp 8))))))

#-sb-xc-host
(progn
(declaim (inline %simd-pack-512-singles))
(defun %simd-pack-512-singles (pack)
  (declare (type simd-pack-512 pack))
  (simd-pack-512-dispatch pack
    (values (%simd-pack-512-single-item pack 0)
            (%simd-pack-512-single-item pack 1)
            (%simd-pack-512-single-item pack 2)
            (%simd-pack-512-single-item pack 3)
            (%simd-pack-512-single-item pack 4)
            (%simd-pack-512-single-item pack 5)
            (%simd-pack-512-single-item pack 6)
            (%simd-pack-512-single-item pack 7)
            (%simd-pack-512-single-item pack 8)
            (%simd-pack-512-single-item pack 9)
            (%simd-pack-512-single-item pack 10)
            (%simd-pack-512-single-item pack 11)
            (%simd-pack-512-single-item pack 12)
            (%simd-pack-512-single-item pack 13)
            (%simd-pack-512-single-item pack 14)
            (%simd-pack-512-single-item pack 15)))))

#-sb-xc-host
(progn
(declaim (inline %simd-pack-512-doubles))
(defun %simd-pack-512-doubles (pack)
  (declare (type simd-pack-512 pack))
  (simd-pack-512-dispatch pack
    (values (%simd-pack-512-double-item pack 0)
            (%simd-pack-512-double-item pack 1)
            (%simd-pack-512-double-item pack 2)
            (%simd-pack-512-double-item pack 3)
            (%simd-pack-512-double-item pack 4)
            (%simd-pack-512-double-item pack 5)
            (%simd-pack-512-double-item pack 6)
            (%simd-pack-512-double-item pack 7))))

(defun %simd-pack-512-inline-constant (pack)
  (list :avx512 (logior (%simd-pack-512-0 pack)
                        (ash (%simd-pack-512-1 pack) 64)
                        (ash (%simd-pack-512-2 pack) 128)
                        (ash (%simd-pack-512-3 pack) 192)
                        (ash (%simd-pack-512-4 pack) 256)
                        (ash (%simd-pack-512-5 pack) 320)
                        (ash (%simd-pack-512-6 pack) 384)
                        (ash (%simd-pack-512-7 pack) 448)))))
