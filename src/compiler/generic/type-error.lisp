;;;; generic error-call operations

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.
(in-package "SB!VM")

;;; (ARRAY NIL) stuff looks the same on all platforms
;;;
;;; This is separate from DATA-VECTOR-REF, because it's declared as
;;; unsafely-flushable, and flushing access to nil arrays causes all
;;; sorts of problems.
(define-vop (data-nil-vector-ref)
  (:translate data-nil-vector-ref)
  (:policy :fast-safe)
  (:args (object :scs (descriptor-reg))
         (index :scs (any-reg descriptor-reg) :load-if nil))
  (:ignore index)
  (:arg-types simple-array-nil *)
  (:vop-var vop)
  (:save-p :compute-only)
  (:generator 1
    (error-call vop 'nil-array-accessed-error object)))

;;; It shouldn't be possible to fall through to here in normal user
;;; code, as the system is smart enough to deduce that there must be
;;; an error upstream, as there are no objects of type NIL that can be
;;; stored in this data vector; however, just in case, we provide this
;;; translation, so that
;;;   (LOCALLY
;;;     (DECLARE (TYPE (SIMPLE-ARRAY NIL (*)) X)
;;;              (OPTIMIZE (SPEED 3) (SAFETY 0)))
;;;     (SB-KERNEL:DATA-VECTOR-SET X 3 'FOO))
;;; signals the right kind of error.
(define-vop (data-vector-set/simple-array-nil)
  (:translate data-vector-set)
  (:policy :fast-safe)
  (:args (object :scs (descriptor-reg))
         (index :scs (unsigned-reg))
         (value :scs (descriptor-reg)))
  (:arg-types simple-array-nil positive-fixnum *)
  (:results (result :scs (descriptor-reg)))
  (:result-types *)
  (:ignore index value result)
  (:vop-var vop)
  (:save-p :compute-only)
  (:generator 1
    (error-call vop 'nil-array-accessed-error object)))

(define-vop (data-vector-set/simple-array-nil)
  (:translate data-vector-set)
  (:policy :fast-safe)
  (:args (object :scs (descriptor-reg))
         (index :scs (unsigned-reg))
         (value :scs (descriptor-reg)))
  (:info offset)
  (:arg-types simple-array-nil positive-fixnum *
              (:constant (integer 0 0)))
  (:results (result :scs (descriptor-reg)))
  (:result-types *)
  (:ignore index value result offset)
  (:vop-var vop)
  (:save-p :compute-only)
  (:generator 1
    (error-call vop 'nil-array-accessed-error object)))

(define-vop (type-check-error/c)
  (:policy :fast-safe)
  (:translate sb!c::%type-check-error/c)
  (:args (object :scs (descriptor-reg any-reg unsigned-reg signed-reg)
                 :load-if (not (sc-is object
                                      descriptor-reg any-reg
                                      unsigned-reg signed-reg constant))))
  (:arg-types * (:constant symbol) (:constant t))
  (:info errcode *location-context*)
  (:vop-var vop)
  (:save-p :compute-only)
  (:generator 900
    ;; FIXME: this should be in the *elsewhere* segment.
    ;; For lack of an architecture-independent way to emit
    ;; a jump, it's in the regular segment which pollutes the
    ;; instruction pipe with undecodable junk (the sc-numbers).
    (error-call vop errcode object)))

(macrolet ((def (name error translate context &rest args)
             `(define-vop (,name)
                ,@(when translate
                    `((:policy :fast-safe)
                      (:translate ,translate)))
                (:args ,@(mapcar (lambda (arg)
                                   `(,arg :scs (descriptor-reg any-reg
                                                unsigned-reg signed-reg)
                                          :load-if (not (sc-is ,arg descriptor-reg any-reg
                                                               unsigned-reg signed-reg constant))))
                                 args))
                ,@(and context
                       `((:info *location-context*)
                         (:arg-types * * (:constant t))))
                (:vop-var vop)
                (:save-p :compute-only)
                (:generator 1000
                  (error-call vop ',error ,@args)))))
  (def arg-count-error invalid-arg-count-error
    sb!c::%arg-count-error nil nargs)
  (def local-arg-count-error local-invalid-arg-count-error
    sb!c::%local-arg-count-error nil nargs fname)
  (def type-check-error object-not-type-error sb!c::%type-check-error t
    object ptype)
  (def layout-invalid-error layout-invalid-error sb!c::%layout-invalid-error nil
    object layout)
  (def odd-key-args-error odd-key-args-error
    sb!c::%odd-key-args-error nil)
  (def unknown-key-arg-error unknown-key-arg-error
    sb!c::%unknown-key-arg-error nil key)
  (def nil-fun-returned-error nil-fun-returned-error nil nil fun))

(defun encode-internal-error-args (values)
  (with-adjustable-vector (vector)
    (dolist (tn values)
      (write-var-integer
       (make-sc-offset (sc-number (tn-sc tn)) (or (tn-offset tn) 0))
       vector))
    (loop for octet across vector do (inst byte octet))))
