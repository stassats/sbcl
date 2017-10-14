;;;; predicate VOPs for the ARM VM

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!VM")


;;;; The Branch VOP.

;;; The unconditional branch, emitted when we can't drop through to the desired
;;; destination.  Dest is the continuation we transfer control to.
;;;
(define-vop (branch)
  (:info dest)
  (:generator 5
    (inst b dest)))


;;;; Generic conditional VOPs

;;; The generic conditional branch, emitted immediately after test
;;; VOPs that only set flags.
(define-vop (branch-if)
  (:info dest flags not-p)
  (:generator 0
    (flet ((negate-condition (name)
             (let ((code (logxor 1 (conditional-opcode name))))
               (aref +condition-name-vec+ code))))
      (aver (null (rest flags)))
      (inst b
            (if not-p
                (negate-condition (first flags))
                (first flags))
            dest))))


(defvar *cmov-ptype-representation-vop*
  (mapcan (lambda (entry)
            (destructuring-bind (ptypes &optional sc vop)
                entry
              (mapcar (if (and vop sc)
                          (lambda (ptype)
                            (list ptype sc vop))
                          #'list)
                      (ensure-list ptypes))))
          '((t descriptor-reg move-if/t)

            ((fixnum positive-fixnum)
             any-reg move-if/fx)
            ((unsigned-byte-64 unsigned-byte-63)
             unsigned-reg move-if/unsigned)
            (signed-byte-64 signed-reg move-if/signed)
            ;; FIXME: Can't use CMOV with byte registers, and characters live
            ;; in such outside of unicode builds. A better solution then just
            ;; disabling MOVE-IF/CHAR should be possible, though.
            #!+sb-unicode
            (character character-reg move-if/char)

            ((single-float complex-single-float
              double-float complex-double-float))

            (system-area-pointer sap-reg move-if/sap))))
(defun convert-conditional-move-p (node dst-tn x-tn y-tn)
  (declare (ignore node))
  (let* ((ptype (sb!c::tn-primitive-type dst-tn))
         (name  (sb!c::primitive-type-name ptype))
         (param (cdr (or (assoc name *cmov-ptype-representation-vop*)
                         '(t descriptor-reg move-if/t)))))
    (when param
      (destructuring-bind (representation vop) param
        (let ((scn (sc-number-or-lose representation)))
          (labels ((make-tn ()
                     (make-representation-tn ptype scn))
                   (frob-tn (tn)
                     (if (immediate-tn-p tn)
                         tn
                         (make-tn))))
            (values vop
                    (frob-tn x-tn) (frob-tn y-tn)
                    (make-tn)
                    nil)))))))

(define-vop (move-if)
  (:args (then) (else))
  (:results (res))
  (:info flags)
  (:generator 0
     (let ((not-p (eq (first flags) 'not)))
       (when not-p (pop flags))
       (flet ((negate-condition (name)
                (let ((code (logxor 1 (conditional-opcode name))))
                  (aref +condition-name-vec+ code)))
              (load-immediate (dst constant-tn
                               &optional (sc (sc-name (tn-sc dst))))
                ;; (inst mov dst (load-immediate-word (tn-value constant-tn)  )
                ;;       (encode-value-if-immediate constant-tn
                ;;                                  (memq sc '(any-reg descriptor-reg))))
                ))
         (aver (null (rest flags)))
         (inst csel res then else (car flags))))))


(macrolet ((def-move-if (name type reg)
             `(define-vop (,name move-if)
                (:args (then :scs (,reg) :to :eval)
                       (else :scs (,reg) :target res))
                (:arg-types ,type ,type)
                (:results (res :scs (,reg)
                               :from (:argument 1)))
                (:result-types ,type))))
  (def-move-if move-if/t t descriptor-reg)
  (def-move-if move-if/fx tagged-num any-reg)
  (def-move-if move-if/unsigned unsigned-num unsigned-reg)
  (def-move-if move-if/signed signed-num signed-reg)
  ;; FIXME: See *CMOV-PTYPE-REPRESENTATION-VOP* above.
  #!+sb-unicode
  (def-move-if move-if/char character character-reg)
  (def-move-if move-if/sap system-area-pointer sap-reg))


;;;; Conditional VOPs:

(define-vop (if-eq)
  (:args (x :scs (any-reg descriptor-reg null))
         (y :scs (any-reg descriptor-reg null)
            :load-if (sc-case y
                       ((any-reg descriptor-reg null))
                       (immediate
                        (not (fixnum-add-sub-immediate-p (tn-value y))))
                       (t t))))
  (:conditional :eq)
  ;(:info target not-p)
  (:policy :fast-safe)
  (:translate eq)
  (:generator 6
              (inst cmp
                    (sc-case x
                      (null null-tn) ;; FIXME: should it really be like that?
                      (t x))
                    (sc-case y
                      (null null-tn)
                      (immediate
                       (fixnumize (tn-value y)))
                      (t y)))))

(macrolet ((def (eq-name eql-name cost)
             `(define-vop (,eq-name ,eql-name)
                (:translate eq)
                (:variant-cost ,cost))))
  (def fast-if-eq-character fast-char=/character 3)
  (def fast-if-eq-character/c fast-char=/character/c 2)
  (def fast-if-eq-fixnum fast-eql/fixnum 3)
  (def fast-if-eq-fixnum/c fast-eql-c/fixnum 2)
  (def fast-if-eq-signed fast-if-eql/signed 5)
  (def fast-if-eq-signed/c fast-if-eql-c/signed 4)
  (def fast-if-eq-unsigned fast-if-eql/unsigned 5)
  (def fast-if-eq-unsigned/c fast-if-eql-c/unsigned 4))
