;;;; This file contains the implementation-independent facilities used
;;;; for defining the compiler's interface to the VM in a given
;;;; implementation that are needed at meta-compile time. They are
;;;; separated out from vmdef.lisp so that they can be compiled and
;;;; loaded without trashing the running compiler.
;;;;
;;;; FIXME: The "trashing the running [CMU CL] compiler" motivation no
;;;; longer makes sense in SBCL, since we can cross-compile cleanly.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

;;;; storage class and storage base definition

;;; Define a storage base having the specified NAME. KIND may be :FINITE,
;;; :UNBOUNDED or :NON-PACKED. The following keywords are legal:
;;;    :SIZE specifies the number of locations in a :FINITE SB or
;;;          the initial size of an :UNBOUNDED SB.
;;;
;;; We enter the basic structure at meta-compile time, and then fill
;;; in the missing slots at load time.
(defmacro define-storage-base (name kind &key size)
  (declare (type symbol name)
           (type (member :finite :unbounded :non-packed) kind))

  ;; SIZE is either mandatory or forbidden.
  (ecase kind
    (:non-packed
     (when size
       (error "A size specification is meaningless in a ~S SB." kind)))
    ((:finite :unbounded)
     (unless size (error "Size is not specified in a ~S SB." kind))
     (aver (typep size 'unsigned-byte))))
  `(eval-when (#-sb-xc :compile-toplevel :load-toplevel :execute)
     (let ((res ,(if (eq kind :non-packed)
                     `(make-sb :name ',name :kind ,kind)
                     `(make-finite-sb :name ',name :kind ,kind :size ,size))))
       ,(unless (eq kind :non-packed)
          `(progn
             (/show0 "not :NON-PACKED, i.e. hairy case")
             (setf (finite-sb-always-live res)
                   (make-array ',size
                               :initial-element
                               #-(or sb-xc sb-xc-host) #*
                               ;; The cross-compiler isn't very good
                               ;; at dumping specialized arrays; we
                               ;; work around that by postponing
                               ;; generation of the specialized
                               ;; array 'til runtime.
                               #+(or sb-xc sb-xc-host)
                               (make-array 0 :element-type 'bit)))
             (/show0 "doing second SEF")
             (setf (finite-sb-conflicts res)
                   (make-array ',size :initial-element '#()))
             (/show0 "doing third SETF")
             (setf (finite-sb-live-tns res)
                   (make-array ',size :initial-element nil))
             (/show0 "doing fourth SETF")
             (setf (finite-sb-always-live-count res)
                   (make-array ',size :initial-element 0))))
       (setf (gethash ',name *backend-sb-names*) res)
       (/show0 "about to put SB onto/into SB-LIST")
       (setf *backend-sb-list*
             (cons res
                   (remove ',name *backend-sb-list* :key #'sb-name))))))

;;; Define a storage class NAME that uses the named Storage-Base.
;;; NUMBER is a small, non-negative integer that is used as an alias.
;;; The following keywords are defined:
;;;
;;; :ELEMENT-SIZE Size
;;;   The size of objects in this SC in whatever units the SB uses.
;;;   This defaults to 1.
;;;
;;; :ALIGNMENT Size
;;;   The alignment restrictions for this SC. TNs will only be
;;;   allocated at offsets that are an even multiple of this number.
;;;   This defaults to 1.
;;;
;;; :LOCATIONS (Location*)
;;;   If the SB is :FINITE, then this is a list of the offsets within
;;;   the SB that are in this SC.
;;;
;;; :RESERVE-LOCATIONS (Location*)
;;;   A subset of the Locations that the register allocator should try to
;;;   reserve for operand loading (instead of to hold variable values.)
;;;
;;; :SAVE-P {T | NIL}
;;;   If T, then values stored in this SC must be saved in one of the
;;;   non-save-p :ALTERNATE-SCs across calls.
;;;
;;; :ALTERNATE-SCS (SC*)
;;;   Indicates other SCs that can be used to hold values from this SC across
;;;   calls or when storage in this SC is exhausted. The SCs should be
;;;   specified in order of decreasing \"goodness\". There must be at least
;;;   one SC in an unbounded SB, unless this SC is only used for restricted or
;;;   wired TNs.
;;;
;;; :CONSTANT-SCS (SC*)
;;;   A list of the names of all the constant SCs that can be loaded into this
;;;   SC by a move function.
(defmacro define-storage-class (name number sb-name
                             &key (element-size '1)
                                  (alignment '1) locations reserve-locations
                                  save-p alternate-scs constant-scs)
  (declare (type symbol name))
  (declare (type sc-number number))
  (declare (type symbol sb-name))
  (declare (type list locations reserve-locations alternate-scs constant-scs))
  (declare (type boolean save-p))
  (unless (= (logcount alignment) 1)
    (error "alignment not a power of two: ~W" alignment))

  (let ((sb (sb-or-lose sb-name)))
    (if (eq (sb-kind sb) :finite)
        (let ((size (sb-size sb))
              (element-size (eval element-size)))
          (declare (type unsigned-byte element-size))
          (dolist (el locations)
            (declare (type unsigned-byte el))
            (unless (<= 1 (+ el element-size) size)
              (error "SC element ~W out of bounds for ~S" el sb))))
        (when locations
          (error ":LOCATIONS is meaningless in a ~S SB." (sb-kind sb))))

    (unless (subsetp reserve-locations locations)
      (error "RESERVE-LOCATIONS not a subset of LOCATIONS."))

    (when (and (or alternate-scs constant-scs)
               (eq (sb-kind sb) :non-packed))
      (error
       "It's meaningless to specify alternate or constant SCs in a ~S SB."
       (sb-kind sb))))

  (let ((nstack-p
          (if (or (eq sb-name 'non-descriptor-stack)
                  (find 'non-descriptor-stack
                        (mapcar #'sc-or-lose alternate-scs)
                        :key (lambda (x)
                               (sb-name (sc-sb x)))))
              t nil)))
    `(let ((res (make-sc :name ',name :number ',number
                         :sb (sb-or-lose ',sb-name)
                         :element-size ,element-size
                         :alignment ,alignment
                         :locations ',locations
                         :reserve-locations ',reserve-locations
                         :save-p ',save-p
                         :number-stack-p ,nstack-p
                         :alternate-scs (mapcar #'sc-or-lose
                                                ',alternate-scs)
                         :constant-scs (mapcar #'sc-or-lose
                                               ',constant-scs)))
           (old (svref *backend-sc-numbers* ',number)))
       (when (and old (not (eq (sc-name old) ',name)))
         (warn "redefining SC number ~W from ~S to ~S" ',number
               (sc-name old) ',name))
       (setf (gethash ',name *backend-sc-names*) res)
       (setf (svref *backend-sc-numbers* ',number) res)
       (setf (svref (sc-load-costs res) ',number) 0))))

;;; handy macro so we don't have to keep changing all the numbers
;;; whenever we insert a new storage class
(defmacro define-storage-classes (&rest classes)
  `(eval-when (#-sb-xc :compile-toplevel :load-toplevel :execute)
     ,@(do ((forms nil
                   (let* ((class (car classes))
                          (sc-name (car class))
                          (constant-name (intern (concatenate 'simple-string
                                                              (string sc-name)
                                                              "-SC-NUMBER"))))
                     (list* `(define-storage-class ,sc-name ,index ,@(cdr class))
                            `(def!constant ,constant-name ,index)
                            forms)))
            (index 0 (1+ index))
            (classes classes (cdr classes)))
           ((null classes)
            (nreverse forms)))))


;;;; move/coerce definition

;;; Given a list of pairs of lists of SCs (as given to DEFINE-MOVE-VOP,
;;; etc.), bind TO-SC and FROM-SC to all the combinations.
(defmacro do-sc-pairs ((from-sc-var to-sc-var scs) &body body)
  `(do ((froms ,scs (cddr froms))
        (tos (cdr ,scs) (cddr tos)))
       ((null froms))
     (dolist (from (car froms))
       (let ((,from-sc-var (sc-or-lose from)))
         (dolist (to (car tos))
           (let ((,to-sc-var (sc-or-lose to)))
             ,@body))))))

;;; Define the function NAME and note it as the function used for
;;; moving operands from the From-SCs to the To-SCs. Cost is the cost
;;; of this move operation. The function is called with three
;;; arguments: the VOP (for context), and the source and destination
;;; TNs. An ASSEMBLE form is wrapped around the body. All uses of
;;; DEFINE-MOVE-FUN should be compiled before any uses of
;;; DEFINE-VOP.
(defmacro define-move-fun ((name cost) lambda-list scs &body body)
  (declare (type index cost))
  (when (or (oddp (length scs)) (null scs))
    (error "malformed SCs spec: ~S" scs))
  `(progn
     (eval-when (#-sb-xc :compile-toplevel :load-toplevel :execute)
       (do-sc-pairs (from-sc to-sc ',scs)
         (unless (eq from-sc to-sc)
           (let ((num (sc-number from-sc)))
             (setf (svref (sc-move-funs to-sc) num) ',name)
             (setf (svref (sc-load-costs to-sc) num) ',cost)))))

     (defun ,name ,lambda-list
       (sb!assem:assemble (*code-segment* ,(first lambda-list))
         ,@body))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *sc-vop-slots*
    '((:move . sc-move-vops)
      (:move-arg . sc-move-arg-vops))))

;;; Make NAME be the VOP used to move values in the specified FROM-SCs
;;; to the representation of the TO-SCs of each SC pair in SCS.
;;;
;;; If KIND is :MOVE-ARG, then the VOP takes an extra argument,
;;; which is the frame pointer of the frame to move into.
;;;
;;; We record the VOP and costs for all SCs that we can move between
;;; (including implicit loading).
(defmacro define-move-vop (name kind &rest scs)
  (when (or (oddp (length scs)) (null scs))
    (error "malformed SCs spec: ~S" scs))
  (let ((accessor (or (cdr (assoc kind *sc-vop-slots*))
                      (error "unknown kind ~S" kind))))
    `(progn
       ,@(when (eq kind :move)
           `((eval-when (#-sb-xc :compile-toplevel :load-toplevel :execute)
               (do-sc-pairs (from-sc to-sc ',scs)
                 (compute-move-costs from-sc to-sc
                                     ,(vop-info-cost
                                       (template-or-lose name)))))))
       (let ((vop (template-or-lose ',name)))
         (do-sc-pairs (from-sc to-sc ',scs)
           (dolist (dest-sc (cons to-sc (sc-alternate-scs to-sc)))
             (let ((vec (,accessor dest-sc)))
               (let ((scn (sc-number from-sc)))
                 (setf (svref vec scn)
                       (adjoin-template vop (svref vec scn))))
               (dolist (sc (append (sc-alternate-scs from-sc)
                                   (sc-constant-scs from-sc)))
                 (let ((scn (sc-number sc)))
                   (setf (svref vec scn)
                         (adjoin-template vop (svref vec scn))))))))))))

;;;; primitive type definition

;;; Define a primitive type NAME. Each SCS entry specifies a storage
;;; class that values of this type may be allocated in. TYPE is the
;;; type descriptor for the Lisp type that is equivalent to this type.
(defmacro !def-primitive-type (name scs &key (type name))
  (declare (type symbol name) (type list scs))
  `(progn
     (/show0 "doing !DEF-PRIMITIVE-TYPE, NAME=..")
     (/primitive-print ,(symbol-name name))
     (eval-when (#-sb-xc :compile-toplevel :load-toplevel :execute)
       (setf (gethash ',name *backend-primitive-type-names*)
             (make-primitive-type :name ',name
                                  :scs (mapcar #'sc-number-or-lose ',scs)
                                  :specifier ',type)))))

;;; Define NAME to be an alias for RESULT in VOP operand type restrictions.
(defmacro !def-primitive-type-alias (name result)
  ;; Just record the translation.
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (setf (gethash ',name *backend-primitive-type-aliases*) ',result)
     ',name))

(defparameter *primitive-type-slot-alist*
  '((:check . primitive-type-check)))

;;;  Primitive-Type-VOP Vop (Kind*) Type*
;;;
;;; Annotate all the specified primitive Types with the named VOP
;;; under each of the specified kinds:
;;;
;;; :CHECK
;;;    A one-argument one-result VOP that moves the argument to the
;;;    result, checking that the value is of this type in the process.
(defmacro primitive-type-vop (vop kinds &rest types)
  (let ((n-vop (gensym))
        (n-type (gensym)))
    `(let ((,n-vop (template-or-lose ',vop)))
       ,@(mapcar
          (lambda (type)
            `(let ((,n-type (primitive-type-or-lose ',type)))
               ,@(mapcar
                  (lambda (kind)
                    (let ((slot (or (cdr (assoc kind
                                                *primitive-type-slot-alist*))
                                    (error "unknown kind: ~S" kind))))
                      `(setf (,slot ,n-type) ,n-vop)))
                  kinds)))
          types)
       nil)))

;;; An OPERAND-PARSE object contains stuff we need to know about an
;;; operand or temporary at meta-compile time. Besides the obvious
;;; stuff, we also store the names of per-operand temporaries here.
(def!struct (operand-parse
             (:make-load-form-fun just-dump-it-normally))
  ;; name of the operand (which we bind to the TN)
  (name nil :type symbol)
  ;; the way this operand is used:
  (kind (missing-arg)
        :type (member :argument :result :temporary
                      :more-argument :more-result))
  ;; If true, the name of an operand that this operand is targeted to.
  ;; This is only meaningful in :ARGUMENT and :TEMPORARY operands.
  (target nil :type (or symbol null))
  ;; the time that this operand is first live and the time at which it
  ;; becomes dead again. These are TIME-SPECs, as returned by
  ;; PARSE-TIME-SPEC.
  born
  dies
  ;; a list of the names of the SCs that this operand is allowed into.
  ;; If false, there is no restriction.
  (scs nil :type list)
  ;; an expression that tests whether to do automatic operand loading
  (load t)
  ;; In a wired or restricted temporary this is the SC the TN is to be
  ;; packed in. Null otherwise.
  (sc nil :type (or symbol null))
  ;; If non-null, we are a temp wired to this offset in SC.
  (offset nil :type (or unsigned-byte null)))
(defprinter (operand-parse)
  name
  kind
  (target :test target)
  born
  dies
  (scs :test scs)
  (load :test load)
  (sc :test sc)
  (offset :test offset))

;;;; miscellaneous utilities

(defun map-vop-operands (function vop-info)
  (map nil function (vop-info-args vop-info))
  (when (vop-info-more-args vop-info)
    (funcall function (vop-info-more-args vop-info)))
  (map nil function (vop-info-results vop-info))
  (when (vop-info-more-results vop-info)
    (funcall function (vop-info-more-results vop-info)))
  (map nil function (vop-info-temps-parse vop-info)))

(defmacro do-vop-operands ((operand vop-info) &body body)
  (let ((vop-info-sym (gensym "VOP-INFO")))
   `(let ((,vop-info-sym ,vop-info))
      (block nil
        (map-vop-operands (lambda (,operand) ,@body)
                          ,vop-info-sym)))))

;;; Find the operand or temporary with the specifed Name in the VOP
;;; Parse. If there is no such operand, signal an error. Also error if
;;; the operand kind isn't one of the specified Kinds. If Error-P is
;;; NIL, just return NIL if there is no such operand.
(defun find-operand (name vop-info &optional
                          (kinds '(:argument :result :temporary))
                          (error-p t))
  (declare (symbol name))
  (let ((found (do-vop-operands (operand vop-info)
                 (when (eq (operand-parse-name operand)
                           name)
                   (return operand)))))
    (if found
        (unless (member (operand-parse-kind found) kinds)
          (error "Operand ~S isn't one of these kinds: ~S." name kinds))
        (when error-p
          (error "~S is not an operand to ~S." name (vop-info-name vop-info))))
    found))

;;; Return a list of LET-forms to parse a TN-REF list into the temps
;;; specified by the operand-parse structures. MORE-OPERAND is the
;;; OPERAND-PARSE describing any more operand, or NIL if none. REFS is
;;; an expression that evaluates into the first TN-REF.
(defun access-operands (operands more-operand refs)
  (declare (list operands))
  (collect ((res))
    (let ((prev refs))
      (dolist (op operands)
        (let ((n-ref (operand-parse-temp op)))
          (res `(,n-ref ,prev))
          (setq prev `(tn-ref-across ,n-ref))))

      (when more-operand
        (res `(,(operand-parse-name more-operand) ,prev))))
    (res)))

;;; This is used with ACCESS-OPERANDS to prevent warnings for TN-REF
;;; temps not used by some particular function. It returns the name of
;;; the last operand, or NIL if OPERANDS is NIL.
(defun ignore-unreferenced-temps (operands)
  (when operands
    (operand-parse-temp (car (last operands)))))

;;; Grab an arg out of a VOP spec, checking the type and syntax and stuff.
(defun vop-spec-arg (spec type &optional (n 0) (last t))
  (let ((len (length spec)))
    (when (<= len n)
      (error "~:R argument missing: ~S" n spec))
    (when (and last (> len (1+ n)))
      (error "extra junk at end of ~S" spec))
    (let ((thing (elt spec n)))
      (unless (typep thing type)
        (error "~:R argument is not a ~S: ~S" n type spec))
      thing)))

;;;; time specs

;;; Return a time spec describing a time during the evaluation of a
;;; VOP, used to delimit operand and temporary lifetimes. The
;;; representation is a cons whose CAR is the number of the evaluation
;;; phase and the CDR is the sub-phase. The sub-phase is 0 in the
;;; :LOAD and :SAVE phases.
(defun parse-time-spec (spec)
  (let ((dspec (if (atom spec) (list spec 0) spec)))
    (unless (and (= (length dspec) 2)
                 (typep (second dspec) 'unsigned-byte))
      (error "malformed time specifier: ~S" spec))

    (cons (case (first dspec)
            (:load 0)
            (:argument 1)
            (:eval 2)
            (:result 3)
            (:save 4)
            (t
             (error "unknown phase in time specifier: ~S" spec)))
          (second dspec))))

;;; Return true if the time spec X is the same or later time than Y.
(defun time-spec-order (x y)
  (or (> (car x) (car y))
      (and (= (car x) (car y))
           (>= (cdr x) (cdr y)))))

;;;; generation of emit functions

(defun compute-temporaries-description (vop-info)
  (let ((temps (vop-info-temps-parse vop-info))
        ;; (element-type '(unsigned-byte 16))
        )
    (when temps
      (let ((results (make-specializable-array
                      (length temps)
                      ;; :element-type element-type
                      ))
            (index 0))
        (dolist (temp temps)
          (let ((sc (operand-parse-sc temp))
                (offset (operand-parse-offset temp)))
            (aver sc)
            (setf (aref results index)
                  (if offset
                      (+ (ash offset (1+ sc-bits))
                         (ash (sc-number-or-lose sc) 1)
                         1)
                      (ash (sc-number-or-lose sc) 1))))
          (incf index))
        ;; KLUDGE: The load-time MAKE-ARRAY here is an artifact of our
        ;; cross-compilation strategy, and the conservative
        ;; assumptions we are forced to make on which specialized
        ;; arrays exist on the host lisp that the cross-compiler is
        ;; running on.  (We used to use COERCE here, but that caused
        ;; SUBTYPEP calls too early in cold-init for comfort).  --
        ;; CSR, 2009-10-30
        (setf (vop-info-temps vop-info)
              (make-array (length results)
                          ;; :element-type `(specializable ,element-type)
                          :initial-contents results))))))

(defun compute-ref-ordering (vop-info)
  (let* ((num-args (+ (length (vop-info-args vop-info))
                      (if (vop-info-more-args vop-info) 1 0)))
         (num-results (+ (length (vop-info-results vop-info))
                         (if (vop-info-more-results vop-info) 1 0)))
         (index 0))
    (collect ((refs) (targets))
      (do-vop-operands (op vop-info)
        (when (operand-parse-target op)
          (unless (member (operand-parse-kind op) '(:argument :temporary))
            (error "cannot target a ~S operand: ~S" (operand-parse-kind op)
                   (operand-parse-name op)))
          (let ((target (find-operand (operand-parse-target op) vop-info
                                      '(:temporary :result))))
            ;; KLUDGE: These formulas must be consistent with those in
            ;; EMIT-VOP, and this is currently maintained by
            ;; hand. -- WHN 2002-01-30, paraphrasing APD
            (targets (+ (* index max-vop-tn-refs)
                        (ecase (operand-parse-kind target)
                          (:result
                           (+ (position-or-lose target
                                                (vop-info-results vop-info))
                              num-args))
                          (:temporary
                           (+ (* (position-or-lose target
                                                   (vop-info-temps-parse vop-info))
                                 2)
                              1
                              num-args
                              num-results)))))))
        (let ((born (operand-parse-born op))
              (dies (operand-parse-dies op)))
          (ecase (operand-parse-kind op)
            (:argument
             (refs (cons (cons dies nil) index)))
            (:more-argument
             (refs (cons (cons dies nil) index)))
            (:result
             (refs (cons (cons born t) index)))
            (:more-result
             (refs (cons (cons born t) index)))
            (:temporary
             (refs (cons (cons dies nil) index))
             (incf index)
             (refs (cons (cons born t) index))))
          (incf index)))
      (let* ((sorted (stable-sort (refs)
                                  (lambda (x y)
                                    (let ((x-time (car x))
                                          (y-time (car y)))
                                      (if (time-spec-order x-time y-time)
                                          (if (time-spec-order y-time x-time)
                                              (and (not (cdr x)) (cdr y))
                                              nil)
                                          t)))
                                  :key #'car))
             ;; :REF-ORDERING element type
             ;;
             ;; KLUDGE: was (MOD #.MAX-VOP-TN-REFS), which is still right
             ;(oe-type '(unsigned-byte 8))
             ;; :TARGETS element-type
             ;;
             ;; KLUDGE: was (MOD #.(* MAX-VOP-TN-REFS 2)), which does
             ;; not correspond to the definition in
             ;; src/compiler/vop.lisp.
             ;(te-type '(unsigned-byte 16))
             (ordering (make-specializable-array
                        (length sorted)
                        ;; :element-type oe-type
                        )))
        (let ((index 0))
          (dolist (ref sorted)
            (setf (aref ordering index) (cdr ref))
            (incf index)))
        (setf (vop-info-num-args vop-info) num-args
              (vop-info-num-results vop-info) num-results
              ;; KLUDGE: see the comment regarding MAKE-ARRAY in
              ;; COMPUTE-TEMPORARIES-DESCRIPTION.  -- CSR, 2009-10-30
              (vop-info-ref-ordering vop-info)
              (make-array (length ordering)
                          :initial-contents ordering
                          ;; :element-type `(specializable ,oe-type)
                          ))
        (when (targets)
          (setf (vop-info-targets vop-info)
                (make-array (length (targets))
                            :initial-contents (targets)
                            ;; :element-type `(specializable ,te-type)
                            )))))))


;;;; generator functions

;;; Return an alist that translates from lists of SCs we can load OP
;;; from to the move function used for loading those SCs. We quietly
;;; ignore restrictions to :non-packed (constant) and :unbounded SCs,
;;; since we don't load into those SCs.
(defun find-move-funs (op load-p)
  (collect ((funs))
    (dolist (sc-name (operand-parse-scs op))
      (let* ((sc (sc-or-lose sc-name))
             (scn (sc-number sc))
             (load-scs (append (when load-p
                                 (sc-constant-scs sc))
                               (sc-alternate-scs sc))))
        (cond
         (load-scs
          (dolist (alt load-scs)
            (unless (member (sc-name alt) (operand-parse-scs op) :test #'eq)
              (let* ((altn (sc-number alt))
                     (name (if load-p
                               (svref (sc-move-funs sc) altn)
                               (svref (sc-move-funs alt) scn)))
                     (found (or (assoc alt (funs) :test #'member)
                                (rassoc name (funs)))))
                (unless name
                  (error "no move function defined to ~:[save~;load~] SC ~S ~
                          ~:[to~;from~] from SC ~S"
                         load-p sc-name load-p (sc-name alt)))

                (cond (found
                       (unless (eq (cdr found) name)
                         (error "can't tell whether to ~:[save~;load~]~@
                                 with ~S or ~S when operand is in SC ~S"
                                load-p name (cdr found) (sc-name alt)))
                       (pushnew alt (car found)))
                      (t
                       (funs (cons (list alt) name))))))))
         ((member (sb-kind (sc-sb sc)) '(:non-packed :unbounded)))
         (t
          (error "SC ~S has no alternate~:[~; or constant~] SCs, yet it is~@
                  mentioned in the restriction for operand ~S"
                 sc-name load-p (operand-parse-name op))))))
    (funs)))

;;; Return a form to load/save the specified operand when it has a
;;; load TN. For any given SC that we can load from, there must be a
;;; unique load function. If all SCs we can load from have the same
;;; move function, then we just call that when there is a load TN. If
;;; there are multiple possible move functions, then we dispatch off
;;; of the operand TN's type to see which move function to use.
(defun call-move-fun (vop-info op load-p)
  (let ((funs (find-move-funs op load-p))
        (load-tn (operand-parse-load-tn op)))
    (if funs
        (let* ((tn `(tn-ref-tn ,(operand-parse-temp op)))
               (n-vop (or (vop-info-vop-var vop-info)
                          (setf (vop-info-vop-var vop-info) '.vop.)))
               (form (if (rest funs)
                         `(sc-case ,tn
                            ,@(mapcar (lambda (x)
                                        `(,(mapcar #'sc-name (car x))
                                          ,(if load-p
                                               `(,(cdr x) ,n-vop ,tn
                                                 ,load-tn)
                                               `(,(cdr x) ,n-vop ,load-tn
                                                 ,tn))))
                                      funs))
                         (if load-p
                             `(,(cdr (first funs)) ,n-vop ,tn ,load-tn)
                             `(,(cdr (first funs)) ,n-vop ,load-tn ,tn)))))
          (if (eq (operand-parse-load op) t)
              `(when ,load-tn ,form)
              `(when (eq ,load-tn ,(operand-parse-name op))
                 ,form)))
        `(when ,load-tn
           (error "load TN allocated, but no move function?~@
                   VM definition is inconsistent, recompile and try again.")))))

;;; Return the TN that we should bind to the operand's var in the
;;; generator body. In general, this involves evaluating the :LOAD-IF
;;; test expression.
(defun decide-to-load (vop-info op)
  (let ((load (operand-parse-load op))
        (load-tn (operand-parse-load-tn op))
        (temp (operand-parse-temp op)))
    (if (eq load t)
        `(or ,load-tn (tn-ref-tn ,temp))
        (collect ((binds)
                  (ignores))
          (do-vop-operands (x vop-info)
            (when (member (operand-parse-kind x) '(:argument :result))
              (let ((name (operand-parse-name x)))
                (binds `(,name (tn-ref-tn ,(operand-parse-temp x))))
                (ignores name))))
          `(if (and ,load-tn
                    (let ,(binds)
                      (declare (ignorable ,@(ignores)))
                      ,load))
               ,load-tn
               (tn-ref-tn ,temp))))))

(defvar *operand-parse-temps*)
(defvar *operand-id*)

(defun make-operand-parse-variables ()
  (without-package-locks
    (prog1 (cons (intern (format nil "OPERAND-PARSE-TEMP-~D" *operand-id*)
                         (symbol-package '*parse-vop-operand-count*))
                 (intern (format nil "OPERAND-PARSE-LOAD-TN-~D" *operand-id*)
                         (symbol-package '*parse-vop-operand-count*)))
      (incf *operand-id*))))

(defun operand-parse-temp (op)
  (car (or (gethash op *operand-parse-temps*)
           (setf (gethash op *operand-parse-temps*)
                 (make-operand-parse-variables)))))

(defun operand-parse-load-tn (op)
  (cdr (or (gethash op *operand-parse-temps*)
           (setf (gethash op *operand-parse-temps*)
                 (make-operand-parse-variables)))))

;;; Make a lambda that parses the VOP TN-REFS, does automatic operand
;;; loading, and runs the appropriate code generator.
(defun make-generator-function (vop-info)
  (let ((n-vop (vop-info-vop-var vop-info))
        (n-info (gensym))
        (n-variant (gensym))
        (*operand-id* 0)
        (*operand-parse-temps* (make-hash-table :test 'eq)))
    (collect ((binds)
              (loads)
              (saves))
      (do-vop-operands (op vop-info)
        (let ((temp (operand-parse-temp op))
              (name (operand-parse-name op)))
          (ecase (operand-parse-kind op)
            ((:argument :result)
             (cond ((and (operand-parse-load op) (operand-parse-scs op))
                    (binds `(,(operand-parse-load-tn op)
                             (tn-ref-load-tn ,temp)))
                    (binds `(,name ,(decide-to-load vop-info op)))
                    (if (eq (operand-parse-kind op) :argument)
                        (loads (call-move-fun vop-info op t))
                        (saves (call-move-fun vop-info op nil))))
                   (t
                    (binds `(,name (tn-ref-tn ,temp))))))
            (:temporary
             (binds `(,name (tn-ref-tn ,temp))))
            ((:more-argument :more-result)))))
      `(lambda (,n-vop)
         (let* (,@(access-operands (vop-info-args vop-info)
                                   (vop-info-more-args vop-info)
                                   `(vop-args ,n-vop))
                  ,@(access-operands (vop-info-results vop-info)
                                     (vop-info-more-results vop-info)
                                     `(vop-results ,n-vop))
                  ,@(access-operands (vop-info-temps-parse vop-info) nil
                                     `(vop-temps ,n-vop))
                  ,@(when (vop-info-info-args vop-info)
                      `((,n-info (vop-codegen-info ,n-vop))
                        ,@(mapcar (lambda (x) `(,x (pop ,n-info)))
                                  (vop-info-info-args vop-info))))
                  ,@(when (vop-info-variant-vars vop-info)
                      `((,n-variant (vop-info-variant (vop-info ,n-vop)))
                        ,@(mapcar (lambda (x) `(,x (pop ,n-variant)))
                                  (vop-info-variant-vars vop-info))))
                  ,@(when (vop-info-node-var vop-info)
                      `((,(vop-info-node-var vop-info) (vop-node ,n-vop))))
                  ,@(binds))
           (declare (ignore ,@(vop-info-ignores vop-info)))
           ,@(loads)
           (sb!assem:assemble (*code-segment* ,n-vop)
             ,@(vop-info-body vop-info))
           ,@(saves))))))


;;; Given a list of operand specifications as given to DEFINE-VOP,
;;; return a list of OPERAND-PARSE structures describing the fixed
;;; operands, and a single OPERAND-PARSE describing any more operand.
;;; If we are inheriting a VOP, we default attributes to the inherited
;;; operand of the same name.
(defun parse-vop-operands (super-vop specs kind)
  (declare (list specs)
           (type (member :argument :result) kind))
  (let ((num -1)
        (more nil))
    (collect ((operands))
      (dolist (spec specs)
        (unless (and (consp spec) (symbolp (first spec)) (oddp (length spec)))
          (error "malformed operand specifier: ~S" spec))
        (when more
          (error "The MORE operand isn't the last operand: ~S" specs))
        (let* ((name (first spec))
               (old (and super-vop
                         (find-operand name super-vop (list kind) nil)))
               (res (if old
                        (make-operand-parse
                         :name name
                         :kind kind
                         :target (operand-parse-target old)
                         :born (operand-parse-born old)
                         :dies (operand-parse-dies old)
                         :scs (operand-parse-scs old)
                         :load (operand-parse-load old))
                        (ecase kind
                          (:argument
                           (make-operand-parse
                            :name (first spec)
                            :kind :argument
                            :born (parse-time-spec :load)
                            :dies (parse-time-spec `(:argument ,(incf num)))))
                          (:result
                           (make-operand-parse
                            :name (first spec)
                            :kind :result
                            :born (parse-time-spec `(:result ,(incf num)))
                            :dies (parse-time-spec :save)))))))
          (do ((key (rest spec) (cddr key)))
              ((null key))
            (let ((value (second key)))
              (case (first key)
                (:scs
                 (aver (listp value))
                 (setf (operand-parse-scs res) (remove-duplicates value)))
                (:load-if
                 (setf (operand-parse-load res) value))
                (:more
                 (aver (typep value 'boolean))
                 (setf (operand-parse-kind res)
                       (if (eq kind :argument) :more-argument :more-result))
                 (setf (operand-parse-load res) nil)
                 (setq more res))
                (:target
                 (aver (symbolp value))
                 (setf (operand-parse-target res) value))
                (:from
                 (unless (eq kind :result)
                   (error "can only specify :FROM in a result: ~S" spec))
                 (setf (operand-parse-born res) (parse-time-spec value)))
                (:to
                 (unless (eq kind :argument)
                   (error "can only specify :TO in an argument: ~S" spec))
                 (setf (operand-parse-dies res) (parse-time-spec value)))
                (t
                 (error "unknown keyword in operand specifier: ~S" spec)))))

          (cond ((not more)
                 (operands res))
                ((operand-parse-target more)
                 (error "cannot specify :TARGET in a :MORE operand"))
                ((operand-parse-load more)
                 (error "cannot specify :LOAD-IF in a :MORE operand")))))
      (values (operands) more))))

;;; Parse a temporary specification, putting the OPERAND-PARSE
;;; structures in the PARSE structure.
(defun parse-temporary (spec vop-info)
  (declare (list spec)
           (type vop-info vop-info))
  (let ((len (length spec)))
    (unless (>= len 2)
      (error "malformed temporary spec: ~S" spec))
    (unless (listp (second spec))
      (error "malformed options list: ~S" (second spec)))
    (unless (evenp (length (second spec)))
      (error "odd number of arguments in keyword options: ~S" spec))
    (unless (consp (cddr spec))
      (warn "temporary spec allocates no temps:~%  ~S" spec))
    (dolist (name (cddr spec))
      (unless (symbolp name)
        (error "bad temporary name: ~S" name))
      (let ((res (make-operand-parse :name name
                                     :kind :temporary
                                     :born (parse-time-spec :load)
                                     :dies (parse-time-spec :save))))
        (do ((opt (second spec) (cddr opt)))
            ((null opt))
          (case (first opt)
            (:target
             (setf (operand-parse-target res)
                   (vop-spec-arg opt 'symbol 1 nil)))
            (:sc
             (setf (operand-parse-sc res)
                   (vop-spec-arg opt 'symbol 1 nil)))
            (:offset
             (let ((offset (eval (second opt))))
               (aver (typep offset 'unsigned-byte))
               (setf (operand-parse-offset res) offset)))
            (:from
             (setf (operand-parse-born res) (parse-time-spec (second opt))))
            (:to
             (setf (operand-parse-dies res) (parse-time-spec (second opt))))
            ;; backward compatibility...
            (:scs
             (let ((scs (vop-spec-arg opt 'list 1 nil)))
               (unless (= (length scs) 1)
                 (error "must specify exactly one SC for a temporary"))
               (setf (operand-parse-sc res) (first scs))))
            (:type)
            (t
             (error "unknown temporary option: ~S" opt))))

        (unless (and (time-spec-order (operand-parse-dies res)
                                      (operand-parse-born res))
                     (not (time-spec-order (operand-parse-born res)
                                           (operand-parse-dies res))))
          (error "Temporary lifetime doesn't begin before it ends: ~S" spec))

        (unless (operand-parse-sc res)
          (error "must specify :SC for all temporaries: ~S" spec))

        (setf (vop-info-temps-parse vop-info)
              (cons res
                    (remove name (vop-info-temps-parse vop-info)
                            :key #'operand-parse-name))))))
  (values))

(defparameter *vop-arguments-order*
  '(:args :results :conditional :temporary
    :effects :affected :info :ignore
    :variant-vars :variant :vop-var :node-var :move-args :note :result-types
    :guard :policy :save-p
    :generator :translate))

(defun sort-vop-arguments (specs)
  (sort (copy-list specs)
        #'<
        :key (lambda (x)
               (cond ((not (consp x))
                      -1)
                     ((position (car x) *vop-arguments-order*))
                     (t
                      most-positive-fixnum)))))

;;; Fill the VOP-INFO structure and return three values
;;; to be put into the macorexpansion:
;;; lambda-expressions for GENERATOR-FUNCTION and GUARD
;;; and a form for VARIANT
(defun parse-define-vop (vop-info super-vop specs &key compile-time)
  (let (guard
        parameters-changed
        variant
        (arg-types (and super-vop
                        (vop-info-arg-types super-vop)))
        (result-types (and super-vop
                           (vop-info-result-types super-vop))))
    (dolist (spec (sort-vop-arguments specs))
      (unless (consp spec)
        (error "malformed option specification: ~S" spec))
      (let ((key (car spec))
            (args (cdr spec)))
        (case key
          (:args
           (multiple-value-bind (args more-args)
               (parse-vop-operands super-vop args :argument)
             (setf (vop-info-args vop-info) args
                   (vop-info-more-args vop-info) more-args)
             (setf (values (vop-info-arg-costs vop-info)
                           (vop-info-arg-load-scs vop-info))
                   (compute-costs-and-restrictions-list args t))
             (setf (vop-info-more-arg-costs vop-info)
                   (and more-args
                        (compute-loading-costs-if-any more-args t))))
           (setf parameters-changed t))
          (:results
           (multiple-value-bind (results more-results)
               (parse-vop-operands super-vop args :result)
             (setf (vop-info-results vop-info) results
                   (vop-info-more-results vop-info) more-results)
             (setf (values (vop-info-result-costs vop-info)
                           (vop-info-result-load-scs vop-info))
                   (compute-costs-and-restrictions-list results nil))
             (setf (vop-info-more-result-costs vop-info)
                   (and more-results
                        (compute-loading-costs-if-any more-results nil))))
           (setf parameters-changed t))
          (:info
           (setf (vop-info-info-args vop-info) args)
           (setf parameters-changed t))
          (:arg-types
           (setf arg-types (parse-vop-operand-types args t)))
          (:result-types
           (setf result-types (parse-vop-operand-types args nil)))
          (:conditional
           (setf (vop-info-result-types vop-info)
                 (if (eq (car args) t)
                     :conditional
                     spec)))
          (:temporary
           (parse-temporary spec vop-info)
           (setf parameters-changed t))
          (:generator
           (setf (vop-info-cost vop-info)
                 (vop-spec-arg args 'unsigned-byte 0 nil))
           (unless (equal (cdr args)
                          (and super-vop
                               (vop-info-body super-vop)))
             (setf (vop-info-body vop-info) (cdr args)
                   parameters-changed t)))
          (:effects
           (setf (vop-info-effects vop-info)
                 (apply #'vop-attributes args)))
          (:affected
           (setf (vop-info-affected vop-info)
                 (apply #'vop-attributes args)))
          (:ignore
           (setf (vop-info-ignores vop-info) args))
          (:variant-vars
           (setf (vop-info-variant-vars vop-info) args))
          (:variant
           (setf variant args)
           (when (/= (length args)
                     (length (vop-info-variant-vars vop-info)))
             (error "Expected ~W variant values: ~S"
                    (length args)
                    (length (vop-info-variant-vars vop-info)))))
          (:variant-cost
           (setf (vop-info-cost vop-info)
                 (vop-spec-arg args 'unsigned-byte)))
          (:vop-var
           (setf (vop-info-vop-var vop-info)
                 (vop-spec-arg args 'symbol)))
          (:node-var
           (setf (vop-info-node-var vop-info)
                 (vop-spec-arg args 'symbol)))
          (:move-args
           (setf (vop-info-move-args vop-info)
                 (vop-spec-arg args
                               '(member nil :local-call :full-call
                                 :known-return))))
          (:note
           (setf (vop-info-note vop-info)
                 (vop-spec-arg args '(or string null))))
          (:translate
           (unless compile-time
             (set-up-fun-translation vop-info args)))
          (:guard
           (setf guard
                 `(lambda ()
                    ,(vop-spec-arg args t))))
          ;; FIXME: :LTN-POLICY would be a better name for this. It
          ;; would probably be good to leave it unchanged for a while,
          ;; though, at least until the first port to some other
          ;; architecture, since the renaming would be a change to the
          ;; interface between
          (:policy
           (setf (vop-info-ltn-policy vop-info)
                 (vop-spec-arg args 'ltn-policy)))
          (:save-p
           (setf (vop-info-save-p vop-info)
                 (vop-spec-arg args
                               '(member t nil :compute-only :force-to-stack))))
          (t
           (error "unknown option specifier: ~S" key)))))
    (set-vop-info-types vop-info arg-types result-types)
    (compute-temporaries-description vop-info)
    (compute-ref-ordering vop-info)
    (setf (vop-info-type vop-info)
          (vop-info-type-specifier vop-info))
    (check-vop-operands vop-info arg-types result-types)
    (values (and parameters-changed
                 (vop-info-body vop-info)
                 (make-generator-function vop-info))
            guard
            variant)))

;;;; making costs and restrictions

;;; Given an operand, returns two values:
;;; 1. A SC-vector of the cost for the operand being in that SC,
;;;    including both the costs for move functions and coercion VOPs.
;;; 2. A SC-vector holding the SC that we load into, for any SC
;;;    that we can directly load from.
;;;
;;; In both vectors, unused entries are NIL. LOAD-P specifies the
;;; direction: if true, we are loading, if false we are saving.
(defun compute-loading-costs (op load-p)
  (declare (type operand-parse op))
  (let ((scs (operand-parse-scs op))
        (costs (make-array sc-number-limit :initial-element nil))
        (load-scs (make-array sc-number-limit :initial-element nil)))
    (dolist (sc-name scs)
      (let* ((load-sc (sc-or-lose sc-name))
             (load-scn (sc-number load-sc)))
        (setf (svref costs load-scn) 0)
        (setf (svref load-scs load-scn) t)
        (dolist (op-sc (append (when load-p
                                 (sc-constant-scs load-sc))
                               (sc-alternate-scs load-sc)))
          (let* ((op-scn (sc-number op-sc))
                 (load (if load-p
                           (aref (sc-load-costs load-sc) op-scn)
                           (aref (sc-load-costs op-sc) load-scn))))
            (unless load
              (error "no move function defined to move ~:[from~;to~] SC ~
                      ~S~%~:[to~;from~] alternate or constant SC ~S"
                     load-p sc-name load-p (sc-name op-sc)))

            (let ((op-cost (svref costs op-scn)))
              (when (or (not op-cost) (< load op-cost))
                (setf (svref costs op-scn) load)))

            (let ((op-load (svref load-scs op-scn)))
              (unless (eq op-load t)
                (pushnew load-scn (svref load-scs op-scn))))))

        (dotimes (i sc-number-limit)
          (unless (svref costs i)
            (let ((op-sc (svref *backend-sc-numbers* i)))
              (when op-sc
                (let ((cost (if load-p
                                (svref (sc-move-costs load-sc) i)
                                (svref (sc-move-costs op-sc) load-scn))))
                  (when cost
                    (setf (svref costs i) cost)))))))))

    (values costs load-scs)))

(defparameter *no-costs*
  (make-array sc-number-limit :initial-element 0))

(defparameter *no-loads*
  (make-array sc-number-limit :initial-element t))

;;; Pick off the case of operands with no restrictions.
(defun compute-loading-costs-if-any (op load-p)
  (declare (type operand-parse op))
  (if (operand-parse-scs op)
      (compute-loading-costs op load-p)
      (values *no-costs* *no-loads*)))

(defun compute-costs-and-restrictions-list (ops load-p)
  (declare (list ops))
  (collect ((costs)
            (scs))
    (dolist (op ops)
      (multiple-value-bind (costs scs) (compute-loading-costs-if-any op load-p)
        (costs costs)
        (scs scs)))
    (values (costs) (scs))))


;;;; operand checking and stuff

;;; Given a list of arg/result restrictions, check for valid syntax
;;; and convert to canonical form.
(defun parse-vop-operand-types (specs args-p)
  (declare (list specs))
  (labels ((parse-operand-type (spec)
             (cond ((eq spec '*) spec)
                   ((symbolp spec)
                    (let ((alias (gethash spec
                                          *backend-primitive-type-aliases*)))
                      (if alias
                          (parse-operand-type alias)
                          `(:or ,spec))))
                   ((atom spec)
                    (error "bad thing to be a operand type: ~S" spec))
                   (t
                    (case (first spec)
                      (:or
                       (collect ((results))
                         (results :or)
                         (dolist (item (cdr spec))
                           (unless (symbolp item)
                             (error "bad PRIMITIVE-TYPE name in ~S: ~S"
                                    spec item))
                           (let ((alias
                                  (gethash item
                                           *backend-primitive-type-aliases*)))
                             (if alias
                                 (let ((alias (parse-operand-type alias)))
                                  (unless (eq (car alias) :or)
                                     (error "can't include primitive-type ~
                                             alias ~S in an :OR restriction: ~S"
                                            item spec))
                                   (dolist (x (cdr alias))
                                     (results x)))
                                 (results item))))
                         (remove-duplicates (results)
                                            :test #'eq
                                            :start 1)))
                      (:constant
                       (unless args-p
                         (error "can't :CONSTANT for a result"))
                       (unless (= (length spec) 2)
                         (error "bad :CONSTANT argument type spec: ~S" spec))
                       spec)
                      (t
                       (error "bad thing to be a operand type: ~S" spec)))))))
    (mapcar #'parse-operand-type specs)))

;;; Check the consistency of OP's SC restrictions with the specified
;;; primitive-type restriction. :CONSTANT operands have already been
;;; filtered out, so only :OR and * restrictions are left.
;;;
;;; We check that every representation allowed by the type can be
;;; directly loaded into some SC in the restriction, and that the type
;;; allows every SC in the restriction. With *, we require that T
;;; satisfy the first test, and omit the second.
(defun check-operand-type-scs (parse op type load-p)
  (let ((ptypes (if (eq type '*) (list t) (rest type)))
        (scs (operand-parse-scs op)))
    (when scs
      (multiple-value-bind (costs load-scs) (compute-loading-costs op load-p)
        (declare (ignore costs))
        (dolist (ptype ptypes)
          (unless (dolist (rep (primitive-type-scs
                                (primitive-type-or-lose ptype))
                               nil)
                    (when (svref load-scs rep) (return t)))
            (error "In the ~A ~:[result~;argument~] to VOP ~S,~@
                    none of the SCs allowed by the operand type ~S can ~
                    directly be loaded~@
                    into any of the restriction's SCs:~%  ~S~:[~;~@
                    [* type operand must allow T's SCs.]~]"
                   (operand-parse-name op) load-p (vop-info-name parse)
                   ptype
                   scs (eq type '*)))))

      (dolist (sc scs)
        (unless (or (eq type '*)
                    (dolist (ptype ptypes nil)
                      (when (sc-allowed-by-primitive-type
                             (sc-or-lose sc)
                             (primitive-type-or-lose ptype))
                        (return t))))
          (warn "~:[Result~;Argument~] ~A to VOP ~S~@
                 has SC restriction ~S which is ~
                 not allowed by the operand type:~%  ~S"
                load-p (operand-parse-name op) (vop-info-name parse)
                sc type)))))

  (values))

;;; Consider types consiting only of * to be the same as unspecified at all
(defun vop-unspecified-types-p (types)
  (not (member '* types :test-not #'eq)))

;;; If the operand types are specified, then check the number specified
;;; against the number of defined operands.
(defun check-operand-types (vop-info ops more-op types load-p)
  (declare (type vop-info vop-info) (list ops)
           (type list types)
           (type (or operand-parse null) more-op))
  (unless (or (eq types :conditional)
              (eq (car types) :conditional)
              (vop-unspecified-types-p types))
    (let ((num (+ (length ops) (if more-op 1 0))))
      (unless (= (count-if-not (lambda (x)
                                 (and (consp x)
                                      (eq (car x) :constant)))
                               types)
                 num)
        (error "expected ~W ~:[result~;argument~] type~P: ~S"
               num load-p types num)))

    (when more-op
      (let ((mtype (car (last types))))
        (when (and (consp mtype) (eq (first mtype) :constant))
          (error "can't use :CONSTANT on VOP more args")))))

  (when (vop-info-translate vop-info)
    (let ((types (specify-operand-types types ops more-op)))
      (mapc (lambda (x y)
              (check-operand-type-scs vop-info x y load-p))
            (if more-op (butlast ops) ops)
            (remove-if (lambda (x)
                         (and (consp x)
                              (eq (car x) ':constant)))
                       (if more-op (butlast types) types)))))

  (values))

(defun check-vop-operands (vop-info arg-types result-types)
  (check-operand-types vop-info
                       (vop-info-args vop-info)
                       (vop-info-more-args vop-info)
                       arg-types
                       t)
  (check-operand-types vop-info
                       (vop-info-results vop-info)
                       (vop-info-more-results vop-info)
                       result-types
                       nil)
  (values))

;;;; function translation stuff

;;; Establish this VOP as a IR2 translation template.
;;; We also set the PREDICATE attribute for each translated function
;;; when the VOP is conditional, causing IR1 conversion to ensure that
;;; a call to the translated is always used in a predicate position.
(defun set-up-fun-translation (vop-info translate-names)
  (mapc (lambda (name)
          (let ((info (fun-info-or-lose name)))
            (setf (fun-info-templates info)
                  (adjoin-template vop-info (fun-info-templates info)))
            (when (vop-info-conditional-p vop-info)
              (setf (fun-info-attributes info)
                    (attributes-union
                     (ir1-attributes 'predicate)
                     (fun-info-attributes info))))))
        translate-names))

;;; Return a form that can be evaluated to get the TEMPLATE operand type
;;; restriction from the given specification.
(defun make-operand-type (type)
  (cond ((eq type '*) '*)
        ((symbolp type)
         `(:or ,(primitive-type-or-lose type)))
        (t
         (ecase (first type)
           (:or
            (if (primitive-type-p (cadr type))
                type
                `(:or ,@(mapcar (lambda (type)
                                  (primitive-type-or-lose type))
                                (rest type)))))
           (:constant
            `(:constant ,(second type)))))))

(defun specify-operand-types (types ops more-ops)
  ;; NOTE: maybe share lists?
  (let ((length (+ (length ops) (if more-ops 1 0))))
    (if (and (vop-unspecified-types-p types)
             (/= length (length types)))
        (make-list length :initial-element '*)
        types)))

;;; Here we make an initial dummy TEMPLATE-TYPE, since it is awkward
;;; to compute the type until the template has been made.
(defun set-vop-info-types (vop-info arg-types result-types)
  (let* ((more-args (vop-info-more-args vop-info))
         (all-args (specify-operand-types arg-types
                                          (vop-info-args vop-info)
                                          more-args))
         (args (if more-args (butlast all-args) all-args))
         (more-arg (when more-args (car (last all-args))))
         (more-results (vop-info-more-results vop-info))
         (all-results (specify-operand-types result-types
                                             (vop-info-results vop-info)
                                             more-results))
         (results (if more-results (butlast all-results) all-results))
         (more-result (when more-results (car (last all-results))))
         (conditional (vop-info-conditional-p vop-info)))
    (setf
     (vop-info-type vop-info) (specifier-type '(function () nil))
     (vop-info-arg-types vop-info) (mapcar #'make-operand-type args)
     (vop-info-more-args-type vop-info) (and more-arg (make-operand-type more-arg)))
    (unless conditional
      (setf (vop-info-result-types vop-info) (mapcar #'make-operand-type results)))
    (when more-results
      (setf (vop-info-more-results-type vop-info)
            (make-operand-type more-result)))))

;;; Define the symbol NAME to be a Virtual OPeration in the compiler.
;;; If specified, INHERITS is the name of a VOP that we default
;;; unspecified information from. Each SPEC is a list beginning with a
;;; keyword indicating the interpretation of the other forms in the
;;; SPEC:
;;;
;;; :ARGS {(Name {Key Value}*)}*
;;; :RESULTS {(Name {Key Value}*)}*
;;;     The Args and Results are specifications of the operand TNs passed
;;;     to the VOP. If there is an inherited VOP, any unspecified options
;;;     are defaulted from the inherited argument (or result) of the same
;;;     name. The following operand options are defined:
;;;
;;;     :SCs (SC*)
;;;         :SCs specifies good SCs for this operand. Other SCs will
;;;         be penalized according to move costs. A load TN will be
;;;         allocated if necessary, guaranteeing that the operand is
;;;         always one of the specified SCs.
;;;
;;;     :LOAD-TN Load-Name
;;;         Load-Name is bound to the load TN allocated for this
;;;         operand, or to NIL if no load TN was allocated.
;;;
;;;     :LOAD-IF EXPRESSION
;;;         Controls whether automatic operand loading is done.
;;;         EXPRESSION is evaluated with the fixed operand TNs bound.
;;;         If EXPRESSION is true, then loading is done and the variable
;;;         is bound to the load TN in the generator body. Otherwise,
;;;         loading is not done, and the variable is bound to the actual
;;;         operand.
;;;
;;;     :MORE T-or-NIL
;;;         If specified, NAME is bound to the TN-REF for the first
;;;         argument or result following the fixed arguments or results.
;;;         A :MORE operand must appear last, and cannot be targeted or
;;;         restricted.
;;;
;;;     :TARGET Operand
;;;         This operand is targeted to the named operand, indicating a
;;;         desire to pack in the same location. Not legal for results.
;;;
;;;     :FROM Time-Spec
;;;     :TO Time-Spec
;;;         Specify the beginning or end of the operand's lifetime.
;;;         :FROM can only be used with results, and :TO only with
;;;         arguments. The default for the N'th argument/result is
;;;         (:ARGUMENT N)/(:RESULT N). These options are necessary
;;;         primarily when operands are read or written out of order.
;;;
;;; :CONDITIONAL [Condition-descriptor+]
;;;     This is used in place of :RESULTS with conditional branch VOPs.
;;;     There are no result values: the result is a transfer of control.
;;;     The target label is passed as the first :INFO arg. The second
;;;     :INFO arg is true if the sense of the test should be negated.
;;;     A side effect is to set the PREDICATE attribute for functions
;;;     in the :TRANSLATE option.
;;;
;;;     If some condition descriptors are provided, this is a flag-setting
;;;     VOP. Descriptors are interpreted in an architecture-dependent
;;;     manner. See the BRANCH-IF VOP in $ARCH/pred.lisp.
;;;
;;; :TEMPORARY ({Key Value}*) Name*
;;;     Allocate a temporary TN for each Name, binding that variable to
;;;     the TN within the body of the generators. In addition to :TARGET
;;;     (which is is the same as for operands), the following options are
;;;     defined:
;;;
;;;     :SC SC-Name
;;;     :OFFSET SB-Offset
;;;         Force the temporary to be allocated in the specified SC
;;;         with the specified offset. Offset is evaluated at
;;;         macroexpand time. If Offset is omitted, the register
;;;         allocator chooses a free location in SC. If both SC and
;;;         Offset are omitted, then the temporary is packed according
;;;         to its primitive type.
;;;
;;;     :FROM Time-Spec
;;;     :TO Time-Spec
;;;         Similar to the argument/result option, this specifies the
;;;         start and end of the temporaries' lives. The defaults are
;;;         :LOAD and :SAVE, i.e. the duration of the VOP. The other
;;;         intervening phases are :ARGUMENT, :EVAL and :RESULT.
;;;         Non-zero sub-phases can be specified by a list, e.g. by
;;;         default the second argument's life ends at (:ARGUMENT 1).
;;;
;;; :GENERATOR Cost Form*
;;;     Specifies the translation into assembly code. Cost is the
;;;     estimated cost of the code emitted by this generator. The body
;;;     is arbitrary Lisp code that emits the assembly language
;;;     translation of the VOP. An ASSEMBLE form is wrapped around
;;;     the body, so code may be emitted by using the local INST macro.
;;;     During the evaluation of the body, the names of the operands
;;;     and temporaries are bound to the actual TNs.
;;;
;;; :EFFECTS Effect*
;;; :AFFECTED Effect*
;;;     Specifies the side effects that this VOP has and the side
;;;     effects that effect its execution. If unspecified, these
;;;     default to the worst case.
;;;
;;; :INFO Name*
;;;     Define some magic arguments that are passed directly to the code
;;;     generator. The corresponding trailing arguments to VOP or
;;;     %PRIMITIVE are stored in the VOP structure. Within the body
;;;     of the generators, the named variables are bound to these
;;;     values. Except in the case of :CONDITIONAL VOPs, :INFO arguments
;;;     cannot be specified for VOPS that are the direct translation
;;;     for a function (specified by :TRANSLATE).
;;;
;;; :IGNORE Name*
;;;     Causes the named variables to be declared IGNORE in the
;;;     generator body.
;;;
;;; :VARIANT Thing*
;;; :VARIANT-VARS Name*
;;;     These options provide a way to parameterize families of VOPs
;;;     that differ only trivially. :VARIANT makes the specified
;;;     evaluated Things be the "variant" associated with this VOP.
;;;     :VARIANT-VARS causes the named variables to be bound to the
;;;     corresponding Things within the body of the generator.
;;;
;;; :VARIANT-COST Cost
;;;     Specifies the cost of this VOP, overriding the cost of any
;;;     inherited generator.
;;;
;;; :NOTE {String | NIL}
;;;     A short noun-like phrase describing what this VOP "does", i.e.
;;;     the implementation strategy. If supplied, efficiency notes will
;;;     be generated when type uncertainty prevents :TRANSLATE from
;;;     working. NIL inhibits any efficiency note.
;;;
;;; :ARG-TYPES    {* | PType | (:OR PType*) | (:CONSTANT Type)}*
;;; :RESULT-TYPES {* | PType | (:OR PType*)}*
;;;     Specify the template type restrictions used for automatic
;;;     translation. If there is a :MORE operand, the last type is the
;;;     more type. :CONSTANT specifies that the argument must be a
;;;     compile-time constant of the specified Lisp type. The constant
;;;     values of :CONSTANT arguments are passed as additional :INFO
;;;     arguments rather than as :ARGS.
;;;
;;; :TRANSLATE Name*
;;;     This option causes the VOP template to be entered as an IR2
;;;     translation for the named functions.
;;;
;;; :POLICY {:SMALL | :FAST | :SAFE | :FAST-SAFE}
;;;     Specifies the policy under which this VOP is the best translation.
;;;
;;; :GUARD Form
;;;     Specifies a Form that is evaluated in the global environment.
;;;     If form returns NIL, then emission of this VOP is prohibited
;;;     even when all other restrictions are met.
;;;
;;; :VOP-VAR Name
;;; :NODE-VAR Name
;;;     In the generator, bind the specified variable to the VOP or
;;;     the Node that generated this VOP.
;;;
;;; :SAVE-P {NIL | T | :COMPUTE-ONLY | :FORCE-TO-STACK}
;;;     Indicates how a VOP wants live registers saved.
;;;
;;; :MOVE-ARGS {NIL | :FULL-CALL | :LOCAL-CALL | :KNOWN-RETURN}
;;;     Indicates if and how the more args should be moved into a
;;;     different frame.
(defmacro define-vop ((name &optional inherits) &body specs)
  (declare (type symbol name))
  ;; Parse the syntax into a VOP-INFO structure, and then expand into
  ;; code that creates the appropriate VOP-INFO structure at load time.
  ;; We implement inheritance by copying the VOP-INFO structure for
  ;; the inherited structure.
  (let* ((inherited-vop (and inherits
                             (template-or-lose inherits)))
         (vop-info (if inherits
                       (copy-vop-info inherited-vop)
                       (make-vop-info)))
         (super-vop-sym (gensym "SUPER-VOP"))
         (vop-info-sym (gensym "VOP-INFO")))
    (setf (vop-info-name vop-info) name)
    (multiple-value-bind (body guard variant)
        (parse-define-vop vop-info inherited-vop specs
                          :compile-time t)
      #+sb-xc-host
      (setf (gethash name *backend-template-names*) vop-info)
      `(eval-when (:load-toplevel :execute)
         (/show0 "definining a VOP" ,name)
         (let* ((,super-vop-sym ,(and inherits
                                      `(template-or-lose ',inherits)))
                (,vop-info-sym ,(if inherits
                                    `(copy-vop-info ,super-vop-sym)
                                    `(make-vop-info))))
           (setf (vop-info-name ,vop-info-sym) ',name)
           (parse-define-vop ,vop-info-sym ,super-vop-sym ',specs)
           (setf (gethash ',name *backend-template-names*) ,vop-info-sym)
           ,@(when guard
               `((setf (vop-info-generator-function ,vop-info-sym)
                       ,guard)))
           ,@(when body
               `((setf (vop-info-generator-function ,vop-info-sym)
                       ,body)))
           ,@(when variant
               ;; variant needs to be evaluated
               `((setf (vop-info-variant ,vop-info-sym)
                       (list ,@variant))))
           ',name)))))

;;;; emission macros

;;; Return code to make a list of VOP arguments or results, linked by
;;; TN-REF-ACROSS. The first value is code, the second value is LET*
;;; forms, and the third value is a variable that evaluates to the
;;; head of the list, or NIL if there are no operands. Fixed is a list
;;; of forms that evaluate to TNs for the fixed operands. TN-REFS will
;;; be made for these operands according using the specified value of
;;; WRITE-P. More is an expression that evaluates to a list of TN-REFS
;;; that will be made the tail of the list. If it is constant NIL,
;;; then we don't bother to set the tail.
(defun make-operand-list (fixed more write-p)
  (collect ((forms)
            (binds))
    (let ((n-head nil)
          (n-prev nil))
      (dolist (op fixed)
        (let ((n-ref (gensym)))
          (binds `(,n-ref (reference-tn ,op ,write-p)))
          (if n-prev
              (forms `(setf (tn-ref-across ,n-prev) ,n-ref))
              (setq n-head n-ref))
          (setq n-prev n-ref)))

      (when more
        (let ((n-more (gensym)))
          (binds `(,n-more ,more))
          (if n-prev
              (forms `(setf (tn-ref-across ,n-prev) ,n-more))
              (setq n-head n-more))))

      (values (forms) (binds) n-head))))

;;; Emit-Template Node Block Template Args Results [Info]
;;;
;;; Call the emit function for TEMPLATE, linking the result in at the
;;; end of BLOCK.
(defmacro emit-template (node block template args results &optional info)
  (with-unique-names (first last)
    (once-only ((n-node node)
                (n-block block)
                (n-template template))
      `(multiple-value-bind (,first ,last)
           (emit-vop ,n-node ,n-block ,n-template ,args ,results
                     ,@(when info `(,info)))
         (insert-vop-sequence ,first ,last ,n-block nil)))))

;;; VOP Name Node Block Arg* Info* Result*
;;;
;;; Emit the VOP (or other template) NAME at the end of the IR2-BLOCK
;;; BLOCK, using NODE for the source context. The interpretation of
;;; the remaining arguments depends on the number of operands of
;;; various kinds that are declared in the template definition. VOP
;;; cannot be used for templates that have more-args or more-results,
;;; since the number of arguments and results is indeterminate for
;;; these templates. Use VOP* instead.
;;;
;;; ARGS and RESULTS are the TNs that are to be referenced by the
;;; template as arguments and results. If the template has
;;; codegen-info arguments, then the appropriate number of INFO forms
;;; following the arguments are used for codegen info.
(defmacro vop (name node block &rest operands)
  (let* ((vop-info (template-or-lose name))
         (arg-count (length (vop-info-args vop-info)))
         (result-count (length (vop-info-results vop-info)))
         (info-count (length (vop-info-info-args vop-info)))
         (noperands (+ arg-count result-count info-count))
         (n-node (gensym))
         (n-block (gensym))
         (n-template (gensym)))

    (when (or (vop-info-more-args vop-info) (vop-info-more-results vop-info))
      (error "cannot use VOP with variable operand count templates"))
    (unless (= noperands (length operands))
      (error "called with ~W operands, but was expecting ~W"
             (length operands) noperands))

    (multiple-value-bind (acode abinds n-args)
        (make-operand-list (subseq operands 0 arg-count) nil nil)
      (multiple-value-bind (rcode rbinds n-results)
          (make-operand-list (subseq operands (+ arg-count info-count)) nil t)

        (collect ((ibinds)
                  (ivars))
          (dolist (info (subseq operands arg-count (+ arg-count info-count)))
            (let ((temp (gensym)))
              (ibinds `(,temp ,info))
              (ivars temp)))

          `(let* ((,n-node ,node)
                  (,n-block ,block)
                  (,n-template (template-or-lose ',name))
                  ,@abinds
                  ,@(ibinds)
                  ,@rbinds)
             ,@acode
             ,@rcode
             (emit-template ,n-node ,n-block ,n-template ,n-args
                            ,n-results
                            ,@(when (ivars)
                                `((list ,@(ivars)))))
             (values)))))))

;;; VOP* Name Node Block (Arg* More-Args) (Result* More-Results) Info*
;;;
;;; This is like VOP, but allows for emission of templates with
;;; arbitrary numbers of arguments, and for emission of templates
;;; using already-created TN-REF lists.
;;;
;;; The ARGS and RESULTS are TNs to be referenced as the first
;;; arguments and results to the template. More-Args and More-Results
;;; are heads of TN-REF lists that are added onto the end of the
;;; TN-REFS for the explicitly supplied operand TNs. The TN-REFS for
;;; the more operands must have the TN and WRITE-P slots correctly
;;; initialized.
;;;
;;; As with VOP, the INFO forms are evaluated and passed as codegen
;;; info arguments.
(defmacro vop* (name node block args results &rest info)
  (declare (type cons args results))
  (let* ((vop-info (template-or-lose name))
         (arg-count (length (vop-info-args vop-info)))
         (result-count (length (vop-info-results vop-info)))
         (info-count (length (vop-info-info-args vop-info)))
         (fixed-args (butlast args))
         (fixed-results (butlast results))
         (n-node (gensym))
         (n-block (gensym))
         (n-template (gensym)))

    (unless (or (vop-info-more-args vop-info)
                (<= (length fixed-args) arg-count))
      (error "too many fixed arguments"))
    (unless (or (vop-info-more-results vop-info)
                (<= (length fixed-results) result-count))
      (error "too many fixed results"))
    (unless (= (length info) info-count)
      (error "expected ~W info args" info-count))

    (multiple-value-bind (acode abinds n-args)
        (make-operand-list fixed-args (car (last args)) nil)
      (multiple-value-bind (rcode rbinds n-results)
          (make-operand-list fixed-results (car (last results)) t)

        `(let* ((,n-node ,node)
                (,n-block ,block)
                (,n-template (template-or-lose ',name))
                ,@abinds
                ,@rbinds)
           ,@acode
           ,@rcode
           (emit-template ,n-node ,n-block ,n-template ,n-args ,n-results
                          ,@(when info
                              `((list ,@info))))
           (values))))))

;;;; miscellaneous macros

;;; SC-Case TN {({(SC-Name*) | SC-Name | T} Form*)}*
;;;
;;; Case off of TN's SC. The first clause containing TN's SC is
;;; evaluated, returning the values of the last form. A clause
;;; beginning with T specifies a default. If it appears, it must be
;;; last. If no default is specified, and no clause matches, then an
;;; error is signalled.
(def!macro sc-case (tn &body forms)
  (let ((n-sc (gensym))
        (n-tn (gensym)))
    (collect ((clauses))
      (do ((cases forms (rest cases)))
          ((null cases)
           (clauses `(t (error "unknown SC to SC-CASE for ~S:~%  ~S" ,n-tn
                               (sc-name (tn-sc ,n-tn))))))
        (let ((case (first cases)))
          (when (atom case)
            (error "illegal SC-CASE clause: ~S" case))
          (let ((head (first case)))
            (when (eq head t)
              (when (rest cases)
                (error "T case is not last in SC-CASE."))
              (clauses `(t nil ,@(rest case)))
              (return))
            (clauses `((or ,@(mapcar (lambda (x)
                                       `(eql ,(sc-number-or-lose x)
                                             ,n-sc))
                                     (if (atom head) (list head) head)))
                       nil ,@(rest case))))))

      `(let* ((,n-tn ,tn)
              (,n-sc (sc-number (tn-sc ,n-tn))))
         (cond ,@(clauses))))))

;;; Return true if TNs SC is any of the named SCs, false otherwise.
(defmacro sc-is (tn &rest scs)
  (once-only ((n-sc `(sc-number (tn-sc ,tn))))
    `(or ,@(mapcar (lambda (x)
                     `(eql ,n-sc ,(sc-number-or-lose x)))
                   scs))))

;;; Iterate over the IR2 blocks in component, in emission order.
(defmacro do-ir2-blocks ((block-var component &optional result)
                         &body forms)
  `(do ((,block-var (block-info (component-head ,component))
                    (ir2-block-next ,block-var)))
       ((null ,block-var) ,result)
     ,@forms))

;;; Iterate over all the TNs live at some point, with the live set
;;; represented by a local conflicts bit-vector and the IR2-BLOCK
;;; containing the location.
(defmacro do-live-tns ((tn-var live block &optional result) &body body)
  (with-unique-names (conf bod i ltns)
    (once-only ((n-live live)
                (n-block block))
      `(block nil
         (flet ((,bod (,tn-var) ,@body))
           ;; Do component-live TNs.
           (dolist (,tn-var (ir2-component-component-tns
                             (component-info
                              (block-component
                               (ir2-block-block ,n-block)))))
             (,bod ,tn-var))

           (let ((,ltns (ir2-block-local-tns ,n-block)))
             ;; Do TNs always-live in this block and live :MORE TNs.
             (do ((,conf (ir2-block-global-tns ,n-block)
                         (global-conflicts-next-blockwise ,conf)))
                 ((null ,conf))
               (when (or (eq (global-conflicts-kind ,conf) :live)
                         (let ((,i (global-conflicts-number ,conf)))
                           (and (eq (svref ,ltns ,i) :more)
                                (not (zerop (sbit ,n-live ,i))))))
                 (,bod (global-conflicts-tn ,conf))))
             ;; Do TNs locally live in the designated live set.
             (dotimes (,i (ir2-block-local-tn-count ,n-block) ,result)
               (unless (zerop (sbit ,n-live ,i))
                 (let ((,tn-var (svref ,ltns ,i)))
                   (when (and ,tn-var (not (eq ,tn-var :more)))
                     (,bod ,tn-var)))))))))))

;;; Iterate over all the IR2 blocks in PHYSENV, in emit order.
(defmacro do-physenv-ir2-blocks ((block-var physenv &optional result)
                                 &body body)
  (once-only ((n-physenv physenv))
    (once-only ((n-first `(lambda-block (physenv-lambda ,n-physenv))))
      (once-only ((n-tail `(block-info
                            (component-tail
                             (block-component ,n-first)))))
        `(do ((,block-var (block-info ,n-first)
                          (ir2-block-next ,block-var)))
             ((or (eq ,block-var ,n-tail)
                  (not (eq (ir2-block-physenv ,block-var) ,n-physenv)))
              ,result)
           ,@body)))))
