;;;; Type checking of higher order function.
;;;;
;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

(defun assert-callable-args (name call)
  (map-callable-arguments
   (lambda (&rest args)
     (apply #'assert-callable-arg name args))
   call))

(defun assert-callable-arg (caller lvar args results &key &allow-other-keys)
  (when args
    (multiple-value-bind (arg-specs result-specs deps)
        (callable-dependant-lvars args results)
      (assert-function-designator-lvar-type lvar
                                            (make-fun-type
                                             :required
                                             (if arg-specs
                                                 (make-list (length args)
                                                            :initial-element *universal-type*)
                                                 args)
                                             :returns (if (ctype-p results)
                                                          results
                                                          *wild-type*)
                                             :designator t)
                                            caller deps arg-specs result-specs))))

(defun callable-dependant-lvars (args results)
  (collect ((lvars))
    (let ((arg-position -1))
      (labels ((process-arg (arg)
                 (destructuring-bind (lvar . options) arg
                   (lvars lvar)
                   (list*
                    (incf arg-position)
                    (loop for (key value) on options by #'cddr
                          collect key
                          collect (cond ((lvar-p value)
                                         (lvars value)
                                         (incf arg-position))
                                        (t
                                         value))))))
               (process-args (args)
                 (loop for arg in args
                       when (consp arg)
                       collect
                       (if (eq (car arg) 'or)
                           (cons 'or (mapcar #'process-arg (cdr arg)))
                           (process-arg arg)))))
        (values (process-args args)
                (and (consp results)
                     (process-arg results))
                (lvars))))))

(defun insert-function-designator-cast-before (next lvar type caller
                                               deps arg-specs result-specs)
  (declare (type node next) (type lvar lvar) (type ctype type))
  (with-ir1-environment-from-node next
    (let* ((ctran (node-prev next))
           (cast (make-function-designator-cast :asserted-type type
                                                :type-to-check (specifier-type 'function-designator)
                                                :value lvar
                                                :derived-type (coerce-to-values type)
                                                :deps deps
                                                :arg-specs arg-specs
                                                :result-specs result-specs
                                                :caller caller))
           (internal-ctran (make-ctran)))
      (loop for lvar in deps
            do (push cast (lvar-dependent-casts lvar)))
      (setf (ctran-next ctran) cast
            (node-prev cast) ctran)
      (use-ctran cast internal-ctran)
      (link-node-to-previous-ctran next internal-ctran)
      (setf (lvar-dest lvar) cast)
      (reoptimize-lvar lvar)
      (when (return-p next)
        (node-ends-block cast))
      (setf (block-type-check (node-block cast)) t)
      cast)))

;;; Similar to assert-lvar-type
(defun assert-function-designator-lvar-type (lvar type caller
                                             deps arg-specs result-specs)
  (declare (type lvar lvar) (type ctype type))
  (let ((internal-lvar (make-lvar))
        (dest (lvar-dest lvar)))
    (substitute-lvar internal-lvar lvar)
    (let ((cast (insert-function-designator-cast-before dest lvar type caller
                                                        deps arg-specs result-specs)))
      (use-lvar cast internal-lvar))))

(defun map-key-lvars (function args type)
  (when (fun-type-keyp type)
    (do* ((non-key (+ (length (fun-type-required type))
                      (length (fun-type-optional type))))
          unknown
          (key (nthcdr non-key args) (cddr key)))
         ((null key) unknown)
      (let ((key (first key))
            (value (second key)))
        (if (constant-lvar-p key)
            (let* ((name (lvar-value key))
                   (info (find name (fun-type-keywords type)
                               :key #'key-info-name)))
              (when info
                (funcall function name value)))
            (setf unknown t))))))

;;; Turn constant LVARs in keyword arg positions to constants so that
;;; they can be passed to FUN-INFO-CALLABLE-CHECK.
(defun resolve-key-args (args type)
  (if (fun-type-keyp type)
      (let* ((non-key (+ (length (fun-type-required type))
                         (length (fun-type-optional type))))
             key-arguments
             (unknown (map-key-lvars (lambda (key value)
                                       (push key key-arguments)
                                       (push value key-arguments))
                                     args
                                     type)))
        (values (nconc (subseq args 0 non-key)
                       (nreverse key-arguments))
                unknown))
      (values args nil)))

;;; The function should accept
;;; (lvar argument-description result-description
;;;       &key (no-function-conversion boolean) (arg-lvars list-of-lvars))
(defun map-callable-arguments (function combination)
  (let* ((comination-name (lvar-fun-name (combination-fun combination) t))
         (type (info :function :type comination-name))
         (info (info :function :info comination-name)))
    (when (fun-info-callable-map info)
      (multiple-value-bind (arg-lvars unknown) (resolve-key-args (combination-args combination) type)
        (apply (fun-info-callable-map info)
               (lambda (lvar args results &rest rest)
                 (apply function lvar args results
                        :arg-lvars arg-lvars
                        :unknown-keys unknown
                        rest))
               arg-lvars)))))

(defun lvar-fun-type (lvar)
  ;; Handle #'function,  'function and (lambda (x y))
  (let* ((use (principal-lvar-use lvar))
         (lvar-type (lvar-type lvar))
         (leaf (if (ref-p use)
                   (ref-leaf use)
                   (return-from lvar-fun-type lvar-type)))
         (defined-type (and (global-var-p leaf)
                            (case (global-var-where-from leaf)
                              (:declared
                               (global-var-type leaf))
                              ((:defined :defined-here)
                               (if (and (defined-fun-p leaf)
                                        (eq (defined-fun-inlinep leaf) :notinline))
                                   lvar-type
                                   (proclaimed-ftype (global-var-%source-name leaf))))
                              (t
                               (global-var-defined-type leaf)))))
         (lvar-type (if (and defined-type
                             (neq defined-type *universal-type*))
                        defined-type
                        lvar-type))
         (fun-name (cond ((or (fun-type-p lvar-type)
                              (functional-p leaf))
                          (cond ((constant-lvar-p lvar)
                                 #+sb-xc-host (bug "Can't call %FUN-NAME")
                                 #-sb-xc-host (%fun-name (lvar-value lvar)))
                                ((and (lambda-p leaf)
                                      (eq (lambda-kind leaf) :external))
                                 (leaf-debug-name (lambda-entry-fun leaf)))
                                (t
                                 (leaf-debug-name leaf))))
                         ((constant-lvar-p lvar)
                          (lvar-value lvar))
                         (t
                          (return-from lvar-fun-type lvar-type))))
         (type (cond ((fun-type-p lvar-type)
                      lvar-type)
                     ((symbolp fun-name)
                      (proclaimed-ftype fun-name))
                     ((functional-p leaf)
                      (let ((info (functional-info leaf)))
                        (if info
                            (specifier-type (entry-info-type info))
                            lvar-type)))
                     (t
                      lvar-type))))
    (values type fun-name leaf)))

(defun callable-argument-lossage-kind (fun-name leaf soft hard)
  (if (and (neq (leaf-where-from leaf) :defined-here)
           (not (and (functional-p leaf)
                     (or (lambda-p leaf)
                         (member (functional-kind leaf)
                                 '(:toplevel-xep)))))
           (or (not fun-name)
               (not (info :function :info fun-name))))
      soft
      hard))

(defun validate-test-and-test-not (combination)
  (let* ((comination-name (lvar-fun-name (combination-fun combination) t))
         (info (info :function :info comination-name)))
    (when (and info
               (ir1-attributep (fun-info-attributes info) call))
      (let (test
            test-not
            (null-type (specifier-type 'null)))
        (map-key-lvars (lambda (key value)
                         (when (and (not test)
                                    (eq key :test))
                           (setf test value))
                         (when (and (not test-not)
                                    (eq key :test-not))
                           (setf test-not value)))
                       (combination-args combination)
                       (info :function :type comination-name))
        (when (and test
                   test-not
                   (eq (type-intersection null-type (lvar-type test))
                       *empty-type*)
                   (eq (type-intersection null-type (lvar-type test-not))
                       *empty-type*))
          (note-lossage "~s: can't specify both :TEST and :TEST-NOT"
                        comination-name))))))

(defun function-designator-cast-types (cast)
  (labels ((arg-type (arg)
             (if (lvar-p arg)
                 (lvar-type arg)
                 (leaf-type arg)))
           (sequence-element-type (lvar)
             (let ((type (arg-type lvar)))
               (cond ((array-type-p type)
                      (let ((elt-type (array-type-element-type type)))
                        (if (eq elt-type *wild-type*)
                            *universal-type*
                            elt-type)))
                     ((csubtypep type (specifier-type 'string))
                      (specifier-type 'character))
                     (t
                      *universal-type*)))))
    (let ((deps (function-designator-cast-deps cast))
          (arg-specs (function-designator-cast-arg-specs cast))
          (result-specs (function-designator-cast-result-specs cast)))
      (labels ((%process-arg (spec)
                 (destructuring-bind (nth-arg . options) spec
                   (let* ((arg (nth nth-arg deps))
                          (key-nth (getf options :key))
                          (key (and key-nth (nth key-nth deps)))
                          (key-return-type (and key
                                                (multiple-value-bind (type name) (lvar-fun-type key)
                                                  (cond ((eq name 'identity)
                                                         nil)
                                                        ((fun-type-p type)
                                                         (single-value-type (fun-type-returns type)))
                                                        (t
                                                         *universal-type*))))))
                     (cond (key-return-type)
                           ((getf options :sequence)
                            (sequence-element-type arg))
                           (t
                            (arg-type arg))))))
               (process-arg (spec)
                 (if (eq (car spec) 'or)
                     (cons 'or (mapcar #'%process-arg (cdr spec)))
                     (%process-arg spec))))
        (values
         (if arg-specs
             (mapcar #'process-arg arg-specs)
             (fun-type-required
              (cast-asserted-type cast)))
         (if result-specs
             (process-arg result-specs)
             (fun-type-returns (cast-asserted-type cast))))))))

(defun update-function-designator-cast (cast)
  (when (function-designator-cast-deps cast)
    (multiple-value-bind (args results)
        (function-designator-cast-types cast)
      (flet ((process-or (specs)
               (loop for spec in specs
                     collect (if (typep spec '(cons (eql or)))
                                 (sb!kernel::%type-union (cdr spec))
                                 spec))))
        (setf (cast-asserted-type cast)
              (make-fun-type
               :required (process-or args)
               :returns results
               :designator t))))))

;;; Return MIN, MAX, whether it contaions &optional/&key/&rest
(defun fun-type-arg-limits (type)
  (if (fun-type-wild-args type)
      (values nil nil)
      (let* ((min (length (fun-type-required type)))
             (max (and (not (or (fun-type-rest type)
                                (fun-type-keyp type)))
                       (+ min
                          (length (fun-type-optional type))))))
        (values min max (or (fun-type-rest type)
                            (fun-type-keyp type)
                            (fun-type-optional type))))))

;;; Should have enough types for N 
(defun fun-type-n-arg-types (n type)
  (let (result)
    (flet ((pick (types)
             (loop for type in types
                   do (push type result)
                   while (plusp (decf n)))))
      (pick (fun-type-required type))
      (pick (fun-type-optional type))
      (loop repeat n
            with rest = (or (fun-type-rest type)
                            *universal-type*)
            do (push rest result)))
    (nreverse result)))

(defun report-arg-count-mismatch (callee caller type arg-count
                                  condition-type)
  (multiple-value-bind (min max optional) (fun-type-arg-limits type)
    (cond
      ((and (not min) (not max))
       nil)
      ((not optional)
       (when (/= arg-count min)
         (warn condition-type
               :format-control
               "The function ~S is called by ~S with ~R argument~:P, but wants exactly ~R."
               :format-arguments
               (list
                callee
                caller
                arg-count min))
         t))
      ((< arg-count min)
       (warn condition-type
             :format-control
             "The function ~S is called by ~S with ~R argument~:P, but wants at least ~R."
             :format-control
             (list
              callee
              caller
              arg-count min))
       t)
      ((not max)
       nil)
      ((> arg-count max)
       (warn condition-type
             :format-control
             "The function ~S called by ~S with ~R argument~:P, but wants at most ~R."
             :format-control
             (list
              callee
              caller
              arg-count max))
       t))))

;;; This can provide better errors and better handle OR types than a
;;; simple type intersection.
(defun check-function-designator-cast (cast)
  (multiple-value-bind (type name leaf) (lvar-fun-type (cast-value cast))
    (when (and (fun-type-p type)
               leaf)
      (multiple-value-bind (args results)
          (function-designator-cast-types cast)
        (let* ((condition (callable-argument-lossage-kind name
                                                          leaf
                                                          'simple-style-warning
                                                          'simple-warning))
               (type-condition (case condition
                                 (simple-style-warning
                                  'type-style-warning)
                                 (t
                                  'type-warning)))
               (caller (function-designator-cast-caller cast))
               (arg-count (length args)))
          (or (report-arg-count-mismatch name caller
                                         type
                                         arg-count
                                         condition)
              (let ((param-types (fun-type-n-arg-types arg-count type)))
                (block nil
                  ;; Need to check each OR seperately, a UNION could
                  ;; intersect with the function parameters
                  (labels ((hide-ors (current-or or-part)
                             (loop for spec in args
                                   collect (cond ((eq spec current-or)
                                                  or-part)
                                                 ((typep spec '(cons (eql or)))
                                                  (sb!kernel::%type-union (cdr spec)))
                                                 (t
                                                  spec))))
                           (check (arg param &optional
                                               current-spec)
                             (when (eq (type-intersection param arg) *empty-type*)
                               (warn type-condition
                                     :format-control
                                     "The function ~S is called by ~S with ~S but it accepts ~S."
                                     :format-arguments
                                     (list
                                      name
                                      caller
                                      (mapcar #'type-specifier (hide-ors current-spec arg))
                                      (mapcar #'type-specifier param-types)))
                               (return t))))
                    (loop for arg-type in args
                          for param-type in param-types
                          if (typep arg-type '(cons (eql or)))
                          do (loop for type in (cdr arg-type)
                                   do (check type param-type arg-type))
                          else do (check arg-type param-type)))))
              (let ((returns (single-value-type (fun-type-returns type))))
                (when (and (neq returns *wild-type*)
                           (neq results *wild-type*)
                           (eq (type-intersection returns results) *empty-type*))
                  (warn type-condition
                        :format-control
                        "The function ~S called by ~S returns ~S but ~S is expected"
                        :format-arguments
                        (list
                         name
                         caller
                         (type-specifier returns)
                         (type-specifier results)))))))))))

;;; Doing this during IR2 conversion and not in ir1-optimize-cast
;;; because of possible function redefinition and the need to signal a
;;; style-warning and not a full warning.
;;; If the cast is not deleted after a warning is signalled then it
;;; might get signalled multiple times, and IR2 conversion happens
;;; only once.
(defun check-functional-cast (cast)
  (let ((value (cast-value cast))
        (atype (cast-asserted-type cast)))
    (cond ((function-designator-cast-p cast)
           (check-function-designator-cast cast))
          ((fun-type-p atype)
           (multiple-value-bind (type name leaf) (lvar-fun-type value)
             (when (and (fun-type-p type)
                        leaf)
               (let ((int (type-intersection type atype)))
                 (when (or (memq *empty-type* (fun-type-required int))
                           (and (eq (fun-type-returns int) *empty-type*)
                                (neq (fun-type-returns type) *empty-type*)
                                (not (and (eq (fun-type-returns atype) *empty-type*)
                                          (eq (fun-type-returns type) *wild-type*)))))
                   (%compile-time-type-error-warn cast
                                                  (type-specifier atype)
                                                  (type-specifier type)
                                                  (list name)
                                                  :condition
                                                  (callable-argument-lossage-kind name
                                                                                  leaf
                                                                                  'type-style-warning
                                                                                  'type-warning))))))))))
