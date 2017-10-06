;;;; This file contains compiler code and compiler-related stuff which
;;;; can be built early on. Some of the stuff may be here because it's
;;;; needed early on, some other stuff (e.g. constants) just because
;;;; it might as well be done early so we don't have to think about
;;;; whether it's done early enough.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

;;; ANSI limits on compilation
(defconstant sb!xc:call-arguments-limit
  #!-64-bit sb!xc:most-positive-fixnum
  ;; x86-64 can save on REX prefixes
  #!+64-bit (ldb (byte (- 32 sb!vm:n-fixnum-tag-bits) 0) -1)
  "The exclusive upper bound on the number of arguments which may be passed
  to a function, including &REST args.")
(defconstant sb!xc:lambda-parameters-limit sb!xc:call-arguments-limit
  "The exclusive upper bound on the number of parameters which may be specified
  in a given lambda list. This is actually the limit on required and &OPTIONAL
  parameters. With &KEY and &AUX you can get more.")
(defconstant sb!xc:multiple-values-limit sb!xc:call-arguments-limit
  "The exclusive upper bound on the number of multiple VALUES that you can
  return.")

;;;; cross-compiler-only versions of CL special variables, so that we
;;;; don't have weird interactions with the host compiler

(defvar sb!xc:*compile-file-pathname*)
(defvar sb!xc:*compile-file-truename*)
(defvar sb!xc:*compile-print*)
(defvar sb!xc:*compile-verbose*)

;;;; miscellaneous types used both in the cross-compiler and on the target

;;;; FIXME: The INDEX and LAYOUT-DEPTHOID definitions probably belong
;;;; somewhere else, not "early-c", since they're after all not part
;;;; of the compiler.

;;; the type of LAYOUT-DEPTHOID slot values
(def!type layout-depthoid () '(or index (integer -1 -1)))
(def!type layout-bitmap ()
  ;; FIXME: Probably should exclude negative bignum
  #!+compact-instance-header 'integer
  #!-compact-instance-header '(and integer (not (eql 0))))

;;; An INLINEP value describes how a function is called. The values
;;; have these meanings:
;;;     NIL     No declaration seen: do whatever you feel like, but don't
;;;             dump an inline expansion.
;;; :NOTINLINE  NOTINLINE declaration seen: always do full function call.
;;;    :INLINE  INLINE declaration seen: save expansion, expanding to it
;;;             if policy favors.
;;; :MAYBE-INLINE
;;;             Retain expansion, but only use it opportunistically.
;;;             :MAYBE-INLINE is quite different from :INLINE. As explained
;;;             by APD on #lisp 2005-11-26: "MAYBE-INLINE lambda is
;;;             instantiated once per component, INLINE - for all
;;;             references (even under #'without FUNCALL)."
(deftype inlinep ()
  '(member :inline :maybe-inline :notinline nil))
(defconstant-eqx +inlinep-translations+
  '((inline . :inline)
    (notinline . :notinline)
    (maybe-inline . :maybe-inline))
  #'equal)

;;; *FREE-VARS* translates from the names of variables referenced
;;; globally to the LEAF structures for them. *FREE-FUNS* is like
;;; *FREE-VARS*, only it deals with function names.
(defvar *free-vars*)
(defvar *free-funs*)
(declaim (type hash-table *free-vars* *free-funs*))

;;; We use the same CONSTANT structure to represent all equal anonymous
;;; constants. This hashtable translates from constants to the LEAFs that
;;; represent them.
(defvar *constants*)
(declaim (type hash-table *constants*))

;;; *ALLOW-INSTRUMENTING* controls whether we should allow the
;;; insertion of instrumenting code (like a (CATCH ...)) around code
;;; to allow the debugger RETURN and STEP commands to function (we
;;; disallow it for internal stuff).
(defvar *allow-instrumenting*)

;;; miscellaneous forward declarations
(defvar *code-segment*)
;; FIXME: this is a kludge due to the absence of a 'vop' argument
;; to ALLOCATION-TRAMP in the x86-64 backend.
(defvar *code-is-immobile*)
#!+sb-dyncount (defvar *collect-dynamic-statistics*)
(defvar *component-being-compiled*)
(defvar *compiler-error-context*)
(defvar *compiler-error-count*)
(defvar *compiler-warning-count*)
(defvar *compiler-style-warning-count*)
(defvar *compiler-note-count*)
(defvar *compiler-trace-output*)
(defvar *constraint-universe*)
(defvar *current-path*)
(defvar *current-component*)
(defvar *delayed-ir1-transforms*)
(defvar *dynamic-counts-tn*)
(defvar *elsewhere*)
(defvar *elsewhere-label*)
(defvar *event-info*)
(defvar *event-note-threshold*)
(defvar *failure-p*)
(defvar *fixup-notes*)
#!+inline-constants
(progn
  (defvar *unboxed-constants*)
  (defstruct (unboxed-constants (:conc-name constant-)
                                (:predicate nil) (:copier nil))
    (table (make-hash-table :test #'equal) :read-only t)
    (segment
     (sb!assem:make-segment :type :elsewhere
                            :run-scheduler nil
                            :inst-hook (default-segment-inst-hook)
                            :alignment 0) :read-only t)
    (vector (make-array 16 :adjustable t :fill-pointer 0) :read-only t))
  (declaim (freeze-type unboxed-constants)))
(defvar *source-info*)
(defvar *source-plist*)
(defvar *source-namestring*)
(defvar *undefined-warnings*)
(defvar *warnings-p*)
(defvar *lambda-conversions*)
(defvar *compile-object* nil)

(defvar *stack-allocate-dynamic-extent* t
  "If true (the default), the compiler respects DYNAMIC-EXTENT declarations
and stack allocates otherwise inaccessible parts of the object whenever
possible. Potentially long (over one page in size) vectors are, however, not
stack allocated except in zero SAFETY code, as such a vector could overflow
the stack without triggering overflow protection.")

(!begin-collecting-cold-init-forms)
;;; This lock is seized in the compiler, and related areas -- like the
;;; classoid/layout/class system.
(defglobal **world-lock** nil)
#-sb-xc-host
(!cold-init-forms
 (setf **world-lock** (sb!thread:make-mutex :name "World Lock")))
(!defun-from-collected-cold-init-forms !world-lock-cold-init)

(defmacro with-world-lock (() &body body)
  `(sb!thread:with-recursive-lock (**world-lock**)
     ,@body))

(declaim (type fixnum *compiler-sset-counter*))
(defvar *compiler-sset-counter* 0)

;;; unique ID for the next object created (to let us track object
;;; identity even across GC, useful for understanding weird compiler
;;; bugs where something is supposed to be unique but is instead
;;; exists as duplicate objects)
#!+sb-show
(progn
  (defvar *object-id-counter* 0)
  (defun new-object-id ()
    (prog1
        *object-id-counter*
      (incf *object-id-counter*))))

;;;; miscellaneous utilities

;;; This is for "observers" who want to know if type names have been added.
;;; Rather than registering listeners, they can detect changes by comparing
;;; their stored nonce to the current nonce. Additionally the observers
;;; can detect whether function definitions have occurred.
(declaim (fixnum *type-cache-nonce*))
(!defglobal *type-cache-nonce* 0)

(def!struct (undefined-warning
            #-no-ansi-print-object
            (:print-object (lambda (x s)
                             (print-unreadable-object (x s :type t)
                               (prin1 (undefined-warning-name x) s))))
            (:copier nil))
  ;; the name of the unknown thing
  (name nil :type (or symbol list))
  ;; the kind of reference to NAME
  (kind (missing-arg) :type (member :function :type :variable))
  ;; the number of times this thing was used
  (count 0 :type unsigned-byte)
  ;; a list of COMPILER-ERROR-CONTEXT structures describing places
  ;; where this thing was used. Note that we only record the first
  ;; *UNDEFINED-WARNING-LIMIT* calls.
  (warnings () :type list))

;;; Delete any undefined warnings for NAME and KIND. This is for the
;;; benefit of the compiler, but it's sometimes called from stuff like
;;; type-defining code which isn't logically part of the compiler.
(declaim (ftype (function ((or symbol cons) keyword) (values))
                note-name-defined))
(defun note-name-defined (name kind)
  #-sb-xc-host (atomic-incf *type-cache-nonce*)
  ;; We do this BOUNDP check because this function can be called when
  ;; not in a compilation unit (as when loading top level forms).
  (when (boundp '*undefined-warnings*)
    (let ((name (uncross name)))
      (setq *undefined-warnings*
            (delete-if (lambda (x)
                         (and (equal (undefined-warning-name x) name)
                              (eq (undefined-warning-kind x) kind)))
                       *undefined-warnings*))))
  (values))

;;; to be called when a variable is lexically bound
(declaim (ftype (function (symbol) (values)) note-lexical-binding))
(defun note-lexical-binding (symbol)
    ;; This check is intended to protect us from getting silently
    ;; burned when we define
    ;;   foo.lisp:
    ;;     (DEFVAR *FOO* -3)
    ;;     (DEFUN FOO (X) (+ X *FOO*))
    ;;   bar.lisp:
    ;;     (DEFUN BAR (X)
    ;;       (LET ((*FOO* X))
    ;;         (FOO 14)))
    ;; and then we happen to compile bar.lisp before foo.lisp.
  (when (looks-like-name-of-special-var-p symbol)
    ;; FIXME: should be COMPILER-STYLE-WARNING?
    (style-warn 'asterisks-around-lexical-variable-name
                :format-control
                "using the lexical binding of the symbol ~
                 ~/sb-ext:print-symbol-with-prefix/, not the~@
                 dynamic binding"
                :format-arguments (list symbol)))
  (values))

(def!struct (debug-name-marker (:print-function print-debug-name-marker)
                               (:copier nil)))

(defvar *debug-name-level* 4)
(defvar *debug-name-length* 12)
(defvar *debug-name-punt*)
(defvar *debug-name-sharp*)
(defvar *debug-name-ellipsis*)

(defmethod make-load-form ((marker debug-name-marker) &optional env)
  (declare (ignore env))
  (cond ((eq marker *debug-name-sharp*)
         `(if (boundp '*debug-name-sharp*)
              *debug-name-sharp*
              (make-debug-name-marker)))
        ((eq marker *debug-name-ellipsis*)
         `(if (boundp '*debug-name-ellipsis*)
              *debug-name-ellipsis*
              (make-debug-name-marker)))
        (t
         (warn "Dumping unknown debug-name marker.")
         '(make-debug-name-marker))))

(defun print-debug-name-marker (marker stream level)
  (declare (ignore level))
  (cond ((eq marker *debug-name-sharp*)
         (write-char #\# stream))
        ((eq marker *debug-name-ellipsis*)
         (write-string "..." stream))
        (t
         (write-string "???" stream))))

(setf *debug-name-sharp* (make-debug-name-marker)
      *debug-name-ellipsis* (make-debug-name-marker))

(declaim (ftype (sfunction () list) name-context))
(defun debug-name (type thing &optional context)
  (let ((*debug-name-punt* nil))
    (labels ((walk (x)
               (typecase x
                 (cons
                  (if (plusp *debug-name-level*)
                      (let ((*debug-name-level* (1- *debug-name-level*)))
                        (do ((tail (cdr x) (cdr tail))
                             (name (cons (walk (car x)) nil)
                                   (cons (walk (car tail)) name))
                             (n (1- *debug-name-length*) (1- n)))
                            ((or (not (consp tail))
                                 (not (plusp n))
                                 *debug-name-punt*)
                             (cond (*debug-name-punt*
                                    (setf *debug-name-punt* nil)
                                    (nreverse name))
                                   ((atom tail)
                                    (nconc (nreverse name) (walk tail)))
                                   (t
                                    (setf *debug-name-punt* t)
                                    (nconc (nreverse name) (list *debug-name-ellipsis*)))))))
                      *debug-name-sharp*))
                 ((or symbol number string)
                  x)
                 (t
                  (type-of x)))))
      (let ((name (list* type (walk thing) (when context (name-context)))))
        (when (legal-fun-name-p name)
          (bug "~S is a legal function name, and cannot be used as a ~
                debug name." name))
        name))))

;;; Set this to NIL to inhibit assembly-level optimization. (For
;;; compiler debugging, rather than policy control.)
(defvar *assembly-optimize* t)

(in-package "SB!ALIEN")

;;; Information describing a heap-allocated alien.
(def!struct (heap-alien-info (:copier nil))
  ;; The type of this alien.
  (type (missing-arg) :type alien-type)
  ;; Its name.
  (alien-name (missing-arg) :type simple-string)
  ;; Data or code?
  (datap (missing-arg) :type boolean))
(!set-load-form-method heap-alien-info (:xc :target))
