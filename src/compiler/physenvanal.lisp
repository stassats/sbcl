;;;; This file implements the environment analysis phase for the
;;;; compiler. This phase annotates IR1 with a hierarchy environment
;;;; structures, determining the physical environment that each LAMBDA
;;;; allocates its variables and finding what values are closed over
;;;; by each physical environment.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB-C")

;;; Do environment analysis on the code in COMPONENT. This involves
;;; various things:
;;;  1. Make a PHYSENV structure for each non-LET LAMBDA, assigning
;;;     the LAMBDA-PHYSENV for all LAMBDAs.
;;;  2. Find all values that need to be closed over by each
;;;     physical environment.
;;;  3. Scan the blocks in the component closing over non-local-exit
;;;     continuations.
;;;  4. Delete all non-top-level functions with no references. This
;;;     should only get functions with non-NULL kinds, since normal
;;;     functions are deleted when their references go to zero.
(defun physenv-analyze (component)
  (declare (type component component))
  (aver (every (lambda (x)
                 (eq (functional-kind x) :deleted))
               (component-new-functionals component)))
  (setf (component-new-functionals component) ())
  (mapc #'add-lambda-vars-and-let-vars-to-closures
        (component-lambdas component))

  (find-non-local-exits component)
  (recheck-dynamic-extent-lvars component)
  (find-cleanup-points component)
  (tail-annotate component)
  (analyze-indirect-lambda-vars component)

  (dolist (fun (component-lambdas component))
    (when (null (leaf-refs fun))
      (let ((kind (functional-kind fun)))
        (unless (or (eq kind :toplevel)
                    (functional-has-external-references-p fun))
          (aver (member kind '(:optional :cleanup :escape)))
          (setf (functional-kind fun) nil)
          (delete-functional fun)))))

  (setf (component-nlx-info-generated-p component) t)
  (values))

;;; If CLAMBDA has a PHYSENV, return it, otherwise assign an empty one
;;; and return that.
(defun get-lambda-physenv (clambda)
  (declare (type clambda clambda))
  (let ((homefun (lambda-home clambda)))
    (or (lambda-physenv homefun)
        (let ((res (make-physenv :lambda homefun)))
          (setf (lambda-physenv homefun) res)
          ;; All the LETLAMBDAs belong to HOMEFUN, and share the same
          ;; PHYSENV. Thus, (1) since HOMEFUN's PHYSENV was NIL,
          ;; theirs should be NIL too, and (2) since we're modifying
          ;; HOMEFUN's PHYSENV, we should modify theirs, too.
          (dolist (letlambda (lambda-lets homefun))
            (aver (eql (lambda-home letlambda) homefun))
            (aver (null (lambda-physenv letlambda)))
            (setf (lambda-physenv letlambda) res))
          res))))

;;; Get NODE's environment, assigning one if necessary.
(defun get-node-physenv (node)
  (declare (type node node))
  (get-lambda-physenv (node-home-lambda node)))

;;; private guts of ADD-LAMBDA-VARS-AND-LET-VARS-TO-CLOSURES
;;;
;;; This is the old CMU CL COMPUTE-CLOSURE, which only works on
;;; LAMBDA-VARS directly, not on the LAMBDA-VARS of LAMBDA-LETS. It
;;; seems never to be valid to use this operation alone, so in SBCL,
;;; it's private, and the public interface,
;;; ADD-LAMBDA-VARS-AND-LET-VARS-TO-CLOSURES, always runs over all the
;;; variables, not only the LAMBDA-VARS of CLAMBDA itself but also
;;; the LAMBDA-VARS of CLAMBDA's LAMBDA-LETS.
(defun %add-lambda-vars-to-closures (clambda)
  (let ((physenv (get-lambda-physenv clambda))
        (did-something nil))
    (note-unreferenced-fun-vars clambda)
    (dolist (var (lambda-vars clambda))
      (dolist (ref (leaf-refs var))
        (let ((ref-physenv (get-node-physenv ref)))
          (unless (eq ref-physenv physenv)
            (when (lambda-var-sets var)
              (setf (lambda-var-indirect var) t))
            (setq did-something t)
            (close-over var ref-physenv physenv))))
      (dolist (set (basic-var-sets var))

        ;; Variables which are set but never referenced can be
        ;; optimized away, and closing over them here would just
        ;; interfere with that. (In bug 147, it *did* interfere with
        ;; that, causing confusion later. This UNLESS solves that
        ;; problem, but I (WHN) am not 100% sure it's best to solve
        ;; the problem this way instead of somehow solving it
        ;; somewhere upstream and just doing (AVER (LEAF-REFS VAR))
        ;; here.)
        (unless (null (leaf-refs var))

          (let ((set-physenv (get-node-physenv set)))
            (unless (eq set-physenv physenv)
              (setf did-something t
                    (lambda-var-indirect var) t)
              (close-over var set-physenv physenv))))))
    did-something))

;;; Find any variables in CLAMBDA -- either directly in LAMBDA-VARS or
;;; in the LAMBDA-VARS of elements of LAMBDA-LETS -- with references
;;; outside of the home environment and close over them. If a
;;; closed-over variable is set, then we set the INDIRECT flag so that
;;; we will know the closed over value is really a pointer to the
;;; value cell. We also warn about unreferenced variables here, just
;;; because it's a convenient place to do it. We return true if we
;;; close over anything.
(defun add-lambda-vars-and-let-vars-to-closures (clambda)
  (declare (type clambda clambda))
  (let ((did-something nil))
    (when (%add-lambda-vars-to-closures clambda)
      (setf did-something t))
    (dolist (lambda-let (lambda-lets clambda))
      ;; There's no need to recurse through full COMPUTE-CLOSURE
      ;; here, since LETS only go one layer deep.
      (aver (null (lambda-lets lambda-let)))
      (when (%add-lambda-vars-to-closures lambda-let)
        (setf did-something t)))
    did-something))

(defun xep-allocator (xep)
  (let ((entry (functional-entry-fun xep)))
    (functional-allocator entry)))

;;; Make sure that THING is closed over in REF-PHYSENV and in all
;;; PHYSENVs for the functions that reference REF-PHYSENV's function
;;; (not just calls). HOME-PHYSENV is THING's home environment. When we
;;; reach the home environment, we stop propagating the closure.
(defun close-over (thing ref-physenv home-physenv)
  (declare (type physenv ref-physenv home-physenv))
  (let ((flooded-physenvs nil))
    (labels ((flood (flooded-physenv)
               (unless (or (eql flooded-physenv home-physenv)
                           (member flooded-physenv flooded-physenvs))
                 (push flooded-physenv flooded-physenvs)
                 (unless (memq thing (physenv-closure flooded-physenv))
                   (push thing (physenv-closure flooded-physenv))
                   (let ((lambda (physenv-lambda flooded-physenv)))
                     (cond ((eq (functional-kind lambda) :external)
                            (let* ((alloc-node (xep-allocator lambda))
                                   (alloc-lambda (node-home-lambda alloc-node))
                                   (alloc-physenv (get-lambda-physenv alloc-lambda)))
                              (flood alloc-physenv)
                              (dolist (ref (leaf-refs lambda))
                                (close-over lambda
                                            (get-node-physenv ref) alloc-physenv))))
                           (t (dolist (ref (leaf-refs lambda))
                                ;; FIXME: This assertion looks
                                ;; reasonable, but does not work for
                                ;; :CLEANUPs.
                                #+nil
                                (let ((dest (node-dest ref)))
                                  (aver (basic-combination-p dest))
                                  (aver (eq (basic-combination-kind dest) :local)))
                                (flood (get-node-physenv ref))))))))))
      (flood ref-physenv)))
  (values))

;;; Find LAMBDA-VARs that are marked as needing to support indirect
;;; access (SET at some point after initial creation) that are present
;;; in CLAMBDAs not marked as being DYNAMIC-EXTENT (meaning that the
;;; value-cell involved must be able to survive past the extent of the
;;; allocating frame), and mark them (the LAMBDA-VARs) as needing
;;; explicit value-cells.  Because they are already closed-over, the
;;; LAMBDA-VARs already appear in the closures of all of the CLAMBDAs
;;; that need checking.
(defun analyze-indirect-lambda-vars (component)
  (dolist (fun (component-lambdas component))
    (let ((entry-fun (functional-entry-fun fun)))
      ;; We also check the ENTRY-FUN, as XEPs for LABELS or FLET
      ;; functions aren't set to be DX even if their underlying
      ;; CLAMBDAs are, and if we ever get LET-bound anonymous function
      ;; DX working, it would mark the XEP as being DX but not the
      ;; "real" CLAMBDA.  This works because a FUNCTIONAL-ENTRY-FUN is
      ;; either NULL, a self-pointer (for :TOPLEVEL functions), a
      ;; pointer from an XEP to its underlying function (for :EXTERNAL
      ;; functions), or a pointer from an underlying function to its
      ;; XEP (for non-:TOPLEVEL functions with XEPs).
      (unless (or (leaf-dynamic-extent fun)
                  ;; Functions without XEPs can be treated as if they
                  ;; are DYNAMIC-EXTENT, even without being so
                  ;; declared, as any escaping closure which /isn't/
                  ;; DYNAMIC-EXTENT but calls one of these functions
                  ;; will also close over the required variables, thus
                  ;; forcing the allocation of value cells.  Since the
                  ;; XEP is stored in the ENTRY-FUN slot, we can pick
                  ;; off the non-XEP case here.
                  (not entry-fun)
                  (leaf-dynamic-extent entry-fun))
        (let ((closure (physenv-closure (lambda-physenv fun))))
          (dolist (var closure)
            (when (and (lambda-var-p var)
                       (lambda-var-indirect var))
              (setf (lambda-var-explicit-value-cell var) t))))))))

;;;; non-local exit

(defvar *functional-escape-info*)

(defun functional-may-escape-p (functional)
  (binding* ((functional (if (lambda-p functional)
                             (lambda-home functional)
                             functional))
             (table (or *functional-escape-info*
                        ;; Many components have no escapes, so we
                        ;; allocate it lazily.
                        (setf *functional-escape-info*
                              (make-hash-table :test #'eq))))
             ((bool ok) (gethash functional table)))
    (if ok
        bool
        (let ((entry (functional-entry-fun functional)))
          ;; First stick a NIL in there: break cycles.
          (setf (gethash functional table) nil)
          ;; Then compute the real value.
          (setf (gethash functional table)
                (and
                 ;; ESCAPE functionals would never escape from their target
                 (neq (functional-kind functional) :escape)
                 (or
                  ;; If the functional has a XEP, it's kind is :EXTERNAL --
                  ;; which means it may escape. ...but if it
                  ;; HAS-EXTERNAL-REFERENCES-P, then that XEP is actually a
                  ;; TL-XEP, which means it's a toplevel function -- which in
                  ;; turn means our search has bottomed out without an escape
                  ;; path. AVER just to make sure, though.
                  (and (eq :external (functional-kind functional))
                       (if (functional-has-external-references-p functional)
                           (aver (eq 'tl-xep (car (functional-debug-name functional))))
                           t))
                  ;; If it has an entry point that may escape, that just as bad.
                  (and entry (functional-may-escape-p entry))
                  ;; If it has references to it in functions that may escape, that's bad
                  ;; too.
                  (dolist (ref (functional-refs functional) nil)
                    (binding* ((lvar (ref-lvar ref) :exit-if-null)
                               (dest (lvar-dest lvar) :exit-if-null))
                      (when (functional-may-escape-p (node-home-lambda dest))
                        (return t)))))))))))

(defun exit-should-check-tag-p (exit)
  (declare (type exit exit))
  (let ((exit-lambda (lexenv-lambda (node-lexenv exit))))
    (unless (or
             ;; Unsafe but fast...
             (policy exit (zerop check-tag-existence))
             ;; Dynamic extent is a promise things won't escape --
             ;; and an explicit request to avoid heap consing.
             (member (lambda-extent exit-lambda) '(truly-dynamic-extent dynamic-extent))
             ;; If the exit lambda cannot escape, then we should be safe.
             ;; ...since the escape analysis is kinda new, and not particularly
             ;; exhaustively tested, let alone proven, disable it for SAFETY 3.
             (and (policy exit (< safety 3))
                  (not (functional-may-escape-p exit-lambda))))
      (when (policy exit (> speed safety))
        (let ((*compiler-error-context* (exit-entry exit)))
          (compiler-notify "~@<Allocating a value-cell at runtime for ~
                            checking possibly out of extent exit via ~S. Use ~
                            GO/RETURN-FROM with SAFETY 0, or declare the exit ~
                            function DYNAMIC-EXTENT to avoid.~:@>"
                           (node-source-form exit))))
      t)))

;;; Insert the entry stub before the original exit target, and add a
;;; new entry to the PHYSENV-NLX-INFO. The %NLX-ENTRY call in the
;;; stub is passed the NLX-INFO as an argument so that the back end
;;; knows what entry is being done.
;;;
;;; The link from the EXIT block to the entry stub is changed to be a
;;; link from the component head. Similarly, the EXIT block is linked
;;; to the component tail. This leaves the entry stub reachable, but
;;; makes the flow graph less confusing to flow analysis.
;;;
;;; If a CATCH or an UNWIND-protect, then we set the LEXENV for the
;;; last node in the cleanup code to be the enclosing environment, to
;;; represent the fact that the binding was undone as a side effect of
;;; the exit. This will cause a lexical exit to be broken up if we are
;;; actually exiting the scope (i.e. a BLOCK), and will also do any
;;; other cleanups that may have to be done on the way.
(defun insert-nlx-entry-stub (exit env)
  (declare (type physenv env) (type exit exit))
  (let* ((exit-block (node-block exit))
         (next-block (first (block-succ exit-block)))
         (entry (exit-entry exit))
         (cleanup (entry-cleanup entry))
         (info (make-nlx-info cleanup exit))
         (new-block (insert-cleanup-code (list exit-block) next-block
                                         entry
                                         `(%nlx-entry ,(opaquely-quote info))
                                         cleanup))
         (component (block-component new-block)))
    (unlink-blocks exit-block new-block)
    (link-blocks exit-block (component-tail component))
    (link-blocks (component-head component) new-block)

    (setf (exit-nlx-info exit) info)
    (setf (nlx-info-target info) new-block)
    (setf (nlx-info-safe-p info) (exit-should-check-tag-p exit))
    (push info (physenv-nlx-info env))
    (push info (cleanup-info cleanup))
    (when (member (cleanup-kind cleanup) '(:catch :unwind-protect))
      (setf (node-lexenv (block-last new-block))
            (node-lexenv entry))))

  (values))

;;; Do stuff necessary to represent a non-local exit from the node
;;; EXIT into ENV. This is called for each non-local exit node, of
;;; which there may be several per exit continuation. This is what we
;;; do:
;;; -- If there isn't any NLX-INFO entry in the environment, make
;;;    an entry stub, otherwise just move the exit block link to
;;;    the component tail.
;;; -- Close over the NLX-INFO in the exit environment.
;;; -- If the exit is from an :ESCAPE function, then substitute a
;;;    constant reference to NLX-INFO structure for the escape
;;;    function reference. This will cause the escape function to
;;;    be deleted (although not removed from the DFO.)  The escape
;;;    function is no longer needed, and we don't want to emit code
;;;    for it.
;;; -- Change the %NLX-ENTRY call to use the NLX lvar so that 1) there
;;;    will be a use to represent the NLX use; 2) make life easier for
;;;    the stack analysis.
(defun note-non-local-exit (env exit)
  (declare (type physenv env) (type exit exit))
  (let ((lvar (node-lvar exit))
        (exit-fun (node-home-lambda exit))
        (info (find-nlx-info exit)))
    (cond (info
           (let ((block (node-block exit)))
             (aver (= (length (block-succ block)) 1))
             (unlink-blocks block (first (block-succ block)))
             (link-blocks block (component-tail (block-component block)))
             (setf (exit-nlx-info exit) info)
             (unless (nlx-info-safe-p info)
               (setf (nlx-info-safe-p info)
                     (exit-should-check-tag-p exit)))))
          (t
           (insert-nlx-entry-stub exit env)
           (setq info (exit-nlx-info exit))
           (aver info)))
    (close-over info (node-physenv exit) env)
    (when (eq (functional-kind exit-fun) :escape)
      (mapc (lambda (x)
              (setf (node-derived-type x) *wild-type*))
            (leaf-refs exit-fun))
      (substitute-leaf (find-constant (opaquely-quote info)) exit-fun))
    (when lvar
      (let ((node (block-last (nlx-info-target info))))
        (unless (node-lvar node)
          (aver (eq lvar (node-lvar exit)))
          (setf (node-derived-type node) (lvar-derived-type lvar))
          (add-lvar-use node lvar)))))
  (values))

;;; Iterate over the EXITs in COMPONENT, calling NOTE-NON-LOCAL-EXIT
;;; when we find a block that ends in a non-local EXIT node.
(defun find-non-local-exits (component)
  (declare (type component component))
  (let ((*functional-escape-info* nil))
    (dolist (lambda (component-lambdas component))
      (dolist (entry (lambda-entries lambda))
        (let ((target-physenv (node-physenv entry)))
          (dolist (exit (entry-exits entry))
            (aver (neq (node-physenv exit) target-physenv))
            (note-non-local-exit target-physenv exit))))))
  (values))

;;;; final decision on stack allocation of dynamic-extent structures
(defun recheck-dynamic-extent-lvars (component)
  (declare (type component component))
  (let (*dx-combination-p-check-local*) ;; catch unconverted combinations
    (dolist (lambda (component-lambdas component))
      (loop for entry in (lambda-entries lambda)
            for cleanup = (entry-cleanup entry)
            do (when (eq (cleanup-kind cleanup) :dynamic-extent)
                 (collect ((real-dx-lvars))
                   (loop for what in (cleanup-info cleanup)
                         do (etypecase what
                              (cons
                               (let ((dx (car what))
                                     (lvar (cdr what)))
                                 (cond ((lvar-good-for-dx-p lvar dx component)
                                        ;; Since the above check does deep
                                        ;; checks. we need to deal with the deep
                                        ;; results in here as well.
                                        (dolist (cell (handle-nested-dynamic-extent-lvars
                                                       dx lvar component))
                                          (let ((real (principal-lvar (cdr cell))))
                                            (setf (lvar-dynamic-extent real) cleanup)
                                            (real-dx-lvars real))))
                                       (t
                                        (note-no-stack-allocation lvar)
                                        (setf (lvar-dynamic-extent lvar) nil)))))
                              (node     ; DX closure
                               (let* ((call what)
                                      (arg (first (basic-combination-args call)))
                                      (funs (lvar-value arg))
                                      (dx nil))
                                 (dolist (fun funs)
                                   (binding* ((() (leaf-dynamic-extent fun)
                                               :exit-if-null)
                                              (xep (functional-entry-fun fun)
                                                   :exit-if-null)
                                              (closure (physenv-closure
                                                        (get-lambda-physenv xep))))
                                     (cond (closure
                                            (setq dx t))
                                           (t
                                            (setf (leaf-extent fun) nil)))))
                                 (when dx
                                   (setf (lvar-dynamic-extent arg) cleanup)
                                   (real-dx-lvars arg))))))
                   (let ((real-dx-lvars (delete-duplicates (real-dx-lvars))))
                     (setf (cleanup-info cleanup) real-dx-lvars)
                     (setf (component-dx-lvars component)
                           (append real-dx-lvars (component-dx-lvars component)))))))))
  (values))

;;;; cleanup emission
(defun cleanup-code (cleanup)
  (let* ((node (cleanup-mess-up cleanup))
         (args (when (basic-combination-p node)
                 (basic-combination-args node))))
    (ecase (cleanup-kind cleanup)
      (:special-bind
       `(%special-unbind ',(lvar-value (car args))))
      (:catch
          `(%catch-breakup ,(opaquely-quote (car (cleanup-info cleanup)))))
      (:unwind-protect
           (values `(%unwind-protect-breakup ,(opaquely-quote (car (cleanup-info cleanup))))
                   (let ((fun (ref-leaf (lvar-uses (second args)))))
                     (when (functional-p fun)
                       fun))))
      ((:block :tagbody)
       (when (cleanup-info cleanup)
         `(progn
            ,@(loop for nlx in (cleanup-info cleanup)
                    collect `(%lexical-exit-breakup ,(opaquely-quote nlx))))))
      (:dynamic-extent
       (when (cleanup-info cleanup)
         `(%cleanup-point)))
      (:restore-nsp
       `(%primitive set-nsp ,(ref-leaf node))))))

;;; Go through the points where the extent of things like special bindings, unwind-protect, etc. ends
;;; and insert the code needed to clean them up (unbind, unlink unwind-block)
;;; before the control proceeds to the next block.
(defun find-cleanup-points (component)
  (declare (type component component))
  (let ((*current-component* component))
    (do-blocks (succ-block component)
      (unless (and (block-to-be-deleted-p succ-block)
                   (block-start succ-block))
        (let* ((succ-env (block-physenv succ-block))
               (start-node (block-start-node succ-block))
               (succ-cleanup (node-enclosing-cleanup start-node))
               (lexenv (node-lexenv start-node))
               (messup-cleanup (and succ-cleanup
                                    (node-enclosing-cleanup
                                     (cleanup-mess-up succ-cleanup))))
               (functionals nil))
          (declare (special functionals))
          (let ((all-cleanups
                  (loop for pred in (block-pred succ-block)
                        when (and (block-start pred)
                                  (neq (block-end-cleanup pred) succ-cleanup)
                                  (eq (block-physenv pred) succ-env)
                                  ;; Ignore the cleanup transition if it is to a cleanup enclosed by
                                  ;; the current cleanup, since in that case we are just messing up the
                                  ;; environment, hence this is not the place to clean it.
                                  (not (and succ-cleanup
                                            (eq messup-cleanup
                                                (block-end-cleanup pred))))
                                  (cleanups-up-to pred lexenv succ-cleanup))
                        collect it)))
            (when all-cleanups
              (setf (component-reanalyze component) t)
              (let ((*current-path* (node-source-path (block-start-node succ-block))))
                (labels ((insert (succ-block lexenv form)
                           (with-component-last-block (component
                                                       (block-next (component-head component)))
                             (let* ((start (make-ctran))
                                    (block (ctran-starts-block start))
                                    (next (make-ctran))
                                    (*lexenv* lexenv))
                               (link-blocks block succ-block)
                               (ir1-convert start next nil form)
                               (setf (block-last block) (ctran-use next))
                               (setf (node-next (block-last block)) nil)
                               block)))
                         (split-equal (cleanups)
                           (let ((result))
                             (loop for cleanup in cleanups
                                   for cons = (find (cdar cleanup) result :key #'cdaar :test #'equal-opaque-box)
                                   if cons
                                   do (push cleanup (cdr cons))
                                   else
                                   do (push (list cleanup) result))
                             result))
                         (emit-cleanups (succ all-cleanups)
                           (loop for common-cleanups in (split-equal all-cleanups)
                                 for new-block = (insert succ (cadaar common-cleanups) (cddaar common-cleanups))
                                 do
                                 (let (remaining)
                                   (loop for (((block) . rest)) on common-cleanups
                                         if rest
                                         do (push rest remaining)
                                         else
                                         do (change-block-successor block succ-block new-block))
                                   (emit-cleanups new-block remaining)))))
                  ;; Many blocks end up with the same cleanups
                  ;; e.g. (let (*) (if x 1 2))
                  ;; Or with more complicated diverging paths
                  ;; e.g. (let (*) (if x (let (**) 1) 2))
                  ;; This goes backwards from * and inserts the same
                  ;; cleanups until the paths diverge.
                  (emit-cleanups succ-block all-cleanups)))
              (dolist (fun functionals)
                (locall-analyze-fun-1 fun))))))))
  (values))

(defun cleanups-up-to (block lexenv cleanup)
  (declare (special functionals))
  (let (cleanups)
    (block nil
      (map-nested-cleanups-and-lexenvs
       (lambda (current-cleanup current-lexenv)
         (when (eq current-cleanup cleanup)
           (return))
         (when (eq (cleanup-kind current-cleanup) :dynamic-extent)
           ;; After this point only STACK-ANALYZE cares about cleanups,
           ;; and only of the :dynamic-extent kind. Force the previously
           ;; collected cleanups to have a DX cleanup.
           ;; Could make each cleanup use its own lexenv, but then the
           ;; cleanups with identical code wouldn't be shared.
           (loop for cleanup in cleanups
                 when (eq (cadr cleanup) lexenv)
                 do (setf (cadr cleanup) current-lexenv)))
         (multiple-value-bind (code fun) (cleanup-code current-cleanup)
           (when code
             (push (list* block lexenv code) cleanups)
             (when fun
               (push `(,block ,lexenv . (%funcall ,fun)) cleanups)
               (pushnew fun functionals :test #'eq)))))
       (block-end-lexenv block)))
    cleanups))

;;; Mark optimizable tail-recursive uses of function result
;;; continuations with the corresponding TAIL-SET.
;;;
;;; Regarding the suppression of TAIL-P for nil-returning calls,
;;; a partial history of the changes affecting this is as follows:
;;;
;;; WHN said [in 85f9c92558538b85540ff420fa8970af91e241a2]
;;;  ;; Nodes whose type is NIL (i.e. don't return) such as calls to
;;;  ;; ERROR are never annotated as TAIL-P, in order to preserve
;;;  ;; debugging information.
;;;
;;; NS added [in bea5b384106a6734a4b280a76e8ebdd4d51b5323]
;;;  ;; Why is that bad? Because this non-elimination of
;;;  ;; non-returning tail calls causes the XEP for FOO [to] appear in
;;;  ;; backtrace for (defun foo (x) (error "foo ~S" x)) w[h]ich seems
;;;  ;; less then optimal. --NS 2005-02-28
;;; (not considering that the point of non-elimination was specifically
;;; to allow FOO to appear in the backtrace?)
;;;
(defun tail-annotate (component)
  (declare (type component component))
  (dolist (fun (component-lambdas component))
    (let ((ret (lambda-return fun)))
      ;; The code below assumes that a lambda whose final node is a call to
      ;; a non-returning function gets a lambda-return. But it doesn't always,
      ;; and it's not clear whether that means "always doesn't".
      ;; If it never does, then (WHEN RET ..) will never execute, so we won't
      ;; even see the call that might be be annotated as tail-p, regardless
      ;; of whether we *want* to annotate it as such.
      (when ret
        (let ((result (return-result ret)))
          (do-uses (use result)
            (when (and (basic-combination-p use)
                       (immediately-used-p result use)
                       (or (eq (basic-combination-kind use) :local)
                           ;; Nodes whose type is NIL (i.e. don't return) such
                           ;; as calls to ERROR are never annotated as TAIL-P,
                           ;; in order to preserve debugging information, so that
                           ;;
                           ;; We spread this net wide enough to catch
                           ;; untrusted NIL return types as well, so that
                           ;; frames calling functions such as FOO-ERROR are
                           ;; kept in backtraces:
                           ;;
                           ;;  (defun foo-error (x) (error "oops: ~S" x))
                           ;;
                           (not (or (eq *empty-type* (node-derived-type use))
                                    (eq *empty-type* (combination-defined-type use))))))
              (setf (node-tail-p use) t)))))))
  ;; The above loop does not find all calls to ERROR.
  (do-blocks (block component)
    (do-nodes (node nil block)
      ;; CAUTION: This looks scary because it affects all known nil-returning
      ;; calls even if not in tail position. Use of the policy quality which
      ;; enables tail-p must be confined to a very restricted lexical scope.
      ;; This might be better implemented as a local declaration about
      ;; function names at the call site: (declare (uninhibit-tco error))
      ;; but adding new kinds of declarations is fairly invasive surgery.
      (when (and (combination-p node)
                 (combination-fun-info node) ; must be a known fun
                 (eq (combination-defined-type node) *empty-type*)
                 (policy node (= allow-non-returning-tail-call 3)))
        (setf (node-tail-p node) t))))
  (values))
