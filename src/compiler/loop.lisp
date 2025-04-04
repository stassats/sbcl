;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

;;; **********************************************************************
;;;
;;; Stuff to annotate the flow graph with information about the loops in it.
;;;
;;; Written by Rob MacLachlan
(in-package "SB-C")

;;; FIND-DOMINATORS  --  Internal
;;;
;;; Find the immediate dominator of each block in COMPONENT.  If a
;;; block is not reachable from an entry point, then its immediate
;;; dominator will still be NIL when we are done.
(defun find-dominators (component)
  (let ((head (loop-head (component-outer-loop component)))
        changed)
    (setf (block-dominator head) head)
    (dfo-as-needed component)
    (labels ((intersect (block1 block2)
               (cond ((eq block1 block2) block1)
                     ((< (block-number block1) (block-number block2))
                      (intersect (block-dominator block1) block2))
                     (t
                      (intersect block1 (block-dominator block2))))))
      (loop
       (setq changed nil)
       (do-blocks (block component :tail)
         (let ((dom))
           (dolist (pred (block-pred block))
             (unless (null (block-dominator pred))
               (setq dom (if dom
                             (intersect pred dom)
                             pred))))
           (unless (eq (block-dominator block) dom)
             (setf (block-dominator block) dom)
             (setq changed t))))
       (unless changed (return))))
    (setf (block-dominator head) nil)))

(defun clear-dominators (component)
  (do-blocks (block component)
    (setf (block-dominator block) nil)))

;;; DOMINATES-P  --  Internal
;;;
;;;    Return true if BLOCK1 dominates BLOCK2, false otherwise.
(defun dominates-p (block1 block2)
  (cond ((null block2) nil)
        ((eq block1 block2) t)
        (t
         (dominates-p block1 (block-dominator block2)))))

;;; LOOP-ANALYZE  --  Interface
;;;
;;; Set up the LOOP structures which describe the loops in the flow
;;; graph for COMPONENT.  We NIL out any existing loop information,
;;; and then scan through the blocks looking for blocks which are the
;;; destination of a retreating edge: an edge that goes backward in
;;; the DFO.  We then create LOOP structures to describe the loops
;;; that have those blocks as their heads.  If find the head of a
;;; strange loop, then we do some graph walking to find the other
;;; segments in the strange loop.  While we are finding the loop
;;; structures in reverse DFO, we walk it to initialize the block
;;; lists and initialize the nesting pointers. Then we assign loop depth.
(defun loop-analyze (component)
  (let ((outer-loop (component-outer-loop component)))
    (do-blocks (block component :both)
      (setf (block-loop block) nil))
    (setf (loop-inferiors outer-loop) ())
    (setf (loop-blocks outer-loop) ())
    ;; By traversing in reverse depth first ordering, we guarantee
    ;; that inner loop heads will be discovered before their
    ;; superiors, since dominated nodes always have lower DFNs.
    (do-blocks-backwards (block component)
      (let ((number (block-number block)))
        (dolist (pred (block-pred block))
          (when (<= (block-number pred) number)
            (let ((loop (note-loop-head block component)))
              (when (eq (loop-kind loop) :strange)
                (clear-flags component)
                (setf (block-flag block) :good)
                (dolist (succ (block-succ block))
                  (find-strange-loop-blocks succ block))
                (find-strange-loop-segments block component))
              (find-loop-blocks loop)
              ;; Loops with no exits are unreachable by predecessor walk and
              ;; by definition belong to the component outer loop.
              (when (eq (loop-kind loop) :natural)
                (unless (or (loop-exits loop)
                            (eq outer-loop loop))
                  (setf (loop-superior loop) outer-loop)
                  (push loop (loop-inferiors outer-loop)))))
            (return)))))
    ;; Remaining blocks belong to the outer loop.
    (find-loop-blocks outer-loop)
    (labels ((assign-depth (loop depth)
               (setf (loop-depth loop) depth)
               (dolist (inferior (loop-inferiors loop))
                 (assign-depth inferior (1+ depth)))))
      (assign-depth outer-loop 0))))

;;; FIND-LOOP-BLOCKS  --  Internal
;;;
;;; This function initializes the block lists and inferiors of LOOP.
;;; When we are done, we scan the blocks looking for exits.  An exit
;;; is always a block that has a successor which doesn't have a LOOP
;;; assigned yet, since the target of the exit must be in a superior
;;; loop.
;;;
;;; We find the blocks by doing a backward walk from the tails of the
;;; loop and from any heads of nested loops.  The walks from inferior
;;; loop heads are necessary because the walks from the tails
;;; terminate when they encounter a block in an inferior loop.
(defun find-loop-blocks (loop)
  (dolist (tail (loop-tail loop))
    (find-blocks-from-here tail loop))
  ;; For the outermost loop, new blocks can still be discovered by
  ;; walking back from natural loops with no exits.
  (when (eq (loop-kind loop) :outer)
    (dolist (sub-loop (loop-inferiors loop))
      (dolist (pred (block-pred (loop-head sub-loop)))
        (find-blocks-from-here pred loop))))
  (collect ((exits))
    (dolist (sub-loop (loop-inferiors loop))
      (dolist (exit (loop-exits sub-loop))
        (dolist (succ (block-succ exit))
          (unless (block-loop succ)
            (exits exit)
            (return)))))

    (do ((block (loop-blocks loop) (block-loop-next block)))
        ((null block))
      (dolist (succ (block-succ block))
        (unless (block-loop succ)
          (exits block)
          (return))))
    (setf (loop-exits loop) (exits))))


;;; FIND-BLOCKS-FROM-HERE  --  Internal
;;;
;;; This function does a graph walk to find the blocks directly within
;;; LOOP that can be reached by a backward walk from BLOCK.  If BLOCK
;;; is already in LOOP or is not dominated by the LOOP-HEAD, then we
;;; return.  If another loop is already assigned to BLOCK, it must be
;;; an inferior loop.  If this loop doesn't have a superior yet, we
;;; record that it must be a direct inferior of LOOP, and recurse on
;;; the head of this loop's predecessor.  But if BLOCK's loop already
;;; has a superior, then we can directly recurse on its existing
;;; superior's head, since all predecessors of the head of BLOCK's
;;; loop are contained in its superior already.  Otherwise, we add the
;;; block to the BLOCKS for LOOP and recurse on its predecessors.
(defun find-blocks-from-here (block loop)
  (when (and (not (eq (block-loop block) loop))
             (dominates-p (loop-head loop) block))
    (cond ((block-loop block)
           (let* ((inner (block-loop block))
                  (inner-superior (loop-superior inner)))
             (cond ((not inner-superior)
                    (setf (loop-superior inner) loop)
                    (push inner (loop-inferiors loop))
                    (dolist (pred (block-pred (loop-head inner)))
                      (find-blocks-from-here pred loop)))
                   ((not (eq inner-superior loop))
                    (find-blocks-from-here (loop-head inner-superior) loop)))))
          (t
           (setf (block-loop block) loop)
           (shiftf (block-loop-next block) (loop-blocks loop) block)
           (dolist (pred (block-pred block))
             (find-blocks-from-here pred loop))))))

;;; NOTE-LOOP-HEAD  --  Internal
;;;
;;; Create a loop structure to describe the loop headed by the block
;;; HEAD.  If some retreating edge into the head is from a block which
;;; isn't dominated by the head, then we have the head of a strange
;;; loop segment.
(defun note-loop-head (head component)
  (declare (ignore component))
  (let ((result (make-loop :natural head))
        (number (block-number head)))
    (dolist (pred (block-pred head))
      (when (<= (block-number pred) number)
        (if (dominates-p head pred)
            (push pred (loop-tail result))
            (setf (loop-kind result) :strange))))
    result))


;;; FIND-STRANGE-LOOP-BLOCKS  --  Internal
;;;
;;; Do a graph walk to find the blocks in the strange loop which HEAD
;;; is in.  BLOCK is the block we are currently at and COMPONENT is
;;; the component we are in.  We do a walk forward from block, using
;;; only edges which are not back edges.  We return true if there is a
;;; path from BLOCK to HEAD, false otherwise.  If the BLOCK-FLAG is
;;; true then we return.  We use two non-null values of FLAG to
;;; indicate whether a path from the BLOCK back to HEAD was found.
(defun find-strange-loop-blocks (block head)
  (let ((flag (block-flag block)))
    (cond (flag
           (if (eq flag :good)
               t
               nil))
          (t
           (setf (block-flag block) :bad)
           (unless (dominates-p block head)
             (dolist (succ (block-succ block))
               (when (find-strange-loop-blocks succ head)
                 (setf (block-flag block) :good))))
           (eq (block-flag block) :good)))))

;;; FIND-STRANGE-LOOP-SEGMENTS  --  Internal
;;;
;;; Do a graph walk to find the segments in the strange loop that has
;;; BLOCK in it.  We walk forward, looking only at blocks in the loop
;;; (flagged as :GOOD.)  Each block in the loop that has predecessors
;;; outside of the loop is the head of a segment.  We enter the LOOP
;;; structures in COMPONENT.
(defun find-strange-loop-segments (block component)
  (when (eq (block-flag block) :good)
    (setf (block-flag block) :done)
    (unless (every #'(lambda (x) (member (block-flag x) '(:good :done)))
                   (block-pred block))
      (note-loop-head block component))
    (dolist (succ (block-succ block))
      (find-strange-loop-segments succ component))))
