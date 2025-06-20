;;;; allocation VOPs for the x86-64

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB-VM")

;;;; allocation helpers

;;; Most allocation is done by inline code with sometimes help
;;; from the C alloc() function by way of the alloc-tramp
;;; assembly routine.

(defun tagify (result base lowtag)
  (if (eql lowtag 0)
      (inst mov result base)
      (inst lea result (ea lowtag base))))

(defun generate-stack-overflow-check (vop size)
  (let ((overflow (generate-error-code
                   vop
                   'stack-allocated-object-overflows-stack-error
                   (if (integerp size)
                       (make-sc+offset immediate-sc-number size)
                       size))))
    (inst sub rsp-tn size)
    (inst cmp :qword rsp-tn (thread-slot-ea thread-control-stack-start-slot))
    ;; avoid clearing condition codes
    (inst lea rsp-tn (if (integerp size)
                         (ea size rsp-tn)
                         (ea rsp-tn size)))
    (inst jmp :le overflow)))

(defun stack-allocation (size lowtag alloc-tn &optional known-alignedp)
  (aver (not (location= alloc-tn rsp-tn)))
  (inst sub rsp-tn size)
  ;; see comment in x86/macros.lisp implementation of this
  ;; However that comment seems inapplicable here because:
  ;; - PAD-DATA-BLOCK quite clearly enforces double-word alignment,
  ;;   contradicting "... unfortunately not enforced by ..."
  ;; - It's not the job of FIXED-ALLOC to realign anything.
  ;; - The real issue is that it's not obvious that the stack is
  ;;   16-byte-aligned at *all* times. Maybe it is, maybe it isn't.
  (unless (aligned-stack-p known-alignedp) ; can skip this AND if we're all good
    (inst and rsp-tn #.(lognot lowtag-mask)))
  (tagify alloc-tn rsp-tn lowtag)
  (values))

(defun alloc-unboxed-p (type)
  (case type
    ((unboxed-array
      #.bignum-widetag
      #.sap-widetag
      #.double-float-widetag
      #.complex-single-float-widetag
      #.complex-double-float-widetag)
     t)))

;;; Insert allocation profiler instrumentation
(eval-when (:compile-toplevel)
  (aver (= thread-tot-bytes-alloc-unboxed-slot
           (1+ thread-tot-bytes-alloc-boxed-slot))))

(defun instrument-alloc-policy-p (node)
  (policy node (> sb-c::instrument-consing 1)))

;;; Emit counter increments for SB-APROF. SCRATCH-REGISTERS is either a TN
;;; or list of TNs that can be used to store into the profiling data.
;;; We pick one of the available TNs to use for addressing the data buffer.
;;; The TN that we pick can't be R12 because encoding it into an instruction
;;; always requires a SIB byte, which doesn't fit in the reserved bytes
;;; of the instruction stream where hot patching occurs.
;;; Compare:
;;;        F048FF4018       LOCK INC QWORD PTR [RAX+24]
;;;        F049FF442418     LOCK INC QWORD PTR [R12+24]
(defun emit-instrument-alloc
    (node thread-temp type size scratch-registers
     &aux (temp (if (listp scratch-registers)
                    (dolist (reg scratch-registers (first scratch-registers))
                      (unless (location= reg r12-tn) (return reg)))
                    scratch-registers)))
  (declare (ignorable type thread-temp))
  ;; Each allocation sequence has to call INSTRUMENT-ALLOC,
  ;; so we may as well take advantage of this fact to load the temp reg
  ;; here, if provided, rather than spewing more #+gs-seg tests around.
  #+gs-seg (when thread-temp (inst rdgsbase thread-temp))
  (when (member :allocation-size-histogram sb-xc:*features*)
    (let ((use-size-temp (not (typep size '(or (signed-byte 32) tn)))))
      ;; Sum up the sizes of boxed vs unboxed allocations.
      (cond ((tn-p type) ; from ALLOCATE-VECTOR-ON-HEAP
             ;; Constant huge size + unknown type can't occur.
             (aver (not use-size-temp))
             (inst cmp :byte type simple-vector-widetag)
             (inst set :ne temp)
             (inst and :dword temp 1)
             (inst add :qword
                   (ea thread-segment-reg
                       (ash thread-tot-bytes-alloc-boxed-slot word-shift)
                       thread-tn temp 8)
                   size))
            (t
             (inst add :qword
                   (thread-slot-ea (if (alloc-unboxed-p type)
                                       thread-tot-bytes-alloc-unboxed-slot
                                       thread-tot-bytes-alloc-boxed-slot))
                   (cond (use-size-temp (inst mov temp size) temp)
                         (t size)))))
      (cond ((tn-p size)
             (assemble ()
               ;; optimistically assume it's a small object, so just divide
               ;; the size by the size of a cons to get a (1-based) index.
               (inst mov :dword temp size)
               (inst shr :dword temp (1+ word-shift))
               ;; now see if the computed index is in range
               (inst cmp size (* n-histogram-bins-small 16))
               (inst jmp :le OK)
               ;; oversized. Compute the log2 of the size
               (inst bsr :dword temp size)
               ;; array of counts ... | array of sizes ...
               (inst add :qword (ea (ash (+ thread-allocator-histogram-slot
                                            1
                                            (- first-large-histogram-bin-log2size)
                                            n-histogram-bins-small
                                            n-histogram-bins-large)
                                         word-shift)
                                    thread-tn temp 8)
                     size)
               ;; not sure why this is "2" and not "1" in the fudge factor!!
               ;; (but the assertions come out right)
               (inst add :dword temp
                     (+ (- first-large-histogram-bin-log2size) n-histogram-bins-small 2))
               OK
               (inst inc :qword (ea thread-segment-reg
                                    (ash (1- thread-allocator-histogram-slot) word-shift)
                                    thread-tn temp 8))))
            ((<= size (* sb-vm:cons-size sb-vm:n-word-bytes n-histogram-bins-small))
             (let ((index (1- (/ size (* sb-vm:cons-size sb-vm:n-word-bytes)))))
               (inst inc :qword (thread-slot-ea (+ thread-allocator-histogram-slot index)))))
            (t
             (let ((index (- (integer-length size) first-large-histogram-bin-log2size)))
               (inst add :qword (thread-slot-ea (+ thread-allocator-histogram-slot
                                                   n-histogram-bins-small
                                                   n-histogram-bins-large index))
                     size)
               (inst inc :qword (thread-slot-ea (+ thread-allocator-histogram-slot
                                                   n-histogram-bins-small index))))))))
  (when (instrument-alloc-policy-p node)
    (when (tn-p size)
      (aver (not (location= size temp))))
    ;; CAUTION: the logic for RAX-SAVE is entirely untested, due to R12 being
    ;; unusable by register allocator currently
    (binding* (((data rax-save) (if (location= temp r12-tn)
                                    (values rax-tn t)
                                    (values temp nil)))
               (patch-loc (gen-label))
               (skip-instrumentation (gen-label)))
      ;; Don't count allocations to the arena
      (inst cmp :qword (thread-slot-ea thread-arena-slot) 0)
      (inst jmp :nz skip-instrumentation)
      (when rax-save (inst push rax-tn))
      (inst mov data (thread-slot-ea thread-profile-data-slot thread-temp))
      (inst test data data)
      ;; This instruction is modified to "JMP :z" when profiling is
      ;; partially enabled. After the buffer is assigned, it becomes
      ;; fully enabled. The unconditional jmp gives minimal performance
      ;; loss if the profiler is statically disabled. (one memory
      ;; read and a test whose result is never used, which the CPU
      ;; is good at ignoring as far as instruction prefetch goes)
      (emit-label patch-loc)
      (push patch-loc (sb-assem::asmstream-alloc-points sb-assem:*asmstream*))
      (inst jmp skip-instrumentation)
      (emit-alignment 3 :long-nop)
      (let ((helper
             (if (integerp size) 'enable-alloc-counter 'enable-sized-alloc-counter)))
        ;; This jump is always encoded as 5 bytes
        (inst call (if (or (not node) ; assembly routine
                           (code-immobile-p node))
                       (make-fixup helper :assembly-routine)
                       (uniquify-fixup helper))))
      (inst nop)
      ;; Emit "TEST AL, imm" where the immediate value
      ;; encodes the the data buffer base reg and size reg numbers.
      (inst byte #xA8) ; "TEST AL,imm"
      (cond ((integerp size)
             (inst byte (tn-offset data)))
            (t
             (inst byte (logior (tn-offset data) (ash (tn-offset size) 4)))
             (inst .skip 8 :long-nop)))
      (when rax-save (inst pop rax-tn))
      (emit-label skip-instrumentation))))

;;; An arbitrary marker for the cons primitive-type, not to be confused
;;; with the CONS-TYPE in our type-algebraic sense. Mostly just informs
;;; the allocator to use cons_tlab.
(defconstant +cons-primtype+ list-pointer-lowtag)

(define-vop (sb-c::end-pseudo-atomic)
  (:generator 1 (emit-end-pseudo-atomic)))

;;; Emit code to allocate an object with a size in bytes given by
;;; SIZE into ALLOC-TN. The size may be an integer of a TN.
;;; NODE may be used to make policy-based decisions.
;;; This function should only be used inside a pseudo-atomic section,
;;; which to the degree needed should also cover subsequent initialization.
;;;
;;; A mnemonic device for the argument pattern here:
;;; 1. what to allocate: type, size, lowtag describe the object
;;; 2. where to put the result
;;; 3. node (for determining immobile-space-p) and a scratch register or two
(defun emit-allocation (node thread-temp type size lowtag alloc-tn temp
                        &key scale overflow (systemp (system-tlab-p type node)))
  (declare (ignorable thread-temp))
  (flet ((fallback (size)
           ;; Call an allocator trampoline and get the result in the proper register.
           ;; There are 2 choices of trampoline to invoke alloc() or alloc_list()
           ;; in C. This is chosen by the name of the asm routine.
           (cond ((typep size '(and integer (not (signed-byte 32))))
                  ;; MOV accepts large immediate operands, PUSH does not
                  (inst mov alloc-tn size)
                  (inst push alloc-tn))
                 (t
                  (inst push size)))
           (invoke-asm-routine
            'call
            (if systemp
                (if (eql type +cons-primtype+) 'sys-list-alloc-tramp 'sys-alloc-tramp)
                (if (eql type +cons-primtype+) 'list-alloc-tramp 'alloc-tramp))
            node)
           (inst pop alloc-tn)))
    (let* ((NOT-INLINE (gen-label))
           (DONE (gen-label))
           (free-pointer (thread-slot-ea
                          (if systemp
                              (if (eql type +cons-primtype+)
                                   thread-sys-cons-tlab-slot
                                   thread-sys-mixed-tlab-slot)
                               (if (eql type +cons-primtype+)
                                   thread-cons-tlab-slot
                                   thread-mixed-tlab-slot))
                           #+gs-seg thread-temp))
           (end-addr (ea (sb-x86-64-asm::ea-segment free-pointer)
                         (+ n-word-bytes (ea-disp free-pointer))
                         (ea-base free-pointer))))
      (cond ((and (integerp size) (>= size (target-heap-large-object-size)))
             ;; large objects will never be made in a per-thread region
             (cond (overflow (funcall overflow))
                   (t (fallback size)
                      (when (/= lowtag 0) (inst or :byte alloc-tn lowtag)))))
            ((and (tn-p size) (location= size alloc-tn))
             (aver (and temp (not (location= temp size))))
             (inst mov temp free-pointer)
             ;; alloc-tn <- old free ptr and temp <- new free ptr
             (inst xadd temp alloc-tn)
             (inst cmp temp end-addr)
             (inst jmp :a NOT-INLINE)
             (inst mov free-pointer temp)
             (emit-label DONE)
             (when (/= lowtag 0) (inst or :byte alloc-tn lowtag))
             (assemble (:elsewhere)
               (emit-label NOT-INLINE)
               (inst sub temp alloc-tn) ; new-free-ptr - old-free-ptr = size
               (cond (overflow (funcall overflow))
                     (t (fallback temp)
                        (inst jmp DONE)))))
            (t
             ;; fixed-size allocation whose size fits in an imm32 can be done
             ;; with only one register, the ALLOC-TN. If it doesn't fit in imm32,
             ;; it would get the first branch of the COND, for large objects.
             (inst mov alloc-tn free-pointer)
             (cond (temp
                    (when (tn-p size) (aver (not (location= size temp))))
                    (inst lea temp (if scale (ea alloc-tn size scale) (ea size alloc-tn)))
                    (inst cmp temp end-addr)
                    (inst jmp :a NOT-INLINE)
                    (inst mov free-pointer temp)
                    (emit-label DONE)
                    (when (/= lowtag 0) (inst or :byte alloc-tn lowtag)))
                   (t
                    (inst add alloc-tn size)
                    (inst cmp alloc-tn end-addr)
                    (inst jmp :a NOT-INLINE)
                    (inst mov free-pointer alloc-tn)
                    (cond ((tn-p size)
                           (inst sub alloc-tn size)
                           (emit-label DONE)
                           (when (/= lowtag 0) (inst or :byte alloc-tn lowtag)))
                          (t
                           ;; SUB can compute the result and tagify it.
                           ;; The fallback also has to tagify.
                           (let ((bias (+ (- size) lowtag)))
                             (if (= bias -1) (inst dec alloc-tn) (inst add alloc-tn bias)))
                           (emit-label DONE)))))
             (assemble (:elsewhere)
               (emit-label NOT-INLINE)
               (cond (overflow (funcall overflow))
                     (t
                      (fallback size)
                      (when (and (/= lowtag 0) (not temp) (not (tn-p size)))
                        (inst or :byte alloc-tn lowtag))
                      (inst jmp DONE))))))))
  t)

;;; Allocate an other-pointer object of fixed NWORDS with a single-word
;;; header having the specified WIDETAG value. The result is placed in
;;; RESULT-TN.  NWORDS counts the header word.
;;;
;;; Revision 4fb3e8c376 added INITS with minimal explanation besides the obvious of
;;; performing initialization within pseudo-atomic. I believe the theory is that (some day)
;;; it may allow using un-pre-zeroed memory. GC would never see any lingering junk
;;; below the region's free pointer. Right now we can do the inits either inside or outside
;;; of pseudo-atomic because all pages except CONS are prezeroed.
(defun emit-alloc-other (node thread-temp widetag nwords result-tn
                         &optional alloc-temps init
                         &aux (bytes (pad-data-block nwords)))
  (declare (dynamic-extent init))
  #+bignum-assertions
  (when (= widetag bignum-widetag) (setq bytes (* bytes 2))) ; use 2x the space
  (emit-instrument-alloc node thread-temp widetag bytes
                         (cons result-tn (ensure-list alloc-temps)))
  (let ((header (compute-object-header nwords widetag))
        (alloc-temp (if (listp alloc-temps) (car alloc-temps) alloc-temps)))
    (allocating ()
      (cond (alloc-temp
             (emit-allocation node thread-temp widetag bytes 0 result-tn alloc-temp)
             (storew* header result-tn 0 0 t)
             (inst or :byte result-tn other-pointer-lowtag))
            (t
             (emit-allocation node thread-temp widetag bytes other-pointer-lowtag result-tn nil)
             (storew* header result-tn 0 other-pointer-lowtag t)))
      (when init
        (funcall init)))))

(defun list-ctor-push-elt (x scratch)
  (multiple-value-bind (operand loadp)
      (if (sc-is x immediate)
          (let ((bits (immediate-tn-repr x)))
            (values bits (typep bits '(or (and integer (not (signed-byte 32)))
                                          nil-relative))))
          (values x nil))
    (inst push (cond ((not loadp) operand)
                     ((typep operand '(unsigned-byte 32))
                      ;; Do a 32-bit move to register, then push as 64 bits.
                      ;; A raw constant would need 8 bytes plus a 6-byte PUSH
                      ;; instruction, but this way encodes to 6 bytes in total.
                      (inst mov :dword scratch operand)
                      scratch)
                     ((nil-relative-p operand) (move-immediate scratch operand))
                     (t (constantize operand))))))

;;;; CONS, ACONS, LIST and LIST*

(defun consing-singleton-nil-p (car cdr)
  (and (eq car cdr) (sc-is car immediate) (null (tn-value car))))

(defun finish-list (alloc result)
  (if (location= alloc result)
      (inst or :byte alloc list-pointer-lowtag)
      (inst lea result (ea list-pointer-lowtag alloc))))

;;; General remark on the optimization for storing partial words when the heap is prezeroed:
;;; It's not terribly important. Gencgc does not prezero cons pages, and the work-in-progress
;;; concurrent collector prefills pages with -1 (an illegal pattern) so that a valid cons
;;; cell can always be recognized without scanning an array of bits to decide which cells
;;; were actually allocated. Mark-region GC does prezero, but perhaps it need not.
(defun init-list (alloc temp result word-indices inits &optional dx)
  (declare (simple-vector word-indices) (dynamic-extent inits))
  (let* ((n (length word-indices))
         ;; SCOREBOARD tracks that the Ith element of INITS is done
         (scoreboard (make-array n :element-type 'bit :initial-element 0)))
    (aver (= n (length inits)))
    (do ((i 0 (1+ i)))
        ((>= i n))
      (let ((tn (pop inits)))
        (unless (= (sbit scoreboard i) 1) ; ignore if already did this
          (setf (sbit scoreboard i) 1)
          (let* ((imm (when (sc-is tn immediate) (immediate-tn-repr tn)))
                 ;; When IMMEDIATE-TN-REPR returns a fixup
                 ;; it is promised to fit in (SIGNED-BYTE 32)
                 (must-load (or (sc-is tn constant control-stack)
                                (and imm
                                     (neq imm null-tn)
                                     (not (typep imm '(or (signed-byte 32) fixup))))))
                 (repeats (memq tn inits))
                 (load (or must-load (and imm (neq imm null-tn) repeats)))
                 (val (or imm tn)))
            (let ((operand (cond (load
                                  ;; MOVE only wants TNs
                                  (cond ((tn-p val) (move temp val))
                                        ((nil-relative-p val) (move-immediate temp val))
                                        (t (inst mov temp val)))
                                  temp)
                                 (t val))))
              (let ((slot (svref word-indices i)))
                (if (and imm (not load) (not dx) (target-heap-prezeroed-p))
                    ;; This makes :smaller-than-qword-cons-slot-init pass
                    ;; but as the comment above says, it's probably not worth
                    ;; the small amount of clutter this adds to the logic.
                    (storew* imm alloc slot 0 t)
                    (storew operand alloc slot 0)))
              ;; This loop is helpful only if the source was not already in a register
              (when (and repeats load)
                ;; Scoreboard indices of remaining elements of INITS are numbered from (1+ I)
                (loop for j from (1+ i)
                      for init in inits
                      when (eq init tn)
                      do (storew operand alloc (svref word-indices j) 0)
                         (setf (sbit scoreboard j) 1)))))))))
  (when result
    (finish-list alloc result)))

(define-allocator (cons)
  (:args (car :scs (any-reg descriptor-reg constant immediate control-stack))
         (cdr :scs (any-reg descriptor-reg constant immediate control-stack)))
  (:temporary (:sc unsigned-reg :to (:result 0) :target result) alloc)
  (:temporary (:sc unsigned-reg :to (:result 0)
               :unused-if (node-stack-allocate-p (sb-c::vop-node vop)))
              temp)
  (:temporary (:unused-if (not (consing-singleton-nil-p car cdr)) :sc sse-reg)
              xmmtemp)
  (:results (result :scs (descriptor-reg)))
  (:vop-var vop)
  (:generator 10
    (let ((car-val (encode-value-if-immediate car))
          (car-regp (sc-is car any-reg descriptor-reg))
          (list-nil-p (consing-singleton-nil-p car cdr))
          (nbytes (* cons-size n-word-bytes)))
      ;; If consing two occurrences of the same value then load into a register unless:
      ;;  - already in a register, OR
      ;;  - PUSHing an imm8, in which case PUSH encodes to exactly 2 bytes
      ;; The second of the above two criteria pertains only to stack-allocation.
      ;; Memory operands are legal for PUSH, therefore CONSTANT and CONTROL-STACK
      ;; don't technically require a temp. However, I believe that one memory load
      ;; is better than two PUSH instructions using memory as the source operand.
      (when list-nil-p
        (inst movaps xmmtemp (ea (- list-pointer-lowtag) null-tn))) ; prefetch
      (cond
        ((node-stack-allocate-p node)
         (unless (aligned-stack-p)
           (inst and rsp-tn (lognot lowtag-mask)))
         (cond (list-nil-p
                (inst sub rsp-tn 16)
                (inst movaps (ea rsp-tn) xmmtemp))
               ((eq car cdr)
                (let ((operand (cond ((or car-regp (typep car-val '(signed-byte 8)))
                                      car-val)
                                     ((nil-relative-p car-val)
                                      (move-immediate alloc car-val))
                                     (t
                                      (inst mov alloc car-val)
                                      alloc))))
                  (inst push operand)
                  (inst push operand)))
               (t (list-ctor-push-elt cdr alloc)
                  (list-ctor-push-elt car alloc)))
         (inst lea result (ea list-pointer-lowtag rsp-tn)))
        (t
         (instrument-alloc +cons-primtype+ nbytes (list temp alloc))
         (allocating ()
           (allocation +cons-primtype+ nbytes 0 alloc temp)
           (cond (list-nil-p
                  (inst movaps (ea alloc) xmmtemp)
                  (finish-list alloc result))
                 (t
                  (init-list alloc temp result `#(,cons-car-slot ,cons-cdr-slot)
                             (list car cdr))))))))))

;;; In terms of minimizing memory loads (CONSTANT operand) or 4-byte immediate
;;; (immediate symbol operand) there are 4 possible patterns reusing a value
;;; none of which are very likely:
;;;   ((a . a) . a)
;;;   ((a . a) . b)
;;;   ((a . b) . a)
;;;   ((a . b) . b)
;;; INIT-LIST can figure out if any of the above patterns match the args.
;;;
;;; Also: Since alists tend to be persistent storage structures, there is probably
;;; not a lot of benefit to ACONS recognizing DX, though it couldn't hurt to have it,
;;; perhaps to temporarily add a key to a mapping.
(define-allocator (acons)
  (:args (key :scs (any-reg descriptor-reg constant immediate control-stack))
         (val :scs (any-reg descriptor-reg constant immediate control-stack))
         (tail :scs (any-reg descriptor-reg constant immediate control-stack)))
  (:temporary (:sc unsigned-reg :to (:result 0) :target result) alloc)
  (:temporary (:sc unsigned-reg :to (:result 0)) temp)
  (:results (result :scs (descriptor-reg)))
  (:translate acons)
  (:policy :fast-safe)
  (:generator 10
    (let ((nbytes (* cons-size 2 n-word-bytes)))
      (instrument-alloc +cons-primtype+ nbytes (list temp alloc))
      (allocating ()
        (allocation +cons-primtype+ nbytes 0 alloc temp)
        ;; the outer cons is at the lower address
        (inst lea temp (ea (+ 16 list-pointer-lowtag) alloc))
        (storew temp alloc cons-car-slot 0)
        (init-list alloc temp result #(1 2 3) (list tail key val))))))

;;; CONS-2 is similar to ACONS, except that instead of producing
;;;  ((X . Y) . Z) it produces (X Y . Z)
(define-allocator (cons-2)
  (:args (car :scs (any-reg descriptor-reg constant immediate control-stack))
         (cadr :scs (any-reg descriptor-reg constant immediate control-stack))
         (cddr :scs (any-reg descriptor-reg constant immediate control-stack)))
  (:temporary (:sc unsigned-reg :to (:result 0) :target result) alloc)
  (:temporary (:sc unsigned-reg :to (:result 0)
               :unused-if (node-stack-allocate-p (sb-c::vop-node vop)))
              temp)
  (:results (result :scs (descriptor-reg)))
  (:vop-var vop)
  (:generator 10
    (cond
      ((node-stack-allocate-p node)
       (unless (aligned-stack-p)
         (inst and rsp-tn (lognot lowtag-mask)))
       ;; TODO: avoid reload of constants just like for single DX CONS
       (list-ctor-push-elt cddr alloc)
       (list-ctor-push-elt cadr alloc)
       (inst lea alloc (ea list-pointer-lowtag rsp-tn))
       (inst push alloc) ; cdr of the first cons
       (list-ctor-push-elt car alloc)
       (inst lea result (ea list-pointer-lowtag rsp-tn)))
      (t
       (let ((nbytes (* cons-size 2 n-word-bytes)))
         (instrument-alloc +cons-primtype+ nbytes (list temp alloc))
         (allocating ()
           (allocation +cons-primtype+ nbytes 0 alloc temp)
           (inst lea temp (ea (+ 16 list-pointer-lowtag) alloc))
           (storew temp alloc cons-cdr-slot 0)
           (init-list alloc temp result #(0 2 3) (list car cadr cddr))))))))

(define-allocator (list)
  (:args (things :more t :scs (descriptor-reg any-reg constant immediate)))
  (:temporary (:sc unsigned-reg) temp)
  (:temporary (:sc unsigned-reg :to (:result 0) :target result) alloc)
  (:info star cons-cells)
  (:results (result :scs (descriptor-reg)))
  (:generator 0
    (aver (>= cons-cells 3)) ; prevent regressions in ir2tran's vop selection
    (let* ((stack-allocate-p (node-stack-allocate-p node))
           (size (* (pad-data-block cons-size) cons-cells))
           (indices (make-array (1+ cons-cells))))
      (collect ((items))
        (macrolet ((pop-thing ()
                     '(prog1 (tn-ref-tn things) (setf things (tn-ref-across things)))))
          (dotimes (i cons-cells)
            (setf (aref indices i) (ash i 1))
            (items (pop-thing)))
          (setf (aref indices cons-cells) (1+ (ash (1- cons-cells) 1)))
          (items (if star (pop-thing) (make-constant-tn (sb-c::find-constant nil)))))
        (aver (null things))
        (unless stack-allocate-p
          (instrument-alloc +cons-primtype+ size (list temp alloc)))
        (allocating (:elide-if stack-allocate-p)
          (if stack-allocate-p
              (stack-allocation size 0 alloc)
              (allocation +cons-primtype+ size 0 alloc temp))
          (init-list alloc temp nil indices (items) stack-allocate-p)
          ;; Stitch the cons cells together
          (dotimes (i (1- cons-cells))
            (case i
              (0 (inst lea temp (ea (+ 16 list-pointer-lowtag) alloc)))
              (t (inst add temp 16)))
            (inst mov (ea (- -8 list-pointer-lowtag) temp) temp))
          (finish-list alloc result))))))

(define-vop ()
  (:translate unaligned-dx-cons)
  (:args (car))
  (:results (result :scs (descriptor-reg)))
  (:ignore car)
  (:policy :fast-safe)
  (:generator 0
    (inst push null-tn)
    (inst lea result (ea (- list-pointer-lowtag n-word-bytes) rsp-tn))))

;;;; special-purpose inline allocators

;;; Special variant of 'storew' which might have a shorter encoding
;;; when storing to the heap (which starts out zero-filled).
;;; This will always write 8 bytes if WORD is a negative number.
(defun storew* (word object slot lowtag zeroed &optional temp)
  (cond
    ;; FIXME: I this misses some cases that could use a dword store
    ;; when the heap is prezeroed. Why can't it take (UNSIGNED-BYTE 32) ?
    ;; For example #x8000FFFF would work as a :DWORD and we leave the upper 4
    ;; bytes alone.
    ((or (not zeroed) (not (typep word '(unsigned-byte 31))))
     ;; Will use temp reg if WORD can't be encoded as an imm32
    (storew word object slot lowtag temp))
   ((/= word 0)
    (let ((size
           (cond ((typep word '(unsigned-byte 8))
                  :byte)
                 ((and (not (logtest word #xff))
                       (typep (ash word -8) '(unsigned-byte 8)))
                  ;; Array lengths 128 to 16384 which are multiples of 128
                  (setq word (ash word -8))
                  (decf lowtag 1) ; increment address by 1
                  :byte)
                 ((and (not (logtest word #xffff))
                       (typep (ash word -16) '(unsigned-byte 8)))
                  ;; etc
                  (setq word (ash word -16))
                  (decf lowtag 2) ; increment address by 2
                  :byte)
                 ((typep word '(unsigned-byte 16))
                  :word)
                 (t ; must be an (unsigned-byte 31)
                  :dword))))
      (inst mov size (object-slot-ea object slot lowtag) word)))))

;;; ALLOCATE-VECTOR
(defun store-string-trailing-null (vector type length words)
  ;; BASE-STRING needs to have a null terminator. The byte is inaccessible
  ;; to lisp, so clear it now.
  (cond ((and (sc-is type immediate)
              (/= (tn-value type) sb-vm:simple-base-string-widetag))) ; do nothing
        ((and (sc-is type immediate)
              (= (tn-value type) sb-vm:simple-base-string-widetag)
              (sc-is length immediate))
         (inst mov :byte (ea (- (+ (ash vector-data-offset word-shift)
                                   (tn-value length))
                                other-pointer-lowtag)
                             vector)
               0))
        ;; Zeroizing the entire final word is easier than using LENGTH now.
        ((sc-is words immediate)
         ;; I am not convinced that this case is reachable -
         ;; we won't DXify a vector of unknown type.
         (inst mov :qword
               ;; Given N data words, write to word N-1
               (ea (- (ash (+ (tn-value words) vector-data-offset -1)
                           word-shift)
                      other-pointer-lowtag)
                   vector)
               0))
        (t
         ;; This final case is ok with 0 data words - it might clobber the LENGTH
         ;; slot, but subsequently we rewrite that slot.
         ;; But strings always have at least 1 word, so no worries either way.
         (inst mov :qword
               (ea (- (ash (1- vector-data-offset) word-shift)
                      other-pointer-lowtag)
                   vector
                   words (ash 1 (- word-shift n-fixnum-tag-bits)))
               0))))

(macrolet ((calc-size-in-bytes (n-words size-tn)
             `(cond ((sc-is ,n-words immediate)
                     (pad-data-block (+ (tn-value ,n-words) vector-data-offset)))
                    (t
                     (inst lea ,size-tn
                           (ea (+ lowtag-mask (* vector-data-offset n-word-bytes))
                               nil ,n-words (ash 1 (- word-shift n-fixnum-tag-bits))))
                     (inst and ,size-tn (lognot lowtag-mask))
                     ,size-tn)))
           (put-header (vector-tn lowtag type len zeroed temp)
             `(let ((len (if (sc-is ,len immediate) (fixnumize (tn-value ,len)) ,len))
                    (type (if (sc-is ,type immediate) (tn-value ,type) ,type)))
                (storew* type ,vector-tn 0 ,lowtag ,zeroed ,temp)
                #+ubsan (inst mov :dword (vector-len-ea ,vector-tn ,lowtag) len)
                #-ubsan (storew* len ,vector-tn vector-length-slot
                                       ,lowtag ,zeroed ,temp)))
           (want-shadow-bits ()
             `(and poisoned
                   (if (sc-is type immediate)
                       (/= (tn-value type) simple-vector-widetag)
                       :maybe)))
           (calc-shadow-bits-size (reg)
             `(cond ((sc-is length immediate)
                     ;; Calculate number of dualwords (as 128 bits per dualword)
                     ;; and multiply by 16 to get number of bytes. Also add the 2 header words.
                     (* 16 (+ 2 (ceiling (tn-value length) 128))))
                    (t
                     ;; Compute (CEILING length 128) by adding 127, then truncating divide
                     ;; by 128, and untag as part of the divide step.
                     ;; Account for the two fixed words by adding in 128 more bits initially.
                     (inst lea :dword ,reg (ea (fixnumize (+ 128 127)) length))
                     (inst shr :dword ,reg 8) ; divide by 128 and untag as one operation
                     (inst shl :dword ,reg 4) ; multiply by 16 bytes per dualword
                     ,reg)))
           (store-originating-pc (vector)
             ;; Put the current program-counter into the length slot of the shadow bits
             ;; so that we can ascribe blame to the array's creator.
             `(let ((here (gen-label)))
                (emit-label here)
                (inst lea temp (rip-relative-ea here))
                (inst shl temp 4)
                (inst mov (ea (- 8 other-pointer-lowtag) ,vector) temp))))

  (define-allocator (allocate-vector-on-heap)
    #+ubsan (:info poisoned)
    (:args (type :scs (unsigned-reg immediate))
           (length :scs (any-reg immediate))
           (words :scs (any-reg immediate)))
    ;; Result is live from the beginning, like a temp, because we use it as such
    ;; in 'calc-size-in-bytes'
    (:results (result :scs (descriptor-reg) :from :load))
    (:arg-types #+ubsan (:constant t)
                positive-fixnum positive-fixnum positive-fixnum)
    (:temporary (:sc unsigned-reg) temp)
    (:policy :fast-safe)
    (:generator 100
      #+ubsan
      (when (want-shadow-bits)
        ;; allocate a vector of "written" bits unless the vector is simple-vector-T,
        ;; which can use unbound-marker as a poison value on reads.
        (when (sc-is type unsigned-reg)
          (inst cmp :byte type simple-vector-widetag)
          (inst push 0)
          (inst jmp :e NO-SHADOW-BITS))
        ;; It would be possible to do this and the array proper
        ;; in a single pseudo-atomic section, but I don't care to do that.
        (let ((nbytes (calc-shadow-bits-size result)))
          (allocating ()
            ;; Allocate the bits into RESULT
            (allocation simple-bit-vector-widetag nbytes 0 result temp nil)
            (inst mov :byte (ea result) simple-bit-vector-widetag)
            (inst mov :dword (vector-len-ea result 0)
                  (if (sc-is length immediate) (fixnumize (tn-value length)) length))
            (inst or :byte result other-pointer-lowtag)))
        (store-originating-pc result)
        (inst push result)) ; save the pointer to the shadow bits
      NO-SHADOW-BITS
      ;; The LET generates instructions that needn't be pseudoatomic
      ;; so don't move it inside.
      ;; There are 3 possibilities for correctness of INSTRUMENT-ALLOC:
      ;; * If WORDS is not immediate, and ALLOC-TEMP is R12, then compute size
      ;;   into ALLOC-TEMP, use RESULT as the instrumentation temp.
      ;;   ALLOCATION receives: input = ALLOC-TEMP, output = RESULT, and no other temp
      ;; * If WORDS is not immediate and ALLOC-TEMP is not R12, then compute size
      ;;   into RESULT, use ALLOC-TEMP as the instrumentation temp.
      ;;   ALLOCATION receives: input = RESULT, output = RESULT, temp = ALLOC-TEMP.
      (multiple-value-bind (size-tn instrumentation-temp alloc-temp)
          (cond ((sc-is words immediate)
                 ;; If WORDS is immediate, then let INSTRUMENT-ALLOC choose its temp
                 (values (calc-size-in-bytes words nil) (list result temp) temp))
                ((location= temp r12-tn)
                 ;; Compute the size into TEMP, use RESULT for instrumentation.
                 ;; Don't give another temp to ALLOCATION, because its SIZE and temp
                 ;; can not be in the same register (which it AVERs).
                 (values (calc-size-in-bytes words temp) result nil))
                (t
                 ;; Compute the size into RESULT, use TEMP for instrumentation.
                 ;; ALLOCATION needs the temp register in this case,
                 ;; because input and output are in the same register.
                 (values (calc-size-in-bytes words result) temp temp)))
        (instrument-alloc (if (sc-is type immediate)
                              (case (tn-value type)
                                (#.simple-vector-widetag 'simple-vector)
                                (t 'unboxed-array))
                              type)
                          size-tn instrumentation-temp)
        (allocating ()
         (allocation type size-tn 0 result alloc-temp)
         (put-header result 0 type length t alloc-temp)
         (inst or :byte result other-pointer-lowtag)))
      #+ubsan
      (cond ((want-shadow-bits)
             (inst pop temp-reg-tn) ; restore shadow bits
             (storew temp-reg-tn result 1 other-pointer-lowtag))
            (poisoned ; uninitialized SIMPLE-VECTOR
             (store-originating-pc result)))))

  (define-vop (allocate-vector-on-stack)
    #+ubsan (:info poisoned)
    (:args (type :scs (unsigned-reg immediate))
           (length :scs (any-reg (immediate
                                  (typep (fixnumize (tn-value tn))
                                         '(signed-byte 32)))))
           (words :scs (any-reg (immediate
                                 (typep (pad-data-block (+ (tn-value tn) vector-data-offset))
                                        'sc-offset)))))
    (:results (result :scs (descriptor-reg) :from :load))
    (:temporary (:sc unsigned-reg) bytes)
    (:node-var node)
    (:vop-var vop)
    (:arg-types #+ubsan (:constant t)
                positive-fixnum positive-fixnum positive-fixnum)
    #+ubsan (:temporary (:sc any-reg :offset rax-offset) rax)
    #+ubsan (:temporary (:sc any-reg :offset rcx-offset) rcx)
    #+ubsan (:temporary (:sc any-reg :offset rdi-offset) rdi)
    (:policy :fast-safe)
    (:generator 10
      #+ubsan
      (when (want-shadow-bits)
        ;; allocate a vector of "written" bits unless the vector is simple-vector-T,
        ;; which can use unbound-marker as a poison value on reads.
        (when (sc-is type unsigned-reg) (bug "vector-on-stack: unknown type"))
        (zeroize rax)
        (let ((nbytes (calc-shadow-bits-size rcx)))
          (stack-allocation nbytes 0 rdi)
          (when (sc-is length immediate) (inst mov rcx nbytes)))
        (inst rep)
        (inst stos :byte) ; RAX was zeroed
        (inst lea rax (ea other-pointer-lowtag rsp-tn))
        (inst mov :dword (ea (- other-pointer-lowtag) rax) simple-bit-vector-widetag)
        (inst mov :dword (vector-len-ea rax)
              (if (sc-is length immediate) (fixnumize (tn-value length)) length))
        (store-originating-pc rax))
      (let ((size (calc-size-in-bytes words bytes)))
        (when (sb-c::make-vector-check-overflow-p node)
          (generate-stack-overflow-check vop size))
        ;; Compute tagged pointer sooner than later since access off RSP
        ;; requires an extra byte in the encoding anyway.
        (stack-allocation size other-pointer-lowtag result
                          ;; If already aligned RSP, don't need to do it again.
                          #+ubsan (and (want-shadow-bits) :aligned-stack))
        ;; NB: store the trailing null BEFORE storing the header,
        ;; in case the length in words is 0, which stores into the LENGTH slot
        ;; as if it were element -1 of data (which probably can't happen).
        (store-string-trailing-null result type length words)
        (put-header result other-pointer-lowtag type length nil nil)
        )
      #+ubsan
      (cond ((want-shadow-bits)
             (storew rax result vector-length-slot other-pointer-lowtag))
            (poisoned ; uninitialized SIMPLE-VECTOR
             (store-originating-pc result)))))

  #+linux ; unimplemented for others
  (define-vop (allocate-vector-on-stack+msan-unpoison)
    #+ubsan (:info poisoned)
    #+ubsan (:ignore poisoned)
    (:args (type :scs (unsigned-reg immediate))
           (length :scs (any-reg immediate))
           (words :scs (any-reg immediate)))
    (:results (result :scs (descriptor-reg) :from :load))
    (:arg-types #+ubsan (:constant t)
                positive-fixnum positive-fixnum positive-fixnum)
    ;; This is a separate vop because it needs more temps.
    (:temporary (:sc any-reg :offset rcx-offset) rcx)
    (:temporary (:sc any-reg :offset rax-offset) rax)
    (:temporary (:sc any-reg :offset rdi-offset) rdi)
    (:temporary (:sc unsigned-reg) bytes)
    (:node-var node)
    (:vop-var vop)
    (:policy :fast-safe)
    (:generator 10
      (let ((size (calc-size-in-bytes words bytes)))
        ;; Compute tagged pointer sooner than later since access off RSP
        ;; requires an extra byte in the encoding anyway.
        (stack-allocation size other-pointer-lowtag result)
        (store-string-trailing-null result type length words)
        (when (sb-c::make-vector-check-overflow-p node)
          (generate-stack-overflow-check vop size))
        (put-header result other-pointer-lowtag type length nil nil)
        (cond ((sc-is words immediate)
               (inst mov rcx (+ (tn-value words) vector-data-offset)))
              (t
               (inst lea rcx (ea (ash vector-data-offset n-fixnum-tag-bits) words))
               (inst shr rcx n-fixnum-tag-bits)))
        (inst mov rdi msan-mem-to-shadow-xor-const)
        (inst xor rdi rsp-tn) ; compute shadow address
        (zeroize rax)
        (inst rep)
        (inst stos :qword)))))

;;; ALLOCATE-LIST
(macrolet ((calc-size-in-bytes (length answer)
             `(cond ((sc-is ,length immediate)
                     (aver (/= (tn-value ,length) 0))
                     (* (tn-value ,length) n-word-bytes 2))
                    (t
                     (inst mov result null-tn)
                     (inst test ,length ,length)
                     (inst jmp :z done)
                     (inst lea ,answer
                           (ea nil ,length
                               (ash 1 (1+ (- word-shift n-fixnum-tag-bits)))))
                     ,answer)))
           (test-for-empty-list (length)
             `(progn (inst mov result null-tn)
                     (inst test ,length ,length)
                     (inst jmp :z done)
                     ,length))
           (compute-end ()
             `(let ((size (cond ((typep size '(or (signed-byte 32) tn))
                                 size)
                                (t
                                 (inst mov limit size)
                                 limit))))
                (inst lea limit
                      (ea (if (fixnump size) size 0) result
                          (if (fixnump size) nil size))))))

  (define-vop (allocate-list-on-stack)
    (:args (length :scs (any-reg (immediate
                                  (typep (* (tn-value tn) n-word-bytes 2) 'sc-offset))))
           (element :scs (any-reg descriptor-reg)))
    (:results (result :scs (descriptor-reg) :from :load))
    (:arg-types positive-fixnum *)
    (:policy :fast-safe)
    (:node-var node)
    (:vop-var vop)
    (:temporary (:sc unsigned-reg) bytes)
    (:temporary (:sc descriptor-reg) tail next limit)
    (:generator 20
      (let ((size (calc-size-in-bytes length bytes))
            (loop (gen-label)))
        (when (sb-c::make-list-check-overflow-p node)
          (generate-stack-overflow-check vop size))
        (stack-allocation size list-pointer-lowtag result)
        (compute-end)
        (inst mov next result)
        (emit-label LOOP)
        (inst mov tail next)
        (inst add next (* 2 n-word-bytes))
        (storew element tail cons-car-slot list-pointer-lowtag)
        ;; Store the CDR even if it will be smashed to nil.
        (storew next tail cons-cdr-slot list-pointer-lowtag)
        (inst cmp next limit)
        (inst jmp :ne loop)
        (storew null-tn tail cons-cdr-slot list-pointer-lowtag))
      done))

  (define-allocator (allocate-list-on-heap)
    (:args (length :scs (any-reg immediate))
           ;; Too bad we don't have an SC that implies actually a CPU immediate
           ;; i.e. fits in an imm32 operand
           (element :scs (any-reg descriptor-reg)))
    (:results (result :scs (descriptor-reg) :from :load))
    (:arg-types positive-fixnum *)
    (:policy :fast-safe)
    (:temporary (:sc descriptor-reg) tail next limit)
    (:generator 20
      (multiple-value-bind (size scale)
          ;; Multiply by 8 in ALLOCATION, not here, if possible.
          (if (and (sc-is length any-reg) (not (instrument-alloc-policy-p node)))
              (values (test-for-empty-list length) 8)
              (values (calc-size-in-bytes length tail) nil))
        (instrument-alloc +cons-primtype+ size (list next limit))
        (allocating ()
         (allocation +cons-primtype+ size list-pointer-lowtag result limit
                     :scale scale
                     :overflow
                     (lambda ()
                       ;; Push C call args right-to-left
                       (list-ctor-push-elt element limit)
                       (list-ctor-push-elt length limit)
                       (invoke-asm-routine
                        'call (if (system-tlab-p 0 node) 'sys-make-list 'make-list) node)
                       (inst pop result)
                       (inst jmp alloc-done)))
         (if scale (inst lea limit (ea result length 8)) (compute-end))
         (inst mov next result)
         (inst jmp entry)
         LOOP
         (storew next tail cons-cdr-slot list-pointer-lowtag)
         ENTRY
         (inst mov tail next)
         (inst add next (* 2 n-word-bytes))
         (storew element tail cons-car-slot list-pointer-lowtag)
         (inst cmp next limit)
         (inst jmp :ne loop)
         ;; still pseudo-atomic
         (storew null-tn tail cons-cdr-slot list-pointer-lowtag)
         ALLOC-DONE))
      done))) ; label needed by calc-size-in-bytes

(define-allocator (make-fdefn)
  (:policy :fast-safe)
  (:translate make-fdefn)
  (:args (name :scs (descriptor-reg) :to :eval))
  (:results (result :scs (descriptor-reg) :from :argument))
  (:generator 37
    (alloc-other fdefn-widetag fdefn-size result nil
      (lambda () (storew name result fdefn-name-slot other-pointer-lowtag)))))

(define-allocator (make-closure)
  (:info label length stack-allocate-p)
  (:temporary (:sc any-reg) temp)
  (:results (result :scs (descriptor-reg)))
  (:vop-var vop)
  (:generator 10
    (let* ((words (+ length closure-info-offset)) ; including header
           (bytes (pad-data-block words))
           (header (logior (ash (1- words) n-widetag-bits) closure-widetag))
           (remain-pseudo-atomic
            (eq (car (last (vop-codegen-info vop))) :pseudo-atomic)))
      (unless stack-allocate-p
        (instrument-alloc closure-widetag bytes (list result temp)))
      (allocating (:default-exit (not remain-pseudo-atomic)
                   :elide-if stack-allocate-p)
        (if stack-allocate-p
            (stack-allocation bytes 0 result stack-allocate-p)
            (allocation closure-widetag bytes 0 result temp))
        (storew* #-compact-instance-header header ; write the widetag and size
                 #+compact-instance-header        ; ... plus the layout pointer
                 (let ((layout (static-constant-ea function-layout)))
                   (cond ((typep header '(unsigned-byte 16))
                          (inst mov temp layout)
                          ;; emit a 2-byte constant, the low 4 of TEMP were zeroed
                          (inst mov :word temp header))
                         (t
                          (inst mov temp header)
                          (inst or temp layout)))
                   temp)
                 result 0 0 (not stack-allocate-p))
        (inst lea temp (rip-relative-ea label (ash simple-fun-insts-offset word-shift)))
        (storew temp result closure-fun-slot 0)
        (inst or :byte result fun-pointer-lowtag)))))

(define-vop (reference-closure)
  (:info label)
  (:results (result :scs (descriptor-reg)))
  (:vop-var vop)
  (:generator 1
    (inst lea result (rip-relative-ea label fun-pointer-lowtag))))

;;; The compiler likes to be able to directly make value cells.
(define-allocator (make-value-cell)
  (:args (value :scs (descriptor-reg any-reg) :to :result
                :load-if (not (reg-or-legal-imm32-p value))))
  (:results (result :scs (descriptor-reg) :from :eval))
  (:generator 10
    (alloc-other value-cell-widetag value-cell-size result nil
      (lambda ()
        (storew (encode-value-if-immediate value)
                result value-cell-value-slot other-pointer-lowtag)))))

;;;; automatic allocators for primitive objects

(flet
  ((alloc (vop thread-temp name words type lowtag stack-allocate-p result alloc-temp
                    &aux (node (sb-c::vop-node vop))
                         (bytes (pad-data-block words))
                         (remain-pseudo-atomic
                          (eq (car (last (vop-codegen-info vop))) :pseudo-atomic)))
    #+bignum-assertions
    (when (eq type bignum-widetag) (setq bytes (* bytes 2))) ; use 2x the space
    (progn name) ; possibly not used
    (unless stack-allocate-p
      (emit-instrument-alloc node thread-temp type bytes (list result alloc-temp)))
    (allocating (:default-exit (not remain-pseudo-atomic) :elide-if stack-allocate-p)
      ;; If storing a header word, defer ORing in the lowtag until after
      ;; the header is written so that displacement can be 0.
      (cond (stack-allocate-p
             (stack-allocation bytes (if type 0 lowtag) result))
            ((eql type funcallable-instance-widetag)
             (inst push bytes)
             (invoke-asm-routine 'call 'alloc-funinstance vop)
             (inst pop result))
            (t
             (emit-allocation node thread-temp
                              type bytes (if type 0 lowtag) result alloc-temp)))
      (let ((header (compute-object-header words type)))
        (cond #+compact-instance-header
              ((and (eq name '%make-structure-instance) stack-allocate-p)
              ;; Write a :DWORD, not a :QWORD, because the high half will be
              ;; filled in when the layout is stored. Can't use STOREW* though,
              ;; because it tries to store as few bytes as possible,
              ;; where this instruction must write exactly 4 bytes.
               (inst mov :dword (ea 0 result) header))
              (t
               (storew* header result 0 0 (not stack-allocate-p)))))
      ;; GC can make the best choice about placement if it has a layout.
      ;; Of course with conservative GC the object will be pinned anyway,
      ;; but still, always having a layout is a good thing.
      (when (typep type 'layout) ; store its layout, while still in pseudo-atomic
        (inst mov :dword (ea 4 result) (make-fixup type :layout)))
      (inst or :byte result lowtag))))
  ;; DX is strictly redundant in these 2 vops, but they're written this way
  ;; so that backends can choose to use a single vop for both.
  (define-vop (fixed-alloc)
    (:info name words type lowtag dx)
    (:results (result :scs (descriptor-reg)))
    (:temporary (:sc unsigned-reg) alloc-temp)
    (:vop-var vop)
    (:generator 50 (alloc vop thread-tn name words type lowtag dx result alloc-temp)))
  (define-vop (sb-c::fixed-alloc-to-stack)
    (:info name words type lowtag dx)
    (:results (result :scs (descriptor-reg)))
    (:vop-var vop)
    (:generator 50 (alloc vop thread-tn name words type lowtag dx result nil))))

;;; Allocate a non-vector variable-length object.
;;; Exactly 4 allocators are rendered via this vop:
;;;  BIGNUM               (%ALLOCATE-BIGNUM)
;;;  FUNCALLABLE-INSTANCE (%MAKE-FUNCALLABLE-INSTANCE)
;;;  CLOSURE              (%ALLOC-CLOSURE)
;;;  INSTANCE             (%MAKE-INSTANCE,%MAKE-INSTANCE/MIXED)
;;; WORDS accounts for the mandatory slots *including* the header.
;;; EXTRA is the variable payload, also measured in words.
(define-allocator (var-alloc)
  (:args (extra :scs (any-reg)))
  (:arg-types positive-fixnum)
  (:info name words type lowtag stack-allocate-p)
  (:results (result :scs (descriptor-reg) :from (:eval 1)))
  (:temporary (:sc unsigned-reg :from :eval :to (:eval 1)) bytes)
  (:temporary (:sc unsigned-reg :from :eval :to :result) header)
  ;; KLUDGE: wire to RAX so that it doesn't get R12
  (:temporary (:sc unsigned-reg :offset 0) alloc-temp)
  (:vop-var vop)
  (:generator 50
   (when (eq name '%make-funcallable-instance)
     ;; %MAKE-FUNCALLABLE-INSTANCE needs to allocate to pages of code,
     ;; which it failed to do if the var-alloc translation was invoked.
     ;; But it seems we never need this! (so is it FIXME or isn't it?)
     (error "can't %MAKE-FUNCALLABLE-INSTANCE of unknown length"))
   (let ((remain-pseudo-atomic (eq (car (last (vop-codegen-info vop))) :pseudo-atomic)))
   ;; With the exception of bignums, these objects have effectively
   ;; 32-bit headers because the high 4 byes contain a layout pointer.
     (let ((operand-size (if (= type bignum-widetag) :qword :dword)))
       (inst lea operand-size bytes
             (ea (* (1+ words) n-word-bytes) nil
                 extra (ash 1 (- word-shift n-fixnum-tag-bits))))
       (inst mov operand-size header bytes)
       (inst shl operand-size header (- (length-field-shift type) word-shift)) ; w+1 to length field
       (inst lea operand-size header                    ; (w-1 << 8) | type
             (ea (+ (ash -2 (length-field-shift type)) type) header))
       (inst and operand-size bytes (lognot lowtag-mask)))
     #+bignum-assertions
     (when (= type bignum-widetag) (inst shl :dword bytes 1)) ; use 2x the space
     (cond (stack-allocate-p
             (stack-allocation bytes lowtag result)
             (storew header result 0 lowtag))
           (t
             ;; can't pass RESULT as a possible choice of scratch register
             ;; because it might be in the same physical reg as BYTES.
             ;; Yup, the lifetime specs in this vop are pretty confusing.
             (instrument-alloc type bytes alloc-temp)
             (allocating (:default-exit (not remain-pseudo-atomic))
              (allocation type bytes lowtag result alloc-temp)
              (storew header result 0 lowtag)))))))

#+sb-xc-host
(define-vop (alloc-code)
  (:args (total-words :scs (unsigned-reg) :target c-arg-1)
         (boxed-words :scs (unsigned-reg) :target c-arg-2))
  (:temporary (:sc unsigned-reg
               :offset #.(first *c-call-register-arg-offsets*)
               :from (:argument 0) :to :result) c-arg-1)
  (:temporary (:sc unsigned-reg :offset rsi-offset
               :offset #.(second *c-call-register-arg-offsets*)
               :from (:argument 1) :to :result) c-arg-2)
  (:temporary (:sc unsigned-reg :offset r15-offset) dummy)
  (:results (res :scs (descriptor-reg)))
  (:ignore dummy)
  (:generator 1
    (move c-arg-1 total-words)
    (move c-arg-2 boxed-words)
    (with-registers-preserved (c :except #-win32 rdi #+win32 rcx :frame-reg r15)
      (allocating () (call-c "alloc_code_object"))
      (move c-arg-1 rax-tn))
    (move res c-arg-1)))

#+(and sb-xc-host immobile-space)
(define-vop (alloc-immobile-fixedobj)
  (:args (size-class :scs (any-reg) :target c-arg1)
         (nwords :scs (any-reg) :target c-arg2)
         (header :scs (any-reg) :target c-arg3))
  (:temporary (:sc unsigned-reg :from (:argument 0) :to :eval
               :offset #.(first *c-call-register-arg-offsets*)) c-arg1)
  (:temporary (:sc unsigned-reg :from (:argument 1) :to :eval
               :offset #.(second *c-call-register-arg-offsets*)) c-arg2)
  (:temporary (:sc unsigned-reg :from (:argument 2) :to :eval
               :offset #.(third *c-call-register-arg-offsets*)) c-arg3)
  (:temporary (:sc unsigned-reg :from :eval :to (:result 0) :offset rax-offset) rax)
  (:results (result :scs (descriptor-reg)))
  (:generator 50
   (inst mov c-arg1 size-class)
   (inst mov c-arg2 nwords)
   (inst mov c-arg3 header)
   ;; RSP needn't be restored because the allocators all return immediately
   ;; which has that effect
   (inst and rsp-tn -16)
   (allocating ()
     (call-c "alloc_immobile_fixedobj")
     (move result rax))))

;;; Timing test:
;;; Dynamic-space allocation:
;;; * (defun f (n) (dotimes (i n) (make-symbol "b")))
;;; * (time (f 500000))
;;; Evaluation took: 0.004 seconds of real time
;;; Immobile-space:
;;; * (defun f (n) (dotimes (i n) (sb-vm::%alloc-immobile-symbol "b")))
;;; Evaluation took: 0.043 seconds of real time
;;; With vop:  0.028 seconds of real time

(eval-when (:compile-toplevel)
  (aver (evenp symbol-size))) ; assumptions in the code below

(define-vop (!fast-alloc-immobile-symbol)
  (:results (result :scs (descriptor-reg)))
  (:temporary (:sc unsigned-reg :offset rax-offset) rax)
  (:temporary (:sc unsigned-reg :offset rbx-offset) rbx)
  (:temporary (:sc unsigned-reg :offset rcx-offset) rcx)
  (:temporary (:sc unsigned-reg) header)
  (:generator 1
    ;; fixedobj_pages alien linkage entry: 1 PTE per page, 12-byte struct
    (inst mov rbx (rip-relative-ea (make-fixup "fixedobj_pages" :foreign-dataref)))
    ;; fixedobj_page_hint: 1 hint per sizeclass. C type = uint32_t
    (inst mov rax (rip-relative-ea (make-fixup "fixedobj_page_hint" :foreign-dataref)))
    (inst mov rbx (ea rbx)) ; get the base of the fixedobj_pages array
    ;; This has to be pseudoatomic as soon as the page hint is loaded.
    ;; Consider the situation where there is exactly one symbol on a page that
    ;; is almost all free, and the symbol page hint points to that page.
    ;; If GC occurs, it might dispose that symbol, resetting the page attributes
    ;; and page hint. It would be an error to allocate to that page
    ;; because it is no longer a page of symbols but rather a free page.
    ;; There is no way to inform GC that we are currently looking at a page
    ;; in anticipation of allocating to it.
    (allocating ()
       (inst mov :dword rax (ea 4 rax)) ; rax := fixedobj_page_hint[1] (sizeclass=SYMBOL)
       (inst test :dword rax rax)
       (inst jmp :z FAIL) ; fail if hint page is 0
       (inst lea rbx (ea rbx rax 8))  ; rbx := &fixedobj_pages[hint].free_index
       ;; compute fixedobj_page_address(hint) into RAX
       (inst mov rcx (rip-relative-ea (make-fixup "FIXEDOBJ_SPACE_START" :foreign-dataref)))
       (inst shl rax (integer-length (1- immobile-card-bytes)))
       (inst add rax (ea rcx))
       ;; load the page's free pointer
       (inst mov :dword rcx (ea rbx)) ; rcx := fixedobj_pages[hint].free_index
       ;; fail if allocation would overrun the page
       (inst cmp :dword rcx (- immobile-card-bytes (* symbol-size n-word-bytes)))
       (inst jmp :a FAIL)
       ;; compute address of the allegedly free memory block into RESULT
       (inst lea result (ea rcx rax)) ; free_index + page_base
       ;; read the potential symbol header
       (inst mov rax (ea result))
       (inst test :dword rax 1)
       (inst jmp :nz FAIL) ; not a fixnum implies already taken
       ;; try to claim this word of memory
       (inst mov header (compute-object-header (1- symbol-size) symbol-widetag))
       (inst cmpxchg :lock (ea result) header)
       (inst jmp :ne FAIL) ; already taken
       ;; compute new free_index = spacing + old header + free_index
       (inst lea :dword rax (ea (* symbol-size n-word-bytes) rax rcx))
       (inst mov :dword (ea rbx) rax) ; store new free_index
       ;; set the low bit of the 'gens' field
       (inst or :lock :byte (ea 7 rbx) 1) ; 7+rbx = &fixedobj_pages[i].attr.parts.gens_
       (inst or :byte result other-pointer-lowtag) ; make_lispobj()
       (inst jmp OUT)
       FAIL
       (inst mov result null-tn)
       OUT)))
