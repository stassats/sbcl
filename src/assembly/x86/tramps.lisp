;;;; Undefined-function and closure trampoline definitions

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.

(in-package "SB!VM")

(define-assembly-routine
    (undefined-tramp (:return-style :none))
    ()
  (inst pop (make-ea :dword :base ebp-tn :disp 4))
  (error-call nil 'undefined-fun-error
              ;; We can't just use EAX-TN because the SC is wrong.
              (make-random-tn :kind :normal
                              :sc (sc-or-lose 'descriptor-reg)
                              :offset eax-offset))
  (inst ret))

(define-assembly-routine
    (closure-tramp (:return-style :none))
    ()
  (loadw eax-tn eax-tn fdefn-fun-slot other-pointer-lowtag)
  (inst jmp (make-ea-for-object-slot eax-tn closure-fun-slot fun-pointer-lowtag)))
