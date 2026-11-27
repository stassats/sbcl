"Line: 8, Column: 22, File-Position: 108" ; expect this
#|
 More randomness
|#


;;;
(progn (defvar *foo* #[ hi ]) x)
                   ;; ^ NO SUCH MACRO
