(with-test (:name :many-packages) ; was blowing up in fun-name-hashset
  (with-scratch-file (sourcefile "lisp")
    (with-open-file (out sourcefile :direction :output)
      (dotimes (i 1200)
        (format out "(defpackage #:pkg~d (:use #:cl))
(in-package #:pkg~d)
(defun initme () ~d)~%" i i i)))
    (with-scratch-file (fasl "fasl")
      (compile-file sourcefile :output-file fasl))))
