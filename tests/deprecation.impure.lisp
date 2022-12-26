;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; While most of SBCL is derived from the CMU CL system, the test
;;;; files (like this one) were written from scratch after the fork
;;;; from CMU CL.
;;;;
;;;; This software is in the public domain and is provided with
;;;; absolutely no warranty. See the COPYING and CREDITS files for
;;;; more information.


;;;; Helpers

(defun test (namespace name state make-body
                               &key replacements
                                    (call t)
                                    (expected-warning-count '(eql 1))
                                    (check-describe t))
  (labels ((search-string (string fragments)
             (let ((start))
               (dolist (fragment fragments)
                 (let ((match (search fragment string :start2 (or start 0))))
                   (assert match)
                   (setf start (+ match (length fragment)))))))
           (search-string/documentation (string)
             (search-string
              string `(,(string-downcase namespace) ,(string name)
                        "deprecated" "as" "of" "some-lib" "version" "1.2.3"))
             (when replacements
               (search-string string `("Use" ,@replacements "instead"))))
           (search-string/describe (string)
             (search-string
              string `(,(string name) ,(string state)
                        "deprecation" "since" "some-lib" "version" "1.2.3"))))
    ;; Check the signaled warning condition.
    (multiple-value-bind (function failure-p warnings style-warnings)
        (checked-compile `(lambda () ,@(funcall make-body name))
                         :allow-style-warnings t ; undefined types, functions
                         :allow-warnings 'deprecation-condition)
      (declare (ignore failure-p))
      (let* ((conditions (remove-if-not
                          (lambda (condition)
                            (typep condition 'deprecation-condition))
                          (append warnings style-warnings)))
             (condition (first conditions))
             (count (length conditions)))
        (assert (typep count expected-warning-count))
        (when condition
          (assert (typep condition (ecase state
                                     (:early 'early-deprecation-warning)
                                     (:late 'late-deprecation-warning)
                                     (:final 'final-deprecation-warning))))
          (search-string/documentation (princ-to-string condition)))
        (when call
          (ecase state
            ((:early :late)
             (assert (eq :deprecated (funcall function))))
            (:final
             (assert-error (funcall function)
                           (or deprecation-error cell-error)))))))
    ;; Check DESCRIBE output.
    (when check-describe
      (search-string/describe (with-output-to-string (stream)
                                (describe name stream))))
    ;; Check DOCUMENTATION.
    (search-string/documentation (documentation name namespace))))

(with-test (:name (deprecated type :unrelated-class))
    (let ((name (gensym)))
      (eval `(progn
               (deftype ,name () 'integer)
               (declaim (deprecated :early ("some-lib" "1.2.3") (type ,name)))))
      ;; Make sure the deprecation declaration works.
      (test
       'type name :early
       (lambda (name)
         `((typep 1 ',name)))
       :call nil)
      ;; Check that the declaration does not apply to an unrelated class
      ;; of the same name.
      (test
       'type name :early
       (lambda (name)
         `((make-instance ,(make-instance 'standard-class :name name))))
       :call                   nil
       :expected-warning-count '(eql 0))))
