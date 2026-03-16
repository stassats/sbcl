(defstruct s1 a)
(defstruct s2 a b)

(defvar *obj1* (make-s1))
(defvar *obj2* (make-s2))
(defvar *addr1* (sb-kernel:get-lisp-obj-address *obj1*))
(defvar *addr2* (sb-kernel:get-lisp-obj-address *obj2*))
(defvar *len1* (sb-kernel:%instance-length *obj1*))
(defvar *len2* (sb-kernel:%instance-length *obj2*))
(defvar *h1* (sxhash *obj1*))
(defvar *h2* (sxhash *obj2*))
(defvar *primsize1* (primitive-object-size *obj1*))
(defvar *primsize2* (primitive-object-size *obj2*))

(with-test (:name :lazy-hash-slot-instance-length-invariant)
  (gc)
  ;; both should have moved
  (assert (/= (sb-kernel:get-lisp-obj-address *obj1*) *addr1*))
  (assert (/= (sb-kernel:get-lisp-obj-address *obj2*) *addr2*))
  ;; both should have kept their pseudorandom address-based hash
  (assert (= (sxhash *obj1*) *h1*))
  (assert (= (sxhash *obj2*) *h2*))
  ;; should not have changed the instance length
  (assert (= (sb-kernel:%instance-length *obj1*) *len1*))
  (assert (= (sb-kernel:%instance-length *obj2*) *len2*))
  ;; one or the other but not both should be physically larger
  (let ((grown1 (> (primitive-object-size *obj1*) *primsize1*))
        (grown2 (> (primitive-object-size *obj2*) *primsize2*)))
    (assert (and (or grown1 grown2)
                 (not (and grown1 grown2))))))
