(in-package :cl-user)
(sb-int:set-floating-point-modes  :traps '(:overflow  :invalid :divide-by-zero))
(sb-ext:defglobal *compilation-count* 0)
(declaim (fixnum *compilation-count*))
(declaim (optimize (sb-c::store-source-form 0)
                   (sb-c::store-xref-data 0)))

(defvar *thread* 0)
(defvar *save* nil)
(defvar *check-return-type* t)
(defvar *the* t)
;;; ================================================================
;;; 1. CONFIGURATION & GRAMMAR
;;; ================================================================
(defvar *integer-types* '(integer fixnum
                          (unsigned-byte #.sb-vm:n-word-bits)
                          (signed-byte #.sb-vm:n-word-bits)
                          (and fixnum unsigned-byte)
                          (integer * 0)
                          (integer * -1)
                          (integer 1)
                          unsigned-byte
                          (and fixnum (integer * 0))
                          (and fixnum (integer * -1))
                          (and fixnum (integer * -1))
                          (and fixnum (integer 1))))

(defparameter *types* (list* 'boolean *integer-types*))
(defvar *number-types*)
(defparameter *max-depth* 7)

(defvar *number-ops*
  '((+   (number number) number)
    (-   (number number) number)
    (-   (number) number)
    (*   (number number) number)
    (/   (number number) number)

    (truncate (number) integer)
    (ceiling (number) integer)
    (floor (number) integer)
    (round (number) integer)
    (mod (number) number)
    (rem (number) number)

    (ffloor (number) number)
    (ftruncate (number) number)
    (fceiling (number) number)
    (fround (number) number)

    (scale-float (number integer) number)
    (integer-decode-float (number) number)
    (decode-float (number) number)
    (float-precision (number) integer)
    (float-sign (number) number)
    (float-sign (number number) number)

    (max (number number) number)
    (min (number number) number)
    (abs (number) number)

    (sin (number) number)
    (cos (number) number)
    (tan (number) number)
    (atan (number) number)
    (atan (number number) number)
    (acos (number) number)
    (asin (number) number)
    (sinh (number) number)
    (cosh (number) number)
    (tanh (number) number)
    (asinh (number) number)
    (acosh (number) number)
    (atanh (number) number)

    (expt (number number) number)
    (exp (number) number)
    (log (number) number)
    (log (number number) number)

    ;; (expt (integer number) number)
    (exp (integer) number)
    (log (integer) number)
    (log (integer number) number)
    (signum (number) number)
    (cis (number) number)
    (complex (number) number)
    (conjugate (number) number)
    (phase (number) number)
    (realpart (number) number)
    (imagpart (number) number)

    (numerator (number) number)
    (denominator (number) number)

    (rational (number) number)
    (rationalize (number) number)

    (+   (number integer) number)
    (-   (number integer) number)
    (*   (number integer) number)
    (/   (number integer) number)

    (>   (number number) boolean)
    (<   (number number) boolean)
    (>=   (number number) boolean)
    (<=   (number number) boolean)
    (=   (number number) boolean)
    (/=   (number number) boolean)
    (eql   (number number) boolean)
    (equal   (number number) boolean)
    (equalp   (number number) boolean)
    (sqrt (number) number)))

(defvar *float-ops*
  '((+   (float float) float)
    (-   (float float) float)
    (-   (float) float)
    (*   (float float) float)
    (/   (float float) float)
    (truncate (float float) integer)
    (ceiling (float float) integer)
    (round (float float) integer)

    (ffloor (float float) float)
    (ftruncate (float float) float)
    (fceiling (float float) float)
    (fround (float float) float)

    (truncate (float) integer)
    (ceiling (float) integer)
    (round (float) integer)

    (ffloor (float) float)
    (ftruncate (float) float)
    (fceiling (float) float)
    (fround (float) float)

    (max (float float) float)
    (min (float float) float)
    (abs (float) float)

    (sin (float) float)
    (sin (integer) float)
    (cos (float) float)
    (cos (integer) float)

    (expt (float float) number)
    (exp (float) number)
    (log (float) number)
    (log (float float) number)

    (expt (integer float) number)
    (exp (integer) number)
    (log (integer) number)
    (log (integer float) number)

    (+   (float integer) float)
    (-   (float integer) float)
    (*   (float integer) float)
    (/   (float integer) float)

    (>   (float float) boolean)
    (<   (float float) boolean)))

(defparameter *noise-ops*
  '((unwind-protect (t t) t)
    (unwind-protect (t) t)
    (catch (t t) t)
    (values (t) t)
    (values (t t) t)
    (values (t t t) t)
    (values (t t t t) t)
    (values (t t t t t) t)
    (progn (t t) t)
    (prog1 (t t) t)
    (list (t) t)))

(defvar *ratio-ops*
  '((+   (rational rational) rational)
    (-   (rational rational) rational)
    (-   (rational) rational)
    (*   (rational rational) rational)
    (/   (rational rational) rational)

    (truncate (rational rational) integer)
    (ceiling (rational rational) integer)
    (round (rational rational) integer)

    (ffloor (rational rational) rational)
    (ftruncate (rational rational) rational)
    (fceiling (rational rational) rational)
    (fround (rational rational) rational)
    (ffloor (rational rational) rational)

    (truncate (rational) integer)
    (ceiling (rational) integer)
    (round (rational) integer)

    (ffloor (rational) rational)
    (ftruncate (rational) rational)
    (fceiling (rational) rational)
    (fround (rational) rational)
    (ffloor (rational) rational)

    (max (rational rational) rational)
    (min (rational rational) rational)
    (abs (rational) rational)

    (sin (rational) single-float)
    (sin (integer) single-float)
    (cos (rational) single-float)
    (cos (integer) single-float)

    (expt (rational (integer -100 100)) number)
    (exp (rational) number)
    (log (rational) number)
    (log (rational rational) number)

    (exp (integer) number)
    (log (integer) number)
    (log (integer rational) number)
    (isqrt (integer) integer)
    (+   (rational integer) rational)
    (-   (rational integer) rational)
    (*   (rational integer) rational)
    (/   (rational integer) rational)

    (>   (rational rational) boolean)
    (<   (rational rational) boolean)))

(defmacro %ldb (size pos i)
  `(ldb (byte (the sb-bignum:bit-index ,size) (the sb-bignum:bit-index ,pos)) ,i))

(defmacro %dpb (n size pos i)
  `(dpb ,n (byte (the sb-bignum:bit-index ,size) (the sb-bignum:bit-index ,pos)) ,i))

(defparameter *operators*
  `(;; Integer
    (+   (integer integer)     integer)
    (-   (integer integer)     integer)
    (-   (integer)     integer)
    (*   (integer integer)     integer)
    (truncate (integer integer) integer)
    (floor (integer integer) integer)
    (ceiling (integer integer) integer)
    (round (integer integer) integer)

    (logand (integer integer) integer)
    (logxor (integer integer) integer)
    (logior (integer integer) integer)
    (lognot (integer) integer)
    (logtest (integer integer) boolean)
    (integer-length (integer) integer)
    (logcount (integer) integer)
    (max (integer integer) integer)
    (min (integer integer) integer)
    (abs (integer) integer)
    (evenp (integer) boolean)
    (oddp (integer) boolean)
    (ash (integer (integer -256 256)) integer)
    (%ldb ((integer 0 256) (integer 0 256) integer) integer)
    (%dpb (integer (integer 0 256) (integer 0 256) integer) integer)

    (gcd (integer integer) integer)
    ;; Comparison
    (>   (integer integer)           boolean)
    (<   (integer integer)           boolean)
    (=   (integer integer)           boolean)


    ;; Logic
    (and (boolean boolean) boolean)
    (or  (boolean boolean) boolean)
    (not (boolean)         boolean)))

;;; ================================================================
;;; 2. GENERATOR
;;; ================================================================

(defun random-elt (seq)
  (if (null seq) nil (elt seq (random (length seq)))))


(defun get-ops (ret-type)
  (when (member ret-type *integer-types* :test #'eq)
    (setf ret-type 'integer))
  (remove-if-not (lambda (x) (eq (third x) ret-type)) *operators*))

(defun get-vars (ret-type schema)
  (mapcar #'car (remove-if-not (lambda (x) (eq (cdr x) ret-type)) schema)))

(defconstant max-integer (1- sb-vm:n-fixnum-bits))

(defun random-const (type)
  (case type
    (number (random-const (random-elt *number-types*)))
    (real (random-const (random-elt '(rational float))))
    (integer (* (if (< (random 100) 30)
                    (random 100)
                    (random (expt 2 max-integer)))
                (if (zerop (random 2)) 1 -1)))
    (unsigned-byte (if (< (random 100) 30)
                       (random 100)
                       (random (expt 2 max-integer))))
    (float
     (random-const (random-elt '(double-float single-float))))
    (single-float (* (if (zerop (random 10))
                         (random-elt (load-time-value (list most-positive-single-float least-positive-single-float
                                                            sb-ext:single-float-positive-infinity (coerce pi 'single-float)
                                                            (exp 1))))
                         (if (zerop (random 2))
                             (float (random (expt 2 64)) 1f0)
                             (scale-float 1f0 (random 100))))
                     (if (zerop (random 2)) 1 -1)))
    (double-float (* (if (zerop (random 10))
                         (random-elt (load-time-value (list most-positive-double-float least-positive-double-float
                                                            sb-ext:double-float-positive-infinity pi
                                                            (exp 1d0))))
                         (if (zerop (random 2))
                             (float (random (expt 2 64)) 1d0)
                             (scale-float 1d0 (random 100))))
                     (if (zerop (random 2)) 1 -1)))
    (boolean      (if (zerop (random 2)) nil t))
    (fixnum (* (random (if (< (random 100) 50)
                           (1+ (random 100))
                           (expt 2 #.(1- sb-vm:n-fixnum-bits))))
               (if (zerop (random 2)) 1 -1)))
    (rational
     (if (< (random 100) 50)
         (random-const 'integer)
         (* (/ (1+ (random (expt 2 max-integer)))
               (1+ (random (expt 2 max-integer))))
            (if (zerop (random 2)) 1 -1))))
    (complex
     (random-const (random-elt '((complex rational) (complex single-float)
                                 (complex double-float)))))
    (t
     (cond ((equal type '(complex rational))
            (complex (random-const 'rational)
                     (loop for x = (random-const 'rational)
                           when (not (eq x 0))
                           return x)))
           ((equal type '(complex single-float))
            (complex (random-const 'single-float)
                     (random-const 'single-float)))
           ((equal type '(complex double-float))
            (complex (random-const 'double-float)
                     (random-const 'double-float)))
           ((equal type '(complex float))
            (let ((type (random-elt '(single-float double-float))))
              (complex (random-const type)
                       (random-const type))))
           ((equal type '(signed-byte #.sb-vm:n-word-bits))
               (* (if (< (random 100) 50)
                      (1+ (random 100))
                      (random (expt 2 #.(1- sb-vm:n-word-bits))))
                  (if (zerop (random 2)) 1 -1)))
           ((equal type '(unsigned-byte #.sb-vm:n-word-bits))
            (random (if (< (random 100) 50)
                        (1+ (random 100))
                        (expt 2 #.sb-vm:n-word-bits))))
           ((equal type '(and fixnum unsigned-byte))
            (random (if (< (random 100) 50)
                        (1+ (random 100))
                        (expt 2 #.(1- sb-vm:n-fixnum-bits)))))
           ((equal type '(integer * 0))
            (- (if (< (random 100) 30)
                   (random 100)
                   (random (expt 2 max-integer)))))
           ((equal type '(integer * -1))
            (- -1 (if (< (random 100) 30)
                      (random 100)
                      (random (expt 2 max-integer)))))
           ((equal type '(and fixnum (integer * -1)))
            (- -1 (if (< (random 100) 30)
                      (random 100)
                      (random (expt 2 #.(1- sb-vm:n-fixnum-bits))))))
           ((equal type '(and fixnum (integer * 0)))
            (- (if (< (random 100) 30)
                   (random 100)
                   (random (expt 2 #.(1- sb-vm:n-fixnum-bits))))))
           ((equal type '(and fixnum (integer 1)))
            (1+ (if (< (random 100) 30)
                    (random 100)
                    (random (1- (expt 2 #.(1- sb-vm:n-fixnum-bits)))))))
           ((equal type '(integer 1))
            (1+ (if (< (random 100) 30)
                    (random 100)
                    (random (expt 2 max-integer)))))
           ((typep type '(cons (eql integer)))
            (destructuring-bind (lo hi) (cdr type)
              (+ (random (1+ (- hi lo)))
                 lo)))))))

(defvar *noise* nil)
(defvar *blocks* nil)
(defvar *vars* nil)
(defvar *flets* nil)

(defun call (x)
  (funcall x))

(define-condition random-error (error) ())

;; (defun check-control-stack ()
;;   (declare (optimize speed))
;;   (let ((widetag-table
;;           (load-time-value
;;            (let ((table (make-array (ash 1 sb-vm:n-widetag-bits) :element-type '(unsigned-byte 8)
;;                                                                  :initial-element 0)))
;;              (loop for tag in sb-vm::(list BIGNUM-WIDETAG RATIO-WIDETAG SINGLE-FLOAT-WIDETAG DOUBLE-FLOAT-WIDETAG COMPLEX-RATIONAL-WIDETAG COMPLEX-SINGLE-FLOAT-WIDETAG COMPLEX-DOUBLE-FLOAT-WIDETAG
;;                                            SYMBOL-WIDETAG SAP-WIDETAG CODE-HEADER-WIDETAG INSTANCE-WIDETAG FUNCALLABLE-INSTANCE-WIDETAG SIMPLE-FUN-WIDETAG CLOSURE-WIDETAG LRA-WIDETAG-NOTUSED
;;                                            VALUE-CELL-WIDETAG CHARACTER-WIDETAG UNUSED00-WIDETAG WEAK-POINTER-WIDETAG FDEFN-WIDETAG UNUSED-WIDETAG UNUSED01-WIDETAG UNUSED03-WIDETAG FILLER-WIDETAG
;;                                            UNUSED04-WIDETAG UNUSED05-WIDETAG UNUSED06-WIDETAG UNUSED07-WIDETAG SIMPLE-ARRAY-WIDETAG SIMPLE-ARRAY-NIL-WIDETAG SIMPLE-VECTOR-WIDETAG
;;                                            SIMPLE-BIT-VECTOR-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-2-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-4-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-7-WIDETAG
;;                                            SIMPLE-ARRAY-UNSIGNED-BYTE-8-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-15-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-16-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-31-WIDETAG
;;                                            SIMPLE-ARRAY-UNSIGNED-BYTE-32-WIDETAG SIMPLE-ARRAY-UNSIGNED-FIXNUM-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-63-WIDETAG SIMPLE-ARRAY-UNSIGNED-BYTE-64-WIDETAG
;;                                            SIMPLE-ARRAY-SIGNED-BYTE-8-WIDETAG SIMPLE-ARRAY-SIGNED-BYTE-16-WIDETAG SIMPLE-ARRAY-SIGNED-BYTE-32-WIDETAG SIMPLE-ARRAY-FIXNUM-WIDETAG
;;                                            SIMPLE-ARRAY-SIGNED-BYTE-64-WIDETAG SIMPLE-ARRAY-SINGLE-FLOAT-WIDETAG SIMPLE-ARRAY-DOUBLE-FLOAT-WIDETAG SIMPLE-ARRAY-COMPLEX-SINGLE-FLOAT-WIDETAG
;;                                            SIMPLE-ARRAY-COMPLEX-DOUBLE-FLOAT-WIDETAG SIMPLE-BASE-STRING-WIDETAG SIMPLE-CHARACTER-STRING-WIDETAG COMPLEX-BASE-STRING-WIDETAG
;;                                            COMPLEX-CHARACTER-STRING-WIDETAG COMPLEX-BIT-VECTOR-WIDETAG COMPLEX-VECTOR-WIDETAG COMPLEX-ARRAY-WIDETAG UNUSED-ARRAY-WIDETAG)
;;                    do (setf (aref table tag) 1))
;;              table))))
;;     (flet ((is-immediate (val)
;;              (or (zerop (logand val sb-vm:fixnum-tag-mask))
;;                  #+64-bit
;;                  (= (logand val #xff) sb-vm:single-float-widetag)
;;                  (and (zerop (logandc2 val #x1fffffff))
;;                       (= (logand val #xff) sb-vm:character-widetag))
;;                  (= val sb-vm:unbound-marker-widetag)))
;;            (is-pointer (val)
;;              (= (logand val 3) 3))
;;            (widetag-p (val)
;;              (let ((byte (ldb (byte 8 0) val)))
;;                (eq (aref widetag-table byte) 1))))
;;       (loop for x from (ash (truly-the (unsigned-byte 63) sb-vm::*control-stack-start*) 1)
;;             to (- (ash (truly-the (and unsigned-byte fixnum) sb-vm::*control-stack-end*) 1)
;;                   (* 2 sb-c:+backend-page-bytes+)) by sb-vm:n-word-bytes
;;             for sap = (sb-sys:int-sap x)
;;             for val = (sb-sys:sap-ref-word sap 0)
;;             always (or (is-pointer val)
;;                        (is-immediate val)
;;                        (widetag-p val))))))

(defun generate-ast (type depth schema)
  (let ((terminals (unless (or (eq type 'boolean)
                               (= depth 0))
                     '(const)))
        (vars (unless (= depth 0)
                (get-vars type schema)))
        (funcs (get-ops type)))
    (when vars (push 'var terminals))
    (let* ((stop (>= depth *max-depth*))
           (options (or (if stop terminals (append terminals '(func if)))
                        '(func))))
      (when (and *noise*
                 (not stop))
        (push 'noise options)
        (push 'block options)
        (push 'nth-value options)
        (push 'let options)
        (push 'closure options)
        ;(push 'error options)
        ;(push 'bad-const options)
        (push 'loop options)
        ;(push 'flet options)
        ;(push 'stack options)
        (when *blocks*
          (push 'return-from options)))
      (when (and *the*
                 (not stop))
        (push 'the options)
        (push 'typecase options))
      (unless stop
        (push 'cond options))
      (flet ((gen-type ()
               `(or ,@(loop repeat (1+ (random 5))
                            for not = (zerop (random 2))
                            for type = (random-elt *types*)
                            collect (if not
                                        `(not ,type)
                                        type)))))
        (ecase (random-elt options)
 ;; (stack
          ;;  `(progn (assert (check-control-stack))
          ;;          ,(random-const type)))
          (const (random-const type))
          (bad-const
           ;; `(sb-sys:sap-ref-8 (sb-sys:int-sap 0) 0)
           `(call
             ',(if (zerop (random 2))
                   `(load-time-value
                     ,(random-elt '(t #\a #\b #\0
                                    "a" #() #(1)
                                    #*00 '(1 2)
                                    (make-hash-table)
                                    #p"a" #'max
                                    (let ((n 0))
                                      (call (lambda () (incf n)))
                                      (lambda () n))
                                    (find-class 'list))))
                   (random-const (random-elt (remove type *types* :test #'eq)))))
           )
          (loop
                `(loop repeat ,(random 10000)
                       while ,(generate-ast 'boolean (1+ depth) schema)
                       ,(if (subtypep type 'number)
                            'sum
                            'do)
                       (progn ,(let ((*blocks* (cons nil *blocks*)))
                                 (generate-ast type (1+ depth) schema)))))
          (var   (random-elt vars))
          (if    (let ((test (generate-ast 'boolean (1+ depth) schema))
                       (c (generate-ast type (1+ depth) schema))
                       (a (generate-ast type (1+ depth) schema)))
                   (cond ;; ((eq test nil)
                     ;;  a)
                     ;; ((eq test t)
                     ;;  c)
                     ;; ((eql c a) c)
                     (t
                      (list 'if test c a)))))
          (noise
           (let ((op (random-elt *noise-ops*)))
             (cons (first op)
                   (loop for arg-t in (second op)
                         collect (generate-ast (if (eq arg-t t)
                                                   type
                                                   arg-t) (1+ depth) schema)))))
          (the
           (let ((rest (zerop (random 4))))
             (if rest
                 `(the
                   (values ,@(loop repeat (random 2)
                                   collect (gen-type))
                           &optional
                           ,@(loop repeat (1+ (random 2))
                                   collect (gen-type))
                           &rest ,(gen-type))
                   ,(generate-ast type (1+ depth) schema))
                 `(the
                   (values ,@(loop repeat (random 5)
                                   collect (gen-type)))
                   ,(generate-ast type (1+ depth) schema)))))
          (typecase
              `(typecase
                   ,(generate-ast type (1+ depth) schema)
                 ,@(loop repeat (1+ (random 5))
                         collect `(,(gen-type)
                                   ,(generate-ast type (1+ depth) schema)))))
          (cond
            `(cond
               ,@(loop repeat (1+ (random 5))
                       collect `(,(generate-ast 'boolean (1+ depth) schema)
                                 ,(generate-ast type (1+ depth) schema)))))
          (block
              (let* ((block (gentemp))
                     (*blocks* (cons block *blocks*)))
                `(block ,block
                   ,@(loop repeat (1+ (random 3))
                           collect (generate-ast type (1+ depth) schema)))))
          (let
              (if (and *vars*
                       (zerop (random 2)))
                  (if (zerop (random 2))
                      (random-elt *vars*)
                      `(setq ,(random-elt *vars*)
                             ,(generate-ast type (+ depth 2) schema)))
                  (let* ((var (gentemp))
                         (value (generate-ast type (+ depth 2) schema))
                         (*vars* (cons var *vars*)))
                    `(let ((,var ,value))
                       ,(generate-ast type (1+ depth) schema)))))
          (flet
              (if (and *flets*
                       (zerop (random 2)))
                  `(,(random-elt *flets*))
                  (let* ((name (gentemp))
                         (body (generate-ast type (1+ depth) schema))
                         (*flets* (cons name *flets*)))
                    `(flet ((,name ()
                              ,body))
                       ,(generate-ast type (1+ depth) schema)))))
          (return-from
           `(return-from ,(random-elt *blocks*)
              ,(generate-ast type (1+ depth) schema)))
          (nth-value
           `(nth-value ,(random 5)
                      ,(generate-ast type (1+ depth) schema)))
          (closure
           `(call (lambda ()
                    ,(generate-ast type (1+ depth) schema))))
          (error
           `(error 'random-error))
          (func (if (null funcs)
                    (random-const type)
                    (let ((op (random-elt funcs)))
                      (cons (first op)
                            (loop for arg-t in (second op)
                                  collect (generate-ast arg-t (1+ depth) schema)))))))))))

(defun build-random-function (target-type)
  (let* ((schema (loop for i from 1 to 3
                       collect (cons (intern (format nil "V~d" i))
                                     (random-elt *types*))))
         (*max-depth* (min 2 (1+ (random *max-depth*))))
         *blocks*
         (sb-impl::*gentemp-counter* 0)
         (body (generate-ast target-type 0 schema))
         (vars (mapcar #'car schema)))
    (values
     `(lambda ,vars
        (declare (ignorable ,@vars))
        ,@(progn;if (> (random 100) 90)
            (loop for (v . t-name) in schema
                  collect `(declare (type ,(if nil;(> (random 100) 60)
                                               t
                                               t-name) ,v))))

        ,body)
     schema)))

;;; ================================================================
;;; 3. EXECUTION & COMPARISON
;;; ================================================================

(defun values-match-p (val1 val2)
  (cond
    ;; ((and (typep val1 'single-float) (typep val2 'single-float))
    ;;  (< (abs (- val1 val2)) 0.001))
    (t (and (= (length val1) (length val2))
            (loop for v1 in val1
                  for v2 in val2
                  always (or (equal v1 v2)
                             #+(and arm64 (not darwin))
                             (or (and (floatp v1) (sb-ext:float-nan-p v1))
                                 (and (floatp v2)
                                      (sb-ext:float-nan-p v2)))
                             ;; MINUS-ZERO
                             ;; (and (or (eql v1 0.0)
                             ;;          (eql v2 0.0))
                             ;;      (= v1 v2))
                             #-(and arm64 (not darwin))
                             (and (and (floatp v1)
                                       (sb-ext:float-nan-p v1))
                                  (and (floatp v2)
                                       (sb-ext:float-nan-p v2)))))))))

(defun safe-execute (func args)
  (ignore-errors (multiple-value-list (apply func args))))

(defun save-test (code reduced)
  (with-open-file (st (format nil "/tmp/test~a.lisp" *thread*)
                      :if-does-not-exist :create :if-exists :supersede
                      :direction :output)
    (write reduced :stream st)
    (terpri st)
    (write code :stream st)
    (pathname st)))

(defun replace-at-index (list index new-value)
  (loop for item in list
        for i from 0
        collect (if (= i index) new-value item)))

(defun ddmin-list (list pred)
  (let ((n 2) (current list))
    (loop
      (let ((len (length current)))
        (when (< len 1) (return current))
        (when (> n len) (setf n len))
        (let ((reduced-p nil))
          (dotimes (i n)
            (let* ((chunk-size (max 1 (ceiling len n)))
                   (start (min len (* i chunk-size)))
                   (end (min len (+ start chunk-size)))
                   (candidate (append (subseq current 0 start) (subseq current end))))
              (when (< (length candidate) (length current))
                (when (funcall pred candidate)
                  (setf current candidate)
                  (setf n 2)
                  (setf reduced-p t)
                  (return)))))
          (unless reduced-p
            (if (>= n len) (return current) (setf n (min len (* n 2))))))))))

(defun reduce-tree-pass (form pred)
  (unless (funcall pred form) (return-from reduce-tree-pass form))

  (cond
    ((consp form)
     ;; STRATEGY A: DEEP TREE DESCENT
     ;; Try replacing 'form' with a child, OR a grandchild.
     ;; This handles (COND ((NTH ...))) -> (NTH ...)
     (let ((candidates nil))
       (dolist (child form)
         (push child candidates)       ; Add Child
         (when (consp child)
           (dolist (grandchild child)
             (push grandchild candidates)))) ; Add Grandchild

       (dolist (candidate (nreverse candidates))
         (when (funcall pred candidate)
           ;; Found a simplified descendant that reproduces the bug
           (return-from reduce-tree-pass (reduce-tree-pass candidate pred)))))

     ;; STRATEGY B: LIST REDUCTION (DDMin)
     (let ((shrunk-list (ddmin-list form pred)))

       ;; STRATEGY C: STRUCTURAL RECURSION
       (let ((final-list shrunk-list))
         (loop for i from 0 below (length final-list) do
           (let ((child (nth i final-list)))
             (when (or (consp child) (stringp child))
               (let ((context-pred
                      (lambda (candidate)
                        (funcall pred (replace-at-index final-list i candidate)))))
                 (let ((reduced-child (reduce-tree-pass child context-pred)))
                   (unless (equal reduced-child child)
                     (setf final-list (replace-at-index final-list i reduced-child))))))))
         final-list)))
    (t form)))

(defun reduce-form (form pred)
  (let ((current form))
    (loop
      (let ((next (reduce-tree-pass current pred)))
        (if (equal next current)
            (return next)
            (setf current next))))))


(declaim (notinline report-compiler-error report-compiler-error))

(defun compile-code (code)
  ;(sb-ext:atomic-incf *compilation-count*)
  (handler-case
      (handler-bind (((or sb-ext:code-deletion-note sb-ext:compiler-note style-warning warning) #'muffle-warning))
        (multiple-value-bind (fun warn fail)
            (sb-ext:with-timeout 120 (compile nil code))
          (declare (ignore warn fail))
          ;; (when fail
          ;;   (error "~a" code))
          (values fun
                  (when *check-return-type*
                    (let* ((type (sb-kernel:%simple-fun-type fun))
                           (type (and (consp type)
                                      (caddr type))))
                      (when (typep type '(cons (eql values)))
                        (let ((ctype (sb-kernel:values-specifier-type type)))
                          (sb-kernel:values-type-required ctype))))))))
    (error (c)
      (report-compiler-error code c))))

(defun interpret-code (code)
  (handler-case
      (handler-bind (((or sb-ext:code-deletion-note sb-ext:compiler-note style-warning warning) #'muffle-warning))
        (sb-ext:with-timeout 120
          (let ((sb-ext:*evaluator-mode* :interpret))
            (eval code))))
    (error (c)
      (report-compiler-error code c))))

(defun error-equal (err1 err2)
  (let ((err1 (type-of err1))
        (err2 (type-of err2)))
    (not (and (not (or (eq err1 'sb-sys:memory-fault-error)
                       (eq err2 'sb-sys:memory-fault-error)))
              (or (eq err1 err2)
                  (subtypep err1 err2)
                  (subtypep err2 err1)
                  (and (eq err2 'sb-kernel:case-failure)
                       (subtypep err1 'type-error))
                  (and (eq err1 'sb-kernel:case-failure)
                       (subtypep err2 'type-error)))))))

(defun reduce-compiler-error (code error)
  (let ((error (if (symbolp error)
                   error
                   (type-of error))))
   (sb-ext:with-timeout 400
     (reduce-form code
                  (lambda (reduced)
                    (when (and (typep reduced '(cons (eql lambda) (cons cons)))
                               (every #'symbolp (second reduced)))
                      (let* ((*error-output* (make-broadcast-stream)))
                        (block nil
                          (handler-bind (((or sb-ext:code-deletion-note sb-ext:compiler-note style-warning warning) #'muffle-warning)
                                         (error (lambda (c)
                                                  (return (eq (type-of c) error)))))
                            (sb-ext:with-timeout 120 (compile nil reduced))
                            nil)))))))))

(defun to-defun (code &optional inputs)
  (if inputs
      `(progn
         (defun f ,@(cdr code))
         (f ,@inputs))
      `(defun f ,@(cdr code))))

(defun report-compiler-error (code error)
  (let ((reduced (to-defun (reduce-compiler-error code error))))
   (format t "~%!!! COMPILER ERROR !!!")
   (format t "~%Reason: ~A" error)
   (format t "~%Code: ~S"  reduced)
   (format t "~%--------------------------------------------------")
   (error "~a" (save-test code reduced))))

(defun reduce-code (code inputs o-c-val o-i-val o-c-err o-i-err type-mismatch)
  (declare (ignore o-c-val o-i-val))
  (let ((n-args (length inputs))
        (*error-output* (make-broadcast-stream))
        (o-c-err (if (typep o-c-err 'condition)
                     (type-of o-c-err)
                     o-c-err))
        (o-i-err (if (typep o-i-err 'condition)
                     (type-of o-i-err)
                     o-i-err)))
    (format t "Reducing ~a~%" (save-test (to-defun code inputs) nil))
    (sb-ext:with-timeout 400
      (reduce-form code
                   (lambda (reduced)
                     (when (and (typep reduced '(cons (eql lambda) (cons cons)))
                                (= (length (second reduced)) n-args)
                                (every #'symbolp (second reduced)))
                       (multiple-value-bind (fn types)
                           (compile-code reduced)
                         (multiple-value-bind (c-val c-err)
                             (ignore-errors (multiple-value-list (apply fn inputs)))
                           (cond (type-mismatch
                                  (not (loop for type in types
                                             for value in c-val
                                             always (sb-kernel:%%typep value type))))
                                 (t
                                  (multiple-value-bind (i-val i-err)
                                      (ignore-errors (multiple-value-list (apply
                                                                           (interpret-code reduced)
                                                                           inputs)))
                                    (and (or (not (or o-c-err c-err))
                                             (eq (type-of c-err) o-c-err))
                                         (or (not (or o-i-err i-err))
                                             (eq (type-of i-err) o-i-err))
                                         (or (not (or c-val i-val))
                                             (not (values-match-p c-val i-val)))))))))))))))

(defun reduce-memfault (code args)
  (format t "Reducing memfault~%")
  (let ((n-args (length args)))
    (sb-ext:with-timeout 400
      (reduce-form code
                   (lambda (reduced)
                     (when (and (typep reduced '(cons (eql lambda) (cons cons)))
                                (= (length (second reduced)) n-args)
                                (every #'symbolp (second reduced)))
                       (let* ((*error-output* (make-broadcast-stream)))
                         (block nil
                           (handler-bind (((or sb-ext:code-deletion-note sb-ext:compiler-note style-warning warning) #'muffle-warning)
                                          (error (lambda (c)
                                                   (report-compiler-error code c))))
                             (let ((fun (sb-ext:with-timeout 120 (compile nil reduced))))
                               (handler-bind ((sb-sys:memory-fault-error (lambda (c) (return c)))
                                              (error (lambda (c) c (return))))
                                 (apply fun args)))
                             nil)))))))))

(defun reduce-memfault-i (code args)
  (format t "Reducing memfault~%")
  (let ((n-args (length args)))
    (sb-ext:with-timeout 400
      (reduce-form code
                   (lambda (reduced)
                     (when (and (typep reduced '(cons (eql lambda) (cons cons)))
                                (= (length (second reduced)) n-args)
                                (every #'symbolp (second reduced)))
                       (let* ((*error-output* (make-broadcast-stream)))
                         (block nil

                           (handler-bind (((or sb-ext:code-deletion-note sb-ext:compiler-note style-warning warning) #'muffle-warning)
                                          (error (lambda (c)
                                                   (report-compiler-error code c))))
                             (let ((fun (sb-ext:with-timeout 120
                                          (let ((sb-ext:*evaluator-mode* :interpret))
                                            (eval code)))))
                               (handler-bind ((sb-sys:memory-fault-error (lambda (c) (return c)))
                                              (error (lambda (c) c (return))))
                                 (apply fun args)))
                             nil)))))))))

(defun reduce-timeout (code &optional (timeout 0.5))
  (reduce-form code
               (lambda (reduced)
                 (when (and (typep reduced '(cons (eql lambda) (cons cons)))
                            (every #'symbolp (second reduced)))
                   (let* ((*error-output* (make-broadcast-stream)))
                     (block nil
                       (handler-bind (((or sb-ext:code-deletion-note sb-ext:compiler-note style-warning warning) #'muffle-warning)
                                      (sb-ext:timeout
                                        (lambda (c)
                                          (return c))))
                         (sb-ext:with-timeout timeout (compile nil reduced))
                         nil)))))))

(defun report-error (reason code inputs c-res i-res c-err i-err &key type-mismatch)
  (let ((reduced (to-defun (reduce-code code inputs c-res i-res c-err i-err type-mismatch)
                           inputs)))
   (format t "~%!!! DETECTED DISCREPANCY !!!")
   (format t "~%Reason: ~A" reason)
   (format t "~%Code: ~S"  reduced)
   (format t "~%Inputs: ~A" inputs)
   (format t "~%Compiled Result: ~S" (or c-res c-err))
   (format t "~%Interpret Result: ~S" (or i-res i-err))
   (format t "~%--------------------------------------------------")

   (error "~a" (save-test code reduced))))

(defun report-memory-fault (code inputs)
  (let ((reduced (to-defun (reduce-memfault code inputs)
                           inputs)))
    (format t "~%!!! MEMORY FAULT !!!")
    (format t "~%Code: ~S"  reduced)
    (format t "~%Inputs: ~A" inputs)
    (format t "~%--------------------------------------------------")
    (error "~a" (save-test code reduced))))

(defun report-memory-fault-i (code inputs)
  (let ((reduced (to-defun (reduce-memfault-i code inputs)
                           inputs)))
    (format t "~%!!! MEMORY FAULT !!!")
    (format t "~%Code: ~S"  reduced)
    (format t "~%Inputs: ~A" inputs)
    (format t "~%--------------------------------------------------")
    (error "~a" (save-test code reduced))))

(defun is-arithmetic-error (err)
  (or (typep err '(or floating-point-invalid-operation
                   floating-point-overflow
                   division-by-zero))
      (and (typep err 'simple-error)
           (or (equal (simple-condition-format-control err)
                      "can't represent result of left shift")
               (equal (simple-condition-format-control err)
                      "Exponent too large to fit into memory: ~a")))))

(defvar *optimize-qualities*
  (loop for s in '(0 1)
        nconc
        (loop for a in '(0 1 3)
              nconc
              (loop for d in '(1 2 3)
                    collect `((speed ,s) (safety ,a) (debug ,d))))))

(defun add-optimize (lambda qualities)
  `(lambda ,(second lambda)
     (declare (optimize ,@qualities))
     ,@(cddr lambda)))

(defun run-test ()
  (let ((target (random-elt *types*)))
    (multiple-value-bind (code1 schema) (build-random-function target)
      (when *save*
        (save-test code1 nil))
      (let* ((*error-output* (make-broadcast-stream))
             (*print-pretty* nil)
             (i-fn (interpret-code code1))
             (inputs (loop repeat 2000
                           collect (loop for (_ . t-name) in schema
                                         collect (random-const t-name))))
             (answers (loop for input in inputs
                            collect (multiple-value-list
                                     (ignore-errors (multiple-value-list (apply i-fn input)))))))
        (multiple-value-bind (no-error-answers no-error-inputs)
            (loop for answer in answers
                  for input in inputs
                  when (car answer)
                  collect answer into no-error-answers
                  and
                  collect input into no-error-inputs
                  finally (return (values no-error-answers no-error-inputs)))
          (loop for oq in *optimize-qualities*
                for code = (add-optimize code1 oq)
                for unsafe = (zerop (second (assoc 'safety oq)))
                do
                (let ((answers (if unsafe
                                   no-error-answers
                                   answers))
                      (inputs (if unsafe
                                  no-error-inputs
                                  inputs)))
                  (multiple-value-bind (fn types) (compile-code code)
                    (loop for input in inputs
                          for (i-val i-err) in answers
                          do
                          (multiple-value-bind (c-val c-err)
                              (ignore-errors (multiple-value-list (apply fn input)))
                            (unless (or c-err
                                        (loop for type in types
                                              for value in c-val
                                              always (sb-kernel:%%typep value type)))
                              (report-error "TYPE MISMATCH" code input c-val types nil nil
                                            :type-mismatch t))
                            (cond
                              ;; A. If either failed due to Div-By-Zero, Ignore completely.
                              ((or (is-arithmetic-error c-err) (is-arithmetic-error i-err))
                               nil)

                              ;; B. Both Succeeded: Check Values
                              ((and (not c-err) (not i-err))
                               (unless (values-match-p c-val i-val)
                                 (report-error "VALUE MISMATCH" code input c-val i-val
                                               c-err i-err)))
                              ;; C. Both Errored (Non-DivZero): Check Error Types match
                              ((and c-err i-err)
                               (let ((c-err (type-of c-err))
                                     (i-err (type-of i-err)))
                                 (cond ((eq c-err 'sb-sys:memory-fault-error)
                                        (report-memory-fault code input))
                                       ((eq i-err 'sb-sys:memory-fault-error)
                                        (report-memory-fault-i code input))
                                       (t
                                        (unless (and (not (or (eq c-err 'sb-sys:memory-fault-error)
                                                              (eq i-err 'sb-sys:memory-fault-error)))
                                                     (or (eq c-err i-err)
                                                         (subtypep c-err i-err)
                                                         (subtypep i-err c-err)
                                                         (and (eq i-err 'sb-kernel:case-failure)
                                                              (subtypep c-err 'type-error))
                                                         (and (eq c-err 'sb-kernel:case-failure)
                                                              (subtypep i-err 'type-error))))
                                          (report-error "ERROR TYPE MISMATCH" code input c-val i-val
                                                        c-err i-err))))))

                              ;; D. One Error, One Success (Non-DivZero)
                              (t
                               (report-error "STATUS MISMATCH (One Error/One Value)"
                                             code input c-val i-val
                                             c-err i-err)))))))))))))

;;; ================================================================
;;; 4. MAIN LOOP
;;; ================================================================
(defvar *rand* (make-random-state t))
(defun main (&key (threads 12) float depth rational (number t)
                  noise
                  save)
  (setf *random-state* (make-random-state t))
  (when save
    (setf *save* t))
  (when noise
    (setf *noise* t))
  (when depth
    (setf *max-depth* depth))
  (when float
    (setf *operators* (append *operators* *float-ops*))
    (pushnew 'float *types*))
  (when rational
    (setf *operators* (append *operators* *ratio-ops*))
    (pushnew 'rational *types*))
  (when number
    (setf *operators* (remove-duplicates (append *operators* *number-ops*)))
    (pushnew 'real *types*)
    (pushnew 'float *types*)
    (pushnew 'single-float *types*)
    (pushnew 'double-float *types*)
    (pushnew 'rational *types*)
    (pushnew 'number *types*)
    (pushnew 'complex *types*)
    (pushnew '(complex rational) *types* :test #'equal)
    (pushnew '(complex float) *types* :test #'equal)
    (pushnew '(complex single-float) *types* :test #'equal)
    (pushnew '(complex double-float) *types* :test #'equal)
    (setf *number-types* (remove 'boolean *types*)))
  (if (= threads 1)
      (loop
       (run-test))
      (let ((threads
              (loop for i below threads
                    collect
                    (let ((i i))
                      (sb-thread:make-thread
                       (lambda ()
                         (let ((*thread* i))
                          (loop
                           (run-test))))
                       :name (format nil "random ~a" i))))))
        (unwind-protect (mapcar (lambda (th)
                                  (sb-thread:join-thread th :default nil ;; :timeout 0.8
                                                         )
                                  ;; (format t "~c~a" #\Return *compilation-count*)
                                  ;; (finish-output)
                                  )
                                threads)
          (mapcar (lambda (th)
                    (ignore-errors (sb-thread:terminate-thread th)))
                  threads)))))
