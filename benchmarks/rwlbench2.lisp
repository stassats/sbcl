(defpackage :sbcl-lock-bench
  (:use :cl :sb-thread)
  (:shadow #:spinlock #:with-spinlock)
  (:export :compare-locks))

(in-package :sbcl-lock-bench)

(defparameter *time-wasting-iterations-read* 100)
(defparameter *time-wasting-iterations-write* 150)

;;; spinlock
(defstruct (spinlock)
  (state 0 :type sb-ext:word)) ; 0 = unlocked, 1 = locked

(defun spin-lock (lock)
  (declare (optimize (speed 3) (safety 0)))
  (loop (if (eql 0 (sb-ext:cas (spinlock-state lock) 0 1))
            (return t)
            (sb-thread:thread-yield))))

(declaim (inline spin-unlock))
(defun spin-unlock (lock)
  (declare (optimize (speed 3) (safety 0)))
  (setf (spinlock-state lock) 0))

(defmacro with-spinlock ((lock) &body body)
  `(progn
     (spin-lock ,lock)
     (unwind-protect (progn ,@body)
       (spin-unlock ,lock))))

(defun run-spinlock-worker (lock operations write-percent)
  (let* ((my-random-state (make-random-state t))
         (r (random 100 my-random-state)))
    (dotimes (i (the fixnum operations))
      ;; readers and writers use the same lock mechanism
      (with-spinlock (lock)
        (if (< r write-percent)
            (loop repeat *time-wasting-iterations-write*)
            (loop repeat *time-wasting-iterations-read*))
        ;; and do some some work inside the lock
        (setq r (random 100 my-random-state))))))

;;; spinlock-based rwlock
(defmacro with-rwlock-read ((lock) &body body)
  `(progn (rwspinlock-rdlock ,lock)
          (multiple-value-prog1 (progn ,@body) (rwspinlock-rdunlock ,lock))))

(defmacro with-rwlock-write ((lock) &body body)
  `(progn (rwspinlock-wrlock ,lock)
          (multiple-value-prog1 (progn ,@body) (rwspinlock-wrunlock ,lock))))

(defun run-rwlock-worker (lock operations write-percent)
  (let* ((my-random-state (make-random-state t))
        (r (random 100 my-random-state)))
    (dotimes (i (the fixnum operations))
      (if (< r write-percent)
          (with-rwlock-write (lock)
            (loop repeat *time-wasting-iterations-write*)
            (setq r (random 100 my-random-state)))
          (with-rwlock-read (lock)
            (loop repeat *time-wasting-iterations-read*)
            (setq r (random 100 my-random-state)))))))

;; runner
(defun execute-bench (lock-type operations threads write-percent)
  (let ((threads-list '())
        (start-time (get-internal-real-time))
        (lock (if (eq lock-type :rwlock)
                  (sb-thread::make-rw-spinlock)
                  (make-spinlock))))

    (dotimes (i threads)
      (push (sb-thread:make-thread
             (lambda ()
               (if (eq lock-type :rwlock)
                   (run-rwlock-worker lock operations write-percent)
                   (run-spinlock-worker lock operations write-percent))))
            threads-list))

    (mapc #'sb-thread:join-thread threads-list)

    (let* ((end-time (get-internal-real-time))
           (elapsed (/ (- end-time start-time) internal-time-units-per-second)))
      elapsed)))

(defun compare-locks (&key (threads 4) (ops-per-thread 100000))
  (format t "~%================================================~%")
  (format t "Comparing spinlock-based RWLOCK vs MUTEX~%")
  (format t "Threads: ~D | Ops/Thread: ~D~%" threads ops-per-thread)
  (format t "================================================~%~%")
  (format t "~10A | ~15A | ~15A | ~A~%" "Write %" "RW-Lock Time" "Mutex Time" "Speedup (RW / Mutex)")
  (format t "------------------------------------------------------------------~%")

  (dolist (pct '(0 1 2 3 5 10 20 30 40 50 60 70 80 90 100))
    (let ((rw-time (execute-bench :rwlock ops-per-thread threads pct))
          (mutex-time (execute-bench :mutex ops-per-thread threads pct)))
      (format t "~10D | ~14,3Fs | ~14,3Fs | ~,2Fx~%"
              pct
              rw-time
              mutex-time
              (/ mutex-time rw-time))))) ; Speedup > 1.0x means RWLock was faster
