;;; queue --- Thread-safe O(1) queues -*- lexical-binding: t -*-

;; From https://gist.github.com/jordonbiondo/d3679eafbe9e99a5dff1

(require 'cl-lib)
(require 'cl-macs)
(require 'ert)

(cl-defstruct dllist value (prev nil) (next nil))

(cl-defstruct fifo (dllist nil))

(cl-defstruct
    (queue
     (:constructor nil)
     (:constructor queue-create
                   (&key (mutex (make-mutex))
                         (pushed (make-condition-variable mutex))
                         (fifo (make-fifo)))))
  mutex pushed fifo)

(defun dllist-from-list (list)
  "Create a doubly linked list with LIST's elements."
  (when list
    (let* ((dll (make-dllist :value (pop list)))
           (prev dll))
      (dolist (v list)
        (let ((next (make-dllist :value v)))
          (setf (dllist-next prev) next)
          (setf (dllist-prev next) prev)
          (setq prev next)))
      dll)))

(defun dllist-to-list (dll)
  "Convert a doubly linked list DLL back into a regular list."
  (cl-loop for x = dll then (dllist-next x)
           while x
           for y = (dllist-value x)
           collect y))

(ert-deftest dllist-to-from-list-test ()
  (let ((x '(1 2 nil 4 5)))
    (should (equal x (dllist-to-list (dllist-from-list x))))))

(ert-deftest dllist-to-from-to-from-list-test ()
  (let ((x '(1 2 nil 4 5)))
    (should (equal x (dllist-to-list
                      (dllist-from-list
                       (dllist-to-list
                        (dllist-from-list x))))))))

(defun dllist-nth (dll n)
  "Get Nth node of the doubly linked list DLL.
N may be negative to look backwards."
  (let ((node dll))
    (dotimes (i (abs n))
      (setq node
            (if (< n 0)
                (dllist-prev node)
              (dllist-next node))))
    node))

(ert-deftest dllist-nth-test ()
  (let ((x (dllist-from-list '(1 2 nil 4 5))))
    (should (= 2 (dllist-value (dllist-nth x 1))))
    (should (= 4 (dllist-value (dllist-nth x 3))))))

(defun dllist-cyclic-from-list (list)
  "Make a cyclic doubly linked list from LIST."
  (let* ((x (dllist-from-list list))
         (end (dllist-nth x (1- (length list)))))
    (setf (dllist-next end) x)
    (setf (dllist-prev x) end)
    x))

(ert-deftest dllist-cyclic-from-list-test ()
  (let ((x (dllist-cyclic-from-list '(1 2 nil 4 5))))
    (should (= 2 (dllist-value (dllist-nth x 1))))
    (should (= 2 (dllist-value (dllist-nth x 6))))))

(defun fifo-push (fifo elem)
  "Push ELEM onto the back of FIFO."
  (let ((dll (fifo-dllist fifo)))
    (if dll
        (let ((n (dllist-from-list (list elem))))
          (setf (dllist-next (dllist-prev dll)) n)
          (setf (dllist-prev n) (dllist-prev dll))
          (setf (dllist-prev dll) n)
          (setf (dllist-next n) dll))
      (setf (fifo-dllist fifo)
            (dllist-cyclic-from-list (list elem))))))

(defun fifo-from-list (list)
  "Create a new FIFO queue containing LIST initially."
  (make-fifo :dllist (dllist-cyclic-from-list list)))

(defun fifo-pop (fifo)
  "Pop and return the first element off FIFO.
This raises an error if the FIFO is empty."
  (cl-assert (not (fifo-empty-p fifo)))
  (let* ((dll (fifo-dllist fifo))
         (val (dllist-value dll)))
    (if (eql dll (dllist-next dll))
        (setf (fifo-dllist fifo) nil)
      (setf (dllist-next (dllist-prev dll)) (dllist-next dll))
      (setf (dllist-prev (dllist-next dll)) (dllist-prev dll))
      (setf (fifo-dllist fifo) (dllist-next dll)))
    val))

(defun fifo-empty-p (fifo)
  "Return non-nil if the FIFO is empty."
  (null (fifo-dllist fifo)))

(defun fifo-length (fifo)
  "Return the number of elements in FIFO."
  (let* ((dll (fifo-dllist fifo))
         (next (dllist-next dll))
         (len (if next 1 0)))
    (while (and dll next (not (eql dll next)))
      (incf len)
      (setq next (dllist-next next)))
    len))

(defun fifo-to-list (fifo)
  "Create a new FIFO queue containing LIST initially."
  (let ((dll (fifo-dllist fifo)))
    (when dll
      (cl-loop for i from 1 to (fifo-length fifo)
               for x = dll then (dllist-next x)
               while x
               for y = (dllist-value x)
               collect y))))

(ert-deftest fifo-push-test ()
  (let ((fifo (fifo-from-list '(1 2 3))))
    (fifo-push fifo 4)
    (should (equal '(1 2 3 4) (fifo-to-list fifo)))))

(ert-deftest fifo-pop-test ()
  (let ((fifo (fifo-from-list '(1 2 3))))
    (should (= 1 (fifo-pop fifo)))
    (should (equal '(2 3) (fifo-to-list fifo)))))

(defun queue-push (queue elem)
  (with-mutex (queue-mutex queue)
    (fifo-push (queue-fifo queue) elem)
    (condition-notify (queue-pushed queue)))
  (thread-yield))

(defun queue-pop (queue)
  (thread-yield)
  (with-mutex (queue-mutex queue)
    (let ((fifo (queue-fifo queue)))
      (while (fifo-empty-p fifo)
        (condition-wait (queue-pushed queue)))
      (fifo-pop fifo))))

(ert-deftest queue-push-test ()
  (let ((queue (queue-create :fifo (fifo-from-list '(1 2 3)))))
    (queue-push queue 4)
    (should (equal '(1 2 3 4) (fifo-to-list (queue-fifo queue))))))

(ert-deftest queue-pop-test ()
  (let ((queue (queue-create :fifo (fifo-from-list '(1 2 3)))))
    (should (= 1 (queue-pop queue)))
    (should (equal '(2 3) (fifo-to-list (queue-fifo queue))))))

(ert-deftest queue-push-pop-test ()
  (let ((queue (queue-create)))
    (queue-push queue 1)
    (queue-push queue 2)
    (queue-push queue 3)
    (should (= 1 (queue-pop queue)))
    (should (= 2 (queue-pop queue)))
    (should (= 3 (queue-pop queue)))))

(ert-deftest queue-with-multi-threads-test ()
  (let* ((queue (queue-create))
         (foo (make-thread
               #'(lambda ()
                   (message "pushing 1.. %S" queue)
                   (queue-push queue 1)
                   (message "pushing 2.. %S" queue)
                   (queue-push queue 2)
                   (message "pushing 3.. %S" queue)
                   (queue-push queue 3)
                   (message "foo is done"))))
         (bar (make-thread
               #'(lambda ()
                   (message "pulling 1.. %S" queue)
                   (should (= 1 (queue-pop queue)))
                   (message "pulling 2.. %S" queue)
                   (should (= 2 (queue-pop queue)))
                   (message "pulling 3.. %S" queue)
                   (should (= 3 (queue-pop queue)))
                   (message "bar is done")))))
    (message "joining foo")
    (thread-join foo)
    (message "joining bar")
    (thread-join bar)
    (should (null (thread-last-error t)))))

(provide 'queue)

;;; queue.el ends here
