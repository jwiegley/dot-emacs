;;; -*- lexical-binding: t -*-

(let* ((mutex (make-mutex))
       (cond-var (make-condition-variable mutex))
       waiting
       (thread-b
        (make-thread
         #'(lambda ()
             (message "b0")
             (with-mutex mutex
               (message "b1")
               (condition-notify cond-var)
               (message "b2"))
             (message "b3"))))
       ;; (thread-a-wait
       ;;  (make-thread
       ;;   #'(lambda ()
       ;;       (message "a0")
       ;;       (with-mutex mutex
       ;;         (message "a1")
       ;;         (setq waiting t)
       ;;         (let ((countdown 10))
       ;;           (while (and (not (condition-wait cond-var 0.1))
       ;;                       (> (setq countdown (1- countdown)) 0))
       ;;             (message "waiting..."))
       ;;           (if (<= countdown 0)
       ;;               (error "Failed to wait on condition variable")
       ;;             (message "countdown %S" countdown)))
       ;;         (setq waiting nil)
       ;;         (message "a2"))
       ;;       (message "a3"))))
       (thread-a
        (make-thread
         #'(lambda ()
             (message "a0")
             (with-mutex mutex
               (message "a1")
               (setq waiting t)
               (condition-wait cond-var)
               (setq waiting nil)
               (message "a2"))
             (message "a3")))))
  (message "main1")
  (message "main2: %S" (thread-last-error t))
  (message "main3: %S" (thread-join thread-a))
  (message "main3a: %S" (thread-last-error t))
  (message "main4: %S" (thread-join thread-b)))
