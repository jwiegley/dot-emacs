(message "Starting thread...")

(let ((thread
       (make-thread
        #'(lambda ()
            (let* (completed
                   (proc
                    (make-process
                     :name "process"
                     :command '("yes")
                     :connection-type 'pipe
                     :filter #'(lambda (_proc x))
                     :sentinel #'(lambda (_proc event)
                                   (message "Sentinel: %S" x)
                                   (setq completed t)))))
              (while (not completed)
                (thread-yield)
                (accept-process-output proc nil 100)))))))

  (message "Beginning yield loop...")
  (while (thread-live-p thread)
    (thread-yield))
  (message "Joining thread...")
  (thread-join thread)

  (message "Test completed!"))
