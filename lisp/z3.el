;; -*- lexical-binding: t -*-

(defmacro z3-get-model (&rest forms)
  `(with-current-buffer (generate-new-buffer "*z3*")
     (lexical-let
         ((proc (start-process "z3" (current-buffer)
                               "z3" "-smt2" "-in"))
          (active t)
          result)

       (set-process-sentinel
        proc
        #'(lambda (proc _)
            (when (eq 'exit (process-status proc))
              (let ((buf (process-buffer proc)))
                (with-current-buffer buf
                  (goto-char (point-min))
                  (when (eq 'sat (read buf))
                    (setq result
                          (mapcar
                           (pcase-lambda
                             (`(define-fun ,sym _ _ ,value))
                             (cons sym value))
                           (cdr (read buf)))))
                  (kill-buffer)))
              (setq active nil))))

       (with-temp-buffer
         (dolist (form ',forms)
           (pp form (point-marker)))
         (process-send-region proc (point-min) (point-max))
         (process-send-string proc "\n(check-sat)\n(get-model)\n")
         (process-send-eof proc))

       (while active
         (sleep-for 0.1))
       result)))

(= 98 (alist-get
       'v2 (z3-get-model
            (declare-const v1 Int)
            (declare-const v2 Int)
            (assert (> v1 0))
            (assert (> v2 0))
            (assert (< (+ v1 v2) 100))
            (maximize v2))))
