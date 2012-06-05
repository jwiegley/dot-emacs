;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defadvice ido-visit-buffer (before switch-to-buffers-workgroup
                                    (buffer method &optional record)
                                    activate)
  "If a workgroup is showing BUFFER, switch to it first"
  (wg-aif (wg-find-buffer (if (bufferp buffer)
                              (buffer-name buffer)
                            buffer))
      (ignore-errors
        (wg-switch-to-workgroup it))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;_ , modeline-posn

;; (size-indication-mode)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when-compile
  (require 'ace-jump-mode))

(defun quick-jump-char (&optional prefix no-ace-jump)
  (interactive "P")
  (let* ((query-char (event-basic-type last-command-event))
         (regexp (regexp-quote (char-to-string query-char)))
         (ace-jump-mode-hook
          (list (function
                 (lambda ()
                   (define-key overriding-local-map
                     [(alt ?-)]
                     (function
                      (lambda (&optional prefix)
                        (interactive "P")
                        (ace-jump-done)
                        (quick-jump-char prefix)))))))))
    (if (looking-at regexp)
        (forward-char))
    (re-search-forward regexp)
    (backward-char)
    (unless no-ace-jump
      (ace-jump-do (regexp-quote (char-to-string query-char))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
