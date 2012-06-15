;; From http://www.emacswiki.org/cgi-bin/wiki.pl?IndirectBuffers

(defun indirect-buffer ()
  "Edit stuff in this buffer in an indirect buffer.
 The indirect buffer can have another major mode."
  (interactive)
  (let ((buffer-name (generate-new-buffer-name "*indirect*")))
    (pop-to-buffer (make-indirect-buffer (current-buffer) buffer-name))))

(defvar indirect-mode-name nil
  "Mode to set for indirect buffers.")
(make-variable-buffer-local 'indirect-mode-name)

(defun indirect-region (start end)
  "Edit the current region in another buffer.
 If the buffer-local variable `indirect-mode-name' is not set, prompt
 for mode name to choose for the indirect buffer interactively.
 Otherwise, use the value of said variable as argument to a funcall."
  (interactive "r")
  (let ((buffer-name (generate-new-buffer-name "*indirect*"))
        (mode
         (if (not indirect-mode-name)
             (setq indirect-mode-name
                   (intern
                    (completing-read
                     "Mode (default `org-mode'): "
                     (mapcar (lambda (e)
                               (list (symbol-name e)))
                             (apropos-internal "-mode$" 'commandp))
                     nil t nil nil "org-mode")))
           indirect-mode-name)))
    (pop-to-buffer (make-indirect-buffer (current-buffer) buffer-name))
    (funcall mode)
    (narrow-to-region start end)
    (goto-char (point-min))
    (shrink-window-if-larger-than-buffer)))

(provide 'indirect)
