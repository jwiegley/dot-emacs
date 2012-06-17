;;; edit-var.el --- display and edit Lisp variables

(defvar edit-variable-buffer)
(defvar edit-variable-symbol)
(defvar edit-variable-windows)

(make-variable-buffer-local 'edit-variable-buffer)
(make-variable-buffer-local 'edit-variable-symbol)
(make-variable-buffer-local 'edit-variable-windows)

;;;###autoload
(defun edit-variable (variable)
  "Edit the value of VARIABLE."
  (interactive (list (completing-read "Edit variable: " obarray 'boundp)))
  (let* ((symbol (intern variable))
	 (value (symbol-value symbol))
	 (buffer (current-buffer)))
    (with-current-buffer (get-buffer-create (format "*var %s*" variable))
      (erase-buffer)
      (emacs-lisp-mode)
      (setq edit-variable-buffer buffer
	    edit-variable-symbol symbol
	    edit-variable-windows (current-window-configuration))
      (insert (pp-to-string value))
      (goto-char (point-min))
      (select-window (display-buffer (current-buffer)))
      (define-key (current-local-map) [(control ?c) (control ?c)]
	(function
	 (lambda ()
	   (interactive)
	   (goto-char (point-min))
	   (let ((symbol edit-variable-symbol)
		 (value (read (current-buffer))))
	     (with-current-buffer edit-variable-buffer
	       (set symbol value)))
	   (set-window-configuration edit-variable-windows)))))))

(provide 'edit-var)

;; edit-var.el ends here
