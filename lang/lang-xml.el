;;;_ * nxml-mode

;(autoload 'nxml-mode "rng-auto" "" t)

(defalias 'xml-mode 'nxml-mode)

(defun my-nxml-mode-hook ()
  (define-key nxml-mode-map [return] 'newline-and-indent)
  (define-key nxml-mode-map [(control return)] 'other-window))

(add-hook 'nxml-mode-hook 'my-nxml-mode-hook)

;;;_ * nxml-mode

(defun load-nxhtml ()
  (interactive)
  (load "autostart"))

;;;_ * zencoding

(setq zencoding-mode-keymap (make-sparse-keymap))
(define-key zencoding-mode-keymap (kbd "C-c C-c") 'zencoding-expand-line)

(autoload 'zencoding-mode "zencoding-mode" nil t)

(add-hook 'nxml-mode-hook 'zencoding-mode)
(add-hook 'html-mode-hook 'zencoding-mode)

(add-hook 'html-mode-hook
	  (function
	   (lambda ()
	     (interactive)
	     (define-key html-mode-map [return] 'newline-and-indent))))

