(require 'pos-tip)

(defun my-describe-function (function)
  "Display the full documentation of FUNCTION (a symbol) in tooltip."
  (interactive (list (function-called-at-point)))
  (if (null function)
      (pos-tip-show
       "** You didn't specify a function! **" '("red"))
    (pos-tip-show
     (with-temp-buffer
       (let ((standard-output (current-buffer))
             (help-xref-following t)
             (major-mode 'help-mode)) ; Avoid error in Emacs 24
         (prin1 function)
         (princ " is ")
         (describe-function-1 function)
         (buffer-string)))
     nil nil nil 0)))

(define-key emacs-lisp-mode-map (kbd "C-;") 'my-describe-function)
(define-key lisp-interaction-mode-map (kbd "C-;") 'my-describe-function)
