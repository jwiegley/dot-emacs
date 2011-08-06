;;;_ * python-mode

;;(require 'python)

(autoload 'python-mode "python-mode" "Python editing mode." t)

(setq auto-mode-alist (cons '("\\.py$" . python-mode) auto-mode-alist)
      interpreter-mode-alist (cons '("python" . python-mode)
                                   interpreter-mode-alist))

(eval-after-load "python-mode"
  '(define-key py-mode-map [(control return)] 'other-window))

(defvar python-keywords-wanting-colon
  '("def" "class" "if" "elif" "while" "else" "with"
    "try" "except" "finally" "for" "lambda"))

(defvar python-kwc-regexp nil)

(autoload 'word-at-point "thingatpt" nil t)

(defun python-newline-and-indent ()
  "Always make sure that colons appear in the appropriate place."
  (interactive)
  (unless (progn
	    (skip-chars-backward " \t")
	    (memq (char-before) '(?: ?, ?\\)))
    (let ((here (point)))
      (goto-char (line-beginning-position))
      (skip-chars-forward " \t")
      (let ((add-colon-p (member (word-at-point)
				 python-keywords-wanting-colon)))
	(goto-char here)
	(if add-colon-p
	    (let ((last-command-char ?:))
	      (python-electric-colon nil))))))
  (call-interactively 'newline-and-indent))

(defun my-python-mode-hook ()
  (flymake-mode)
  
  (setq indicate-empty-lines t)
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq indent-tabs-mode nil)

  ;;(define-key python-mode-map [return] 'python-newline-and-indent)
  ;;
  ;;(define-key python-mode-map [(control ?c) ?w]
  ;;  'flymake-display-err-menu-for-current-line)
  ;;(define-key python-mode-map [(control ?c) (control ?w)]
  ;;  'flymake-start-syntax-check)
  ;;(define-key python-mode-map [(meta ?n)] 'flymake-goto-next-error)
  ;;(define-key python-mode-map [(meta ?p)] 'flymake-goto-prev-error)
  )

(add-hook 'python-mode-hook 'my-python-mode-hook)

;;; flymake

(autoload 'flymake-mode "flymake" "" t)

(eval-after-load "flymake"
  '(progn
     (defun flymake-pylint-init ()
       (let* ((temp-file   (flymake-init-create-temp-buffer-copy
			    'flymake-create-temp-inplace))
	      (local-file  (file-relative-name
			    temp-file
			    (file-name-directory buffer-file-name))))
	 (list "epylint" (list local-file))))

     (add-to-list 'flymake-allowed-file-name-masks
		  '("\\.py\\'" flymake-pylint-init))

     (defun flymake-hslint-init ()
       (let* ((temp-file   (flymake-init-create-temp-buffer-copy
			    'flymake-create-temp-inplace))
	      (local-file  (file-relative-name
			    temp-file
			    (file-name-directory buffer-file-name))))
	 (list "hslint" (list local-file))))

     (add-to-list 'flymake-allowed-file-name-masks
		  '("\\.l?hs\\'" flymake-hslint-init))))

;;; lang-python.el ends here
