(eval-after-load "cc-styles"
  '(progn
     (add-to-list
      'c-style-alist
      '("ceg"
	(c-basic-offset . 3)
	(c-comment-only-line-offset . (0 . 0))
	(c-hanging-braces-alist     . ((substatement-open before after)
				       (arglist-cont-nonempty)))
	(c-offsets-alist . ((statement-block-intro . +)
			    (knr-argdecl-intro . 5)
			    (substatement-open . 0)
			    (substatement-label . 0)
			    (label . 0)
			    (statement-case-open . 0)
			    (statement-cont . +)
			    (arglist-intro . c-lineup-arglist-intro-after-paren)
			    (arglist-close . c-lineup-arglist)
			    (inline-open . 0)
			    (brace-list-open . 0)
			    (topmost-intro-cont
			     . (first c-lineup-topmost-intro-cont
				      c-lineup-gnu-DEFUN-intro-cont))))
	(c-special-indent-hook . c-gnu-impose-minimum)
	(c-block-comment-prefix . "")))
     (add-to-list
      'c-style-alist
      '("edg"
	(indent-tabs-mode . nil)
	(c-basic-offset . 3)
	(c-comment-only-line-offset . (0 . 0))
	(c-hanging-braces-alist     . ((substatement-open before after)
				       (arglist-cont-nonempty)))
	(c-offsets-alist . ((statement-block-intro . +)
			    (knr-argdecl-intro . 5)
			    (substatement-open . 0)
			    (substatement-label . 0)
			    (label . 0)
			    (case-label . +)
			    (statement-case-open . 0)
			    (statement-cont . +)
			    (arglist-intro . c-lineup-arglist-intro-after-paren)
			    (arglist-close . c-lineup-arglist)
			    (inline-open . 0)
			    (brace-list-open . 0)
			    (topmost-intro-cont
			     . (first c-lineup-topmost-intro-cont
				      c-lineup-gnu-DEFUN-intro-cont))))
	(c-special-indent-hook . c-gnu-impose-minimum)
	(c-block-comment-prefix . "")))
     (add-to-list
      'c-style-alist
      '("ledger"
	(indent-tabs-mode . nil)
	(c-basic-offset . 2)
	(c-comment-only-line-offset . (0 . 0))
	(c-hanging-braces-alist     . ((substatement-open before after)
				       (arglist-cont-nonempty)))
	(c-offsets-alist . ((statement-block-intro . +)
			    (knr-argdecl-intro . 5)
			    (substatement-open . 0)
			    (substatement-label . 0)
			    (label . 0)
			    (case-label . +)
			    (statement-case-open . 0)
			    (statement-cont . +)
			    (arglist-intro . c-lineup-arglist-intro-after-paren)
			    (arglist-close . c-lineup-arglist)
			    (inline-open . 0)
			    (brace-list-open . 0)
			    (topmost-intro-cont
			     . (first c-lineup-topmost-intro-cont
				      c-lineup-gnu-DEFUN-intro-cont))))
	(c-special-indent-hook . c-gnu-impose-minimum)
	(c-block-comment-prefix . "")))))

(eval-when-compile
  (defvar c-mode-base-map))

(defun my-c-mode-common-hook ()
  (define-key c-mode-base-map "\C-m" 'newline-and-indent)
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq indicate-empty-lines t)
  (setq fill-column 72)
  (cond
   ((string-match "/ledger/" (buffer-file-name))
    (c-set-style "ledger"))
   ((string-match "/ANSI/" (buffer-file-name))
    (c-set-style "edg")))
  (font-lock-add-keywords
   'c++-mode '(("\\<\\(assert\\|DEBUG\\)(" 1 widget-inactive t))))

(which-function-mode t)

(add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

(defun batch-untabify ()
  ;; command-line-args-left is what is left of the command line (from startup.el)
  (defvar command-line-args-left)	;Avoid 'free variable' warning
  (if (not noninteractive)
      (error "`batch-untabify' is to be used only with -batch"))
  (while command-line-args-left
    (if (file-directory-p (expand-file-name (car command-line-args-left)))
        ;; Directory as argument.
        (let ((untabify-files (directory-files (car command-line-args-left)))
              untabify-source untabify-dest)
          (dolist (untabify-file untabify-files)
            (if (and (not (auto-save-file-name-p untabify-file))
                     (setq untabify-source
                           (expand-file-name untabify-file
                                             (car command-line-args-left))))
                (with-current-buffer (find-file untabify-source)
                  (untabify (point-min) (point-max))
                  (save-buffer)))))
      ;; Specific file argument
      (let ((untabify-source (car command-line-args-left)))
        (with-current-buffer (find-file untabify-source)
          (untabify (point-min) (point-max))
          (save-buffer))))
    (setq command-line-args-left (cdr command-line-args-left))))
