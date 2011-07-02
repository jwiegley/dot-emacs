;;;_ * cc-mode

(require 'cc-mode)

(setq c-syntactic-indentation nil)

(define-key c-mode-base-map "#"         'self-insert-command)
(define-key c-mode-base-map "{"         'self-insert-command)
(define-key c-mode-base-map "}"         'self-insert-command)
(define-key c-mode-base-map "/"         'self-insert-command)
(define-key c-mode-base-map "*"         'self-insert-command)
(define-key c-mode-base-map ";"         'self-insert-command)
(define-key c-mode-base-map ","         'self-insert-command)
(define-key c-mode-base-map ":"         'self-insert-command)
(define-key c-mode-base-map "("         'self-insert-command)
(define-key c-mode-base-map ")"         'self-insert-command)
(define-key c-mode-base-map [tab]       'yas/expand)

(define-key c++-mode-map "<"        'self-insert-command)
(define-key c++-mode-map ">"        'self-insert-command)

(add-to-list 'auto-mode-alist '("\\.h\\'" . c++-mode))
(add-to-list 'auto-mode-alist '("\\.m\\'" . c-mode))
(add-to-list 'auto-mode-alist '("\\.mm\\'" . c++-mode))

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
			    (case-label . 0)
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
  (doxymacs-mode)
  (define-key c-mode-base-map "\C-m" 'newline-and-indent)
  (define-key c-mode-base-map [(meta ?j)] 'delete-indentation-forward)
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq indicate-empty-lines t)
  (setq fill-column 72)
  (column-marker-3 80)
  (let ((bufname (buffer-file-name)))
    (when bufname
      (cond
       ((string-match "/ledger/" bufname)
        (c-set-style "ledger"))
       ((string-match "/ANSI/" bufname)
        (c-set-style "edg")))))
  (font-lock-add-keywords
   'c++-mode '(("\\<\\(assert\\|DEBUG\\)(" 1 font-lock-warning-face t))))

(which-function-mode t)

(add-hook 'c-mode-common-hook 'my-c-mode-common-hook)

(require 'rx)

(defvar c++-token-regexp
  (rx (or (and "delete" ?\[ ?\])        ; delete[]
          (regexp "[A-Za-z0-9_]+")      ; identifier (more or less)
          (and (or ?! ?% ?* ?/ ?= ?^ ?~) (? ?=))
          (and ?& (? (or ?& ?=)))       ; &, &=, &&
          (and ?| (? (or ?| ?=)))       ; |, |=, ||
          (and ?+ (? (or ?+ ?=)))       ; +, +=, ++
          (and ?- (? (or ?> ?- ?=)))    ; -, -=, ->, --
          (and ?\< (? (or (and ?\< (? ?=)) ?=)))
                                        ; <, <=, <<, <<=
          (and ?\> (? (or (and ?\< (? ?=)) ?=)))
                                        ; >, >=, >>, >>=
          (and ?: (? ?:))               ; :, ::
          ?,                            ; comma
          ?#                            ; preprocessor token
          ?\;                           ; semi-colon
          ?.                            ; dot, decimal point
          ??                            ; ternary question
          ?\'                           ; char literal
          ?\"                           ; string literal
          ?\\                           ; escape char
          ?\(                           ; open paren
          ?\)                           ; close paren
          ?\[                           ; left bracket
          ?\]                           ; right bracket
          ?\{                           ; left brace
          ?\}                           ; right brace
          anything)))

(defun forward-c++-token (arg)
  (interactive "p")
  (dotimes (n arg)
    (let ((here (point)))
      (skip-chars-forward " \t\n\r")
      (when (and (= here (point))
                 (looking-at c++-token-regexp))
        (goto-char (match-end 0))
        (skip-chars-forward " \t\n\r"))
      (when (= here (point))
        (forward-word)
        (skip-chars-forward " \t\n\r")))))

(defun backward-c++-token (arg)
  (interactive "p")
  (dotimes (n arg)
    (let ((here (point)))
      (skip-chars-backward " \t\n\r")
      (if (looking-back c++-token-regexp nil t)
          (goto-char (match-beginning 0))))))

(defun setup-token-movement ()
  (define-key c-mode-base-map [(meta ?f)] 'forward-c++-token)
  (define-key c-mode-base-map [(meta ?b)] 'backward-c++-token))

;(add-hook 'c-mode-common-hook 'setup-token-movement)

;;;_ * doxymacs

(autoload 'doxymacs-mode "doxymacs")
(autoload 'doxymacs-font-lock "doxymacs")

(defun my-doxymacs-font-lock-hook ()
  (if (or (eq major-mode 'c-mode) (eq major-mode 'c++-mode))
      (doxymacs-font-lock)))

(add-hook 'font-lock-mode-hook 'my-doxymacs-font-lock-hook)

