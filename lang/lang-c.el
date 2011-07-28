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
        (c-set-style "edg")
        (substitute-key-definition 'fill-paragraph 'ti-refill-comment
                                   c-mode-base-map global-map)
        (define-key c-mode-base-map [(meta ?q)] 'ti-refill-comment)))))
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

(defun ti-refill-comment ()
  (interactive)
  (save-excursion
    (goto-char (line-beginning-position))
    (let ((begin (point)) end
          (marker ?-) (marker-re "\\(-----\\|\\*\\*\\*\\*\\*\\)")
          (leader-width 0))
      (unless (looking-at "[ \t]*/\\*[-* ]")
        (search-backward "/*")
        (goto-char (line-beginning-position)))
      (unless (looking-at "[ \t]*/\\*[-* ]")
        (error "Not in a comment"))
      (while (and (looking-at "\\([ \t]*\\)/\\* ")
                  (setq leader-width (length (match-string 1)))
                  (not (looking-at (concat "[ \t]*/\\*" marker-re))))
        (forward-line -1)
        (setq begin (point)))
      (when (looking-at (concat "[^\n]+?" marker-re "\\*/[ \t]*$"))
        (setq marker (if (string= (match-string 1) "-----") ?- ?*))
        (forward-line))
      (while (and (looking-at "[^\n]+?\\*/[ \t]*$")
                  (not (looking-at (concat "[^\n]+?" marker-re
                                           "\\*/[ \t]*$"))))
        (forward-line))
      (when (looking-at (concat "[^\n]+?" marker-re "\\*/[ \t]*$"))
        (forward-line))
      (setq end (point))
      (let ((comment (buffer-substring-no-properties begin end)))
        (with-temp-buffer
          (insert comment)
          (goto-char (point-min))
          (flush-lines (concat "^[ \t]*/\\*" marker-re "[-*]+\\*/[ \t]*$"))
          (goto-char (point-min))
          (while (re-search-forward "^[ \t]*/\\* ?" nil t)
            (goto-char (match-beginning 0))
            (delete-region (match-beginning 0) (match-end 0)))
          (goto-char (point-min))
          (while (re-search-forward "[ \t]*\\*/[ \t]*$" nil t)
            (goto-char (match-beginning 0))
            (delete-region (match-beginning 0) (match-end 0)))
          (goto-char (point-min)) (delete-trailing-whitespace)
          (goto-char (point-min)) (flush-lines "^$")
          (set-fill-column (- 80         ; width of the text
                              6          ; width of "/*  */"
                              leader-width))
          (goto-char (point-min)) (fill-paragraph)
          (goto-char (point-min))
          (while (not (eobp))
            (insert (make-string leader-width ? ) "/* ")
            (goto-char (line-end-position))
            (insert (make-string (- 80 3 (current-column)) ? ) " */")
            (forward-line))
          (goto-char (point-min))
          (insert (make-string leader-width ? )
                  "/*" (make-string (- 80 4 leader-width) marker) "*/\n")
          (goto-char (point-max))
          (insert (make-string leader-width ? )
                  "/*" (make-string (- 80 4 leader-width) marker) "*/\n")
          (setq comment (buffer-string)))
        (goto-char begin)
        (delete-region begin end)
        (insert comment)))))

;;;_ * doxymacs

(autoload 'doxymacs-mode "doxymacs")
(autoload 'doxymacs-font-lock "doxymacs")

(defun my-doxymacs-font-lock-hook ()
  (if (or (eq major-mode 'c-mode) (eq major-mode 'c++-mode))
      (doxymacs-font-lock)))

(add-hook 'font-lock-mode-hook 'my-doxymacs-font-lock-hook)

