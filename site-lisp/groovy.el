;;; groovy.el --- Major mode for editing Groovy source text
;;; This file was created from javascript.el written and maintained by Karl.
;;; Minor changes were made to include some of the keywords from Groovy
;;; and use groovy/gr- instead of javascript/js-.

;; Copyright (C) 2007 Seth Schroeder

;; Author: Seth Schroeder <seth.schroeder@nearinfinity.com>
;; Author of javascript.el: Karl Landström <kland@comhem.se>
;; Maintainer: Seth Schroeder <seth.schroeder@nearinfinity.com>
;; Version: 1.0
;; Date: 2007-12-26
;; Keywords: languages, oop, groovy

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;; The main features of this Groovy mode are syntactic
;; highlighting (enabled with `font-lock-mode' or
;; `global-font-lock-mode'), automatic indentation and filling of
;; comments.
;;
;; This package has (only) been tested with Carbon "Summer" Emacs 22.1.1.
;;
;; Installation:
;;
;; Put this file in a directory where Emacs can find it (`C-h v
;; load-path' for more info). Then add the following lines to your
;; Emacs initialization file:
;;
;;    (add-to-list 'auto-mode-alist '("\\.groovy\\'" . groovy-mode))
;;    (autoload 'groovy-mode "groovy" nil t)
;;
;; General Remarks:
;;
;; This mode assumes that block comments are not nested inside block
;; comments and that strings do not contain line breaks.
;;
;; Exported names start with "groovy-" whereas private names start
;; with "gr-".
;;

;;; Code:

(require 'cc-mode)
(require 'font-lock)
(require 'newcomment)

(defgroup groovy nil
  "Customization variables for `groovy-mode'."
  :tag "Groovy"
  :group 'languages)

(defcustom groovy-indent-level 4
  "Number of spaces for each indentation step."
  :type 'integer
  :group 'groovy)
(make-variable-buffer-local 'groovy-indent-level)

(defcustom groovy-auto-indent-flag t
  "Automatic indentation with punctuation characters. If non-nil, the
current line is indented when certain punctuations are inserted."
  :type 'boolean
  :group 'groovy)


;; --- Keymap ---

(defvar groovy-mode-map nil
  "Keymap used in Groovy mode.")

(unless groovy-mode-map
  (setq groovy-mode-map (make-sparse-keymap)))

(when groovy-auto-indent-flag
  (mapc (lambda (key)
	  (define-key groovy-mode-map key 'groovy-insert-and-indent))
	'("[" "]" "{" "}" "(" ")" ":" ";" ",")))

(defun groovy-insert-and-indent (key)
  "Run command bound to key and indent current line. Runs the command
bound to KEY in the global keymap and indents the current line."
  (interactive (list (this-command-keys)))
  (call-interactively (lookup-key (current-global-map) key))
  (indent-according-to-mode))


;; --- Syntax Table And Parsing ---

(defvar groovy-mode-syntax-table
  (let ((table (make-syntax-table)))
    (c-populate-syntax-table table)

    ;; The syntax class of underscore should really be `symbol' ("_")
    ;; but that makes matching of tokens much more complex as e.g.
    ;; "\\<xyz\\>" matches part of e.g. "_xyz" and "xyz_abc". Defines
    ;; it as word constituent for now.
    (modify-syntax-entry ?_ "w" table)

    table)
  "Syntax table used in Groovy mode.")


(defun gr-re-search-forward-inner (regexp &optional bound count)
  "Auxiliary function for `gr-re-search-forward'."
  (let ((parse)
        (saved-point (point-min)))
    (while (> count 0)
      (re-search-forward regexp bound)
      (setq parse (parse-partial-sexp saved-point (point)))
      (cond ((nth 3 parse)
             (re-search-forward
              (concat "\\([^\\]\\|^\\)" (string (nth 3 parse)))
              (save-excursion (end-of-line) (point)) t))
            ((nth 7 parse)
             (forward-line))
            ((or (nth 4 parse)
                 (and (eq (char-before) ?\/) (eq (char-after) ?\*)))
             (re-search-forward "\\*/"))
            (t
             (setq count (1- count))))
      (setq saved-point (point))))
  (point))


(defun gr-re-search-forward (regexp &optional bound noerror count)
  "Search forward but ignore strings and comments. Invokes
`re-search-forward' but treats the buffer as if strings and
comments have been removed."
  (let ((saved-point (point))
        (search-expr
         (cond ((null count)
                '(gr-re-search-forward-inner regexp bound 1))
               ((< count 0)
                '(gr-re-search-backward-inner regexp bound (- count)))
               ((> count 0)
                '(gr-re-search-forward-inner regexp bound count)))))
    (condition-case err
        (eval search-expr)
      (search-failed
       (goto-char saved-point)
       (unless noerror
         (error (error-message-string err)))))))


(defun gr-re-search-backward-inner (regexp &optional bound count)
  "Auxiliary function for `gr-re-search-backward'."
  (let ((parse)
        (saved-point (point-min)))
    (while (> count 0)
      (re-search-backward regexp bound)
      (when (and (> (point) (point-min))
                 (save-excursion (backward-char) (looking-at "/[/*]")))
        (forward-char))
      (setq parse (parse-partial-sexp saved-point (point)))
      (cond ((nth 3 parse)
             (re-search-backward
              (concat "\\([^\\]\\|^\\)" (string (nth 3 parse)))
              (save-excursion (beginning-of-line) (point)) t))
            ((nth 7 parse)
             (goto-char (nth 8 parse)))
            ((or (nth 4 parse)
                 (and (eq (char-before) ?/) (eq (char-after) ?*)))
             (re-search-backward "/\\*"))
            (t
             (setq count (1- count))))))
  (point))


(defun gr-re-search-backward (regexp &optional bound noerror count)
  "Search backward but ignore strings and comments. Invokes
`re-search-backward' but treats the buffer as if strings and
comments have been removed."
  (let ((saved-point (point))
        (search-expr
         (cond ((null count)
                '(gr-re-search-backward-inner regexp bound 1))
               ((< count 0)
                '(gr-re-search-forward-inner regexp bound (- count)))
               ((> count 0)
                '(gr-re-search-backward-inner regexp bound count)))))
    (condition-case err
        (eval search-expr)
      (search-failed
       (goto-char saved-point)
       (unless noerror
         (error (error-message-string err)))))))


(defun gr-continued-var-decl-list-p ()
  "Return non-nil if point is inside a continued variable declaration
list."
  (interactive)
  (let ((start (save-excursion (gr-re-search-backward "\\<var\\>" nil t))))
    (and start
	 (save-excursion (re-search-backward "\n" start t))
	 (not (save-excursion
		(gr-re-search-backward
		 ";\\|[^, \t][ \t]*\\(/[/*]\\|$\\)" start t))))))


;; --- Font Lock ---

(defun gr-inside-param-list-p ()
  "Return non-nil if point is inside a function parameter list."
  (condition-case err
      (save-excursion
	(up-list -1)
	(and (looking-at "(")
	     (progn (backward-word 1)
		    (or (looking-at "function")
			(progn (backward-word 1) (looking-at "function"))))))
    (error nil)))


(defconst gr-function-heading-1-re
  "^[ \t]*function[ \t]+\\(\\w+\\)"
  "Regular expression matching the start of a function header.")

(defconst gr-function-heading-2-re
  "^[ \t]*\\(\\w+\\)[ \t]*:[ \t]*function\\>"
  "Regular expression matching the start of a function entry in
  an associative array.")

(defconst gr-keyword-re
  (regexp-opt '("abstract" "break" "case" "catch" "class" "const"
                "continue" "def" "debugger" "default" "delete" "do" "else"
                "enum" "export" "extends" "final" "finally" "for"
                "function" "goto" "if" "implements" "import" "in"
                "instanceof" "interface" "native" "new" "package"
                "private" "protected" "public" "return" "static"
                "super" "switch" "synchronized" "this" "throw"
                "throws" "transient" "try" "typeof" "var" "void"
                "volatile" "while" "with") 'words)
  "Regular expression matching any Groovy keyword.")

(defconst gr-basic-type-re
  (regexp-opt '("boolean" "byte" "char"
                "true" "false" "null"
                "[dD]ouble" "[fF]loat" "int" "Integer" "[Ll]ong"
                "short" "void") 'words)
  "Regular expression matching any predefined type in Groovy.")

(defconst gr-constant-re
  (regexp-opt '() 'words)
  "Regular expression matching any future reserved words in Groovy.")


(defconst gr-font-lock-keywords-1
  (list
   "\\<import\\>"
   (list gr-function-heading-1-re 1 font-lock-function-name-face)
   (list gr-function-heading-2-re 1 font-lock-function-name-face)
   (list "[=(][ \t]*\\(/.*?[^\\]/\\w*\\)" 1 font-lock-string-face))
  "Level one font lock.")

(defconst gr-font-lock-keywords-2
  (append gr-font-lock-keywords-1
          (list (list gr-keyword-re 1 font-lock-keyword-face)
                (cons gr-basic-type-re font-lock-type-face)
                (cons gr-constant-re font-lock-constant-face)))
  "Level two font lock.")


;; Limitations with variable declarations: There seems to be no
;; sensible way to highlight variables occuring after an initialized
;; variable in a variable list. For instance, in
;;
;;    var x, y = f(a, b), z
;;
;; z will not be highlighted.

(defconst gr-font-lock-keywords-3
  (append
   gr-font-lock-keywords-2
   (list

    ;; variable declarations
    (list
     (concat "\\<\\(const\\|var\\)\\>\\|" gr-basic-type-re)
     (list "\\(\\w+\\)[ \t]*\\([=;].*\\|,\\|/[/*]\\|$\\)"
	   nil
	   nil
	   '(1 font-lock-variable-name-face)))

    ;; continued variable declaration list
    (list
     (concat "^[ \t]*\\w+[ \t]*\\([,;=]\\|/[/*]\\|$\\)")
     (list "\\(\\w+\\)[ \t]*\\([=;].*\\|,\\|/[/*]\\|$\\)"
	   '(if (save-excursion (backward-char) (gr-continued-var-decl-list-p))
		(backward-word 1)
	      (end-of-line))
	   '(end-of-line)
	   '(1 font-lock-variable-name-face)))

    ;; formal parameters
    (list
     (concat "\\<function\\>\\([ \t]+\\w+\\)?[ \t]*([ \t]*\\w")
     (list "\\(\\w+\\)\\([ \t]*).*\\)?"
	   '(backward-char)
	   '(end-of-line)
	   '(1 font-lock-variable-name-face)))

    ;; continued formal parameter list
    (list
     (concat "^[ \t]*\\w+[ \t]*[,)]")
     (list "\\w+"
	   '(if (save-excursion (backward-char) (gr-inside-param-list-p))
		(backward-word 1)
	      (end-of-line))
	   '(end-of-line)
	   '(0 font-lock-variable-name-face)))))
  "Level three font lock.")

(defconst gr-font-lock-keywords
  '(gr-font-lock-keywords-3 gr-font-lock-keywords-1 gr-font-lock-keywords-2
                            gr-font-lock-keywords-3)
  "See `font-lock-keywords'.")


;; --- Indentation ---

(defconst gr-possibly-braceless-keyword-re
  (regexp-opt
   '("catch" "do" "else" "finally" "for" "if" "try" "while" "with")
   'words)
  "Regular expression matching keywords that are optionally
  followed by an opening brace.")

(defconst gr-indent-operator-re
  (concat "[-+*/%<>=&^|?:]\\([^-+*/]\\|$\\)\\|"
          (regexp-opt '("in" "instanceof") 'words))
  "Regular expression matching operators that affect indentation
  of continued expressions.")


(defun gr-looking-at-operator-p ()
  "Return non-nil if text after point is an operator (that is not
a comma)."
  (save-match-data
    (and (looking-at gr-indent-operator-re)
         (or (not (looking-at ":"))
             (save-excursion
               (and (gr-re-search-backward "[?:{]\\|\\<case\\>" nil t)
                    (looking-at "?")))))))


(defun gr-continued-expression-p ()
  "Returns non-nil if the current line continues an expression."
  (save-excursion
    (back-to-indentation)
    (or (gr-looking-at-operator-p)
        (and (gr-re-search-backward "\n" nil t)
	     (progn
	       (skip-chars-backward " \t")
               (unless (bobp)
                 (backward-char)
                 (and (> (point) (point-min))
                      (save-excursion (backward-char) (not (looking-at "[/*]/")))
                      (save-excursion (backward-char) (not (looking-at "->")))
                      (gr-looking-at-operator-p)
                      (and (progn (backward-char)
                                  (not (looking-at "++\\|--\\|/[/*]")))))))))))


(defun gr-end-of-do-while-loop-p ()
  "Returns non-nil if word after point is `while' of a do-while
statement, else returns nil. A braceless do-while statement
spanning several lines requires that the start of the loop is
indented to the same column as the current line."
  (interactive)
  (save-excursion
    (save-match-data
      (when (looking-at "\\s-*\\<while\\>")
	(if (save-excursion
	      (skip-chars-backward "[ \t\n]*}")
	      (looking-at "[ \t\n]*}"))
	    (save-excursion
	      (backward-list) (backward-word 1) (looking-at "\\<do\\>"))
	  (gr-re-search-backward "\\<do\\>" (point-at-bol) t)
	  (or (looking-at "\\<do\\>")
	      (let ((saved-indent (current-indentation)))
		(while (and (gr-re-search-backward "^[ \t]*\\<" nil t)
			    (/= (current-indentation) saved-indent)))
		(and (looking-at "[ \t]*\\<do\\>")
		     (not (gr-re-search-forward
			   "\\<while\\>" (point-at-eol) t))
		     (= (current-indentation) saved-indent)))))))))


(defun gr-ctrl-statement-indentation ()
  "Returns the proper indentation of the current line if it
starts the body of a control statement without braces, else
returns nil."
  (save-excursion
    (back-to-indentation)
    (when (save-excursion
            (and (not (looking-at "[{]"))
                 (progn
                   (gr-re-search-backward "[[:graph:]]" nil t)
                   (forward-char)
                   (when (= (char-before) ?\)) (backward-list))
                   (skip-syntax-backward " ")
                   (skip-syntax-backward "w")
                   (looking-at gr-possibly-braceless-keyword-re))
                 (not (gr-end-of-do-while-loop-p))))
      (save-excursion
        (goto-char (match-beginning 0))
        (+ (current-indentation) groovy-indent-level)))))


(defun gr-proper-indentation (parse-status)
  "Return the proper indentation for the current line."
  (save-excursion
    (back-to-indentation)
    (let ((ctrl-stmt-indent (gr-ctrl-statement-indentation))
          (same-indent-p (looking-at "[]})]\\|\\<case\\>\\|\\<default\\>"))
          (continued-expr-p (gr-continued-expression-p)))
      (cond (ctrl-stmt-indent)
	    ((gr-continued-var-decl-list-p)
	     (gr-re-search-backward "\\<var\\>" nil t)
	     (+ (current-indentation) groovy-indent-level))
            ((nth 1 parse-status)
             (goto-char (nth 1 parse-status))
             (if (looking-at "[({[][ \t]*\\(/[/*]\\|$\\)")
                 (progn
                   (skip-syntax-backward " ")
                   (when (= (char-before) ?\)) (backward-list))
                   (back-to-indentation)
                   (cond (same-indent-p
                          (current-column))
                         (continued-expr-p
                          (+ (current-column) (* 2 groovy-indent-level)))
                         (t
                          (+ (current-column) groovy-indent-level))))
               (unless same-indent-p
                 (forward-char)
                 (skip-chars-forward " \t"))
               (current-column)))
	    (continued-expr-p groovy-indent-level)
            (t 0)))))


(defun groovy-indent-line ()
  "Indent the current line as Groovy source text."
  (interactive)
  (let ((parse-status
         (save-excursion (parse-partial-sexp (point-min) (point-at-bol))))
        (offset (- (current-column) (current-indentation))))
    (when (not (nth 8 parse-status))
      (indent-line-to (gr-proper-indentation parse-status))
      (when (> offset 0) (forward-char offset)))))

(defun groovy-indent-block ()
  "Indent the current block"
  (interactive)
  (let ((here (point)))
    (save-excursion
      (forward-sexp)
      (indent-region here (point)))))


;; --- Filling ---

;; FIXME: It should be possible to use the more sofisticated function
;; `c-fill-paragraph' in `cc-cmds.el' instead. However, just setting
;; `fill-paragraph-function' to `c-fill-paragraph' does not work;
;; inside `c-fill-paragraph', `fill-paragraph-function' evaluates to
;; nil!?

(defun gr-backward-paragraph ()
  "Move backward to start of paragraph. Postcondition: Point is at
beginning of buffer or the previous line contains only whitespace."
  (forward-line -1)
  (while (not (or (bobp) (looking-at "^[ \t]*$")))
    (forward-line -1))
  (when (not (bobp)) (forward-line 1)))


(defun gr-forward-paragraph ()
  "Move forward to end of paragraph. Postcondition: Point is at
end of buffer or the next line contains only whitespace."
  (forward-line 1)
  (while (not (or (eobp) (looking-at "^[ \t]*$")))
    (forward-line 1))
  (when (not (eobp)) (backward-char 1)))


(defun gr-fill-block-comment-paragraph (parse-status justify)
  "Fill current paragraph as a block comment. PARSE-STATUS is the
result of `parse-partial-regexp' from beginning of buffer to
point. JUSTIFY has the same meaning as in `fill-paragraph'."
  (let ((offset (save-excursion
                  (goto-char (nth 8 parse-status)) (current-indentation))))
    (save-excursion
      (save-restriction
        (narrow-to-region (save-excursion
                            (goto-char (nth 8 parse-status)) (point-at-bol))
                          (save-excursion
			    (goto-char (nth 8 parse-status))
			    (re-search-forward "*/")))
        (narrow-to-region (save-excursion
                            (gr-backward-paragraph)
                            (when (looking-at "^[ \t]*$") (forward-line 1))
                            (point))
                          (save-excursion
                            (gr-forward-paragraph)
                            (when (looking-at "^[ \t]*$") (backward-char))
                            (point)))
        (goto-char (point-min))
        (while (not (eobp))
          (delete-horizontal-space)
          (forward-line 1))
        (let ((fill-column (- fill-column offset))
              (fill-paragraph-function nil))
          (fill-paragraph justify))

        ;; In Emacs 21.4 as opposed to CVS Emacs 22,
        ;; `fill-paragraph' seems toadd a newline at the end of the
        ;; paragraph. Remove it!
        (goto-char (point-max))
        (when (looking-at "^$") (backward-delete-char 1))

        (goto-char (point-min))
        (while (not (eobp))
          (indent-to offset)
          (forward-line 1))))))


(defun gr-sline-comment-par-start ()
  "Return point at the beginning of the line where the current
single-line comment paragraph starts."
  (save-excursion
    (beginning-of-line)
    (while (and (not (bobp))
                (looking-at "^[ \t]*//[ \t]*[[:graph:]]"))
      (forward-line -1))
    (unless (bobp) (forward-line 1))
    (point)))


(defun gr-sline-comment-par-end ()
  "Return point at end of current single-line comment paragraph."
  (save-excursion
    (beginning-of-line)
    (while (and (not (eobp))
                (looking-at "^[ \t]*//[ \t]*[[:graph:]]"))
      (forward-line 1))
    (unless (bobp) (backward-char))
    (point)))


(defun gr-sline-comment-offset (line)
  "Return the column at the start of the current single-line
comment paragraph."
  (save-excursion
    (goto-line line)
    (re-search-forward "//" (point-at-eol))
    (goto-char (match-beginning 0))
    (current-column)))


(defun gr-sline-comment-text-offset (line)
  "Return the column at the start of the text of the current
single-line comment paragraph."
  (save-excursion
    (goto-line line)
    (re-search-forward "//[ \t]*" (point-at-eol))
    (current-column)))


(defun gr-at-empty-sline-comment-p ()
  "Return non-nil if inside an empty single-line comment."
  (and (save-excursion
         (beginning-of-line)
         (not (looking-at "^.*//.*[[:graph:]]")))
       (save-excursion
         (re-search-backward "//" (point-at-bol) t))))


(defun gr-fill-sline-comments (parse-status justify)
  "Fill current paragraph as a sequence of single-line comments.
PARSE-STATUS is the result of `parse-partial-regexp' from
beginning of buffer to point. JUSTIFY has the same meaning as in
`fill-paragraph'."
  (when (not (gr-at-empty-sline-comment-p))
    (let* ((start (gr-sline-comment-par-start))
           (start-line (1+ (count-lines (point-min) start)))
           (end (gr-sline-comment-par-end))
           (offset (gr-sline-comment-offset start-line))
           (text-offset (gr-sline-comment-text-offset start-line)))
      (save-excursion
        (save-restriction
          (narrow-to-region start end)
          (goto-char (point-min))
          (while (re-search-forward "^[ \t]*//[ \t]*" nil t)
            (replace-match "")
            (forward-line 1))
          (let ((fill-paragraph-function nil)
                (fill-column (- fill-column text-offset)))
            (fill-paragraph justify))

          ;; In Emacs 21.4 as opposed to CVS Emacs 22,
          ;; `fill-paragraph' seems toadd a newline at the end of the
          ;; paragraph. Remove it!
          (goto-char (point-max))
          (when (looking-at "^$") (backward-delete-char 1))

          (goto-char (point-min))
          (while (not (eobp))
            (indent-to offset)
            (insert "//")
            (indent-to text-offset)
            (forward-line 1)))))))


(defun gr-trailing-comment-p (parse-status)
  "Return non-nil if inside a trailing comment. PARSE-STATUS is
the result of `parse-partial-regexp' from beginning of buffer to
point."
  (save-excursion
    (when (nth 4 parse-status)
      (goto-char (nth 8 parse-status))
      (skip-chars-backward " \t")
      (not (bolp)))))


(defun gr-block-comment-p (parse-status)
  "Return non-nil if inside a block comment. PARSE-STATUS is the
result of `parse-partial-regexp' from beginning of buffer to
point."
  (save-excursion
    (save-match-data
      (when (nth 4 parse-status)
        (goto-char (nth 8 parse-status))
        (looking-at "/\\*")))))


(defun groovy-fill-paragraph (&optional justify)
  "If inside a comment, fill the current comment paragraph.
Trailing comments are ignored."
  (interactive)
  (let ((parse-status (parse-partial-sexp (point-min) (point))))
    (when (and (nth 4 parse-status)
               (not (gr-trailing-comment-p parse-status)))
      (if (gr-block-comment-p parse-status)
          (gr-fill-block-comment-paragraph parse-status justify)
        (gr-fill-sline-comments parse-status justify))))
  t)


;; --- Imenu ---

(defconst gr-imenu-generic-expression
  (list
   (list
    nil
    "function\\s-+\\(\\w+\\)\\s-*("
    1))
  "Regular expression matching top level procedures. Used by imenu.")


;; --- Main Function ---

;;;###autoload
(defun groovy-mode ()
  "Major mode for editing Groovy source text.

Key bindings:

\\{groovy-mode-map}"
  (interactive)
  (kill-all-local-variables)

  (use-local-map groovy-mode-map)
  (set-syntax-table groovy-mode-syntax-table)
  (set (make-local-variable 'indent-line-function) 'groovy-indent-line)
  (set (make-local-variable 'font-lock-defaults) (list gr-font-lock-keywords))

  (set (make-local-variable 'parse-sexp-ignore-comments) t)

  (define-key groovy-mode-map [(control meta ?q)] 'groovy-indent-block)

  ;; Comments
  (setq comment-start "// ")
  (setq comment-end "")
  (set (make-local-variable 'fill-paragraph-function)
       'groovy-fill-paragraph)

  ;; Imenu
  (setq imenu-case-fold-search nil)
  (set (make-local-variable 'imenu-generic-expression)
       gr-imenu-generic-expression)

  (setq major-mode 'groovy-mode)
  (setq mode-name "Groovy")
  (run-hooks 'groovy-mode-hook))


(provide 'groovy-mode)
;;; groovy.el ends here
