;;; nix-mode.el --- Major mode for editing .nix files -*- lexical-binding: t -*-

;; Maintainer: Matthew Bauer <mjbauer95@gmail.com>
;; Homepage: https://github.com/matthewbauer/nix-mode
;; Version: 1.2.1
;; Keywords: nix, languages, tools, unix
;; Package-Requires: ((emacs "24.3"))

;; This file is NOT part of GNU Emacs.

;;; Commentary:

;; A major mode for editing Nix expressions (.nix files).  See the Nix manual
;; for more information available at https://nixos.org/nix/manual/.

;;; Code:

(require 'nix-format nil 'noerror)

(defgroup nix nil
  "Nix-related customizations"
  :group 'languages)

(defgroup nix-mode nil
  "Nix mode customizations"
  :group 'nix)

(defgroup nix-faces nil
  "Nix faces."
  :group 'nix
  :group 'faces)

(defface nix-keyword-face
  '((t :inherit font-lock-keyword-face))
  "Face used to highlight Nix keywords."
  :group 'nix-faces)

(defface nix-keyword-warning-face
  '((t :inherit font-lock-warning-face))
  "Face used to highlight Nix warning keywords."
  :group 'nix-faces)

(defface nix-builtin-face
  '((t :inherit font-lock-builtin-face))
  "Face used to highlight Nix builtins."
  :group 'nix-faces)

(defface nix-constant-face
  '((t :inherit font-lock-constant-face))
  "Face used to highlight Nix constants."
  :group 'nix-faces)

(defface nix-attribute-face
  '((t :inherit font-lock-variable-name-face))
  "Face used to highlight Nix attributes."
  :group 'nix-faces)

(defface nix-antiquote-face
  '((t :inherit font-lock-preprocessor-face))
  "Face used to highlight Nix antiquotes."
  :group 'nix-faces)

(defvar nix-system-types
  '("x86_64-linux" "i686-linux" "aarch64-linux" "x86_64-darwin")
  "List of supported systems.")

;;; Syntax coloring

(defconst nix-keywords
  '("if" "then"
    "else" "with"
    "let" "in"
    "rec" "inherit"
    "or"))

(defconst nix-builtins
  '("builtins" "baseNameOf"
    "derivation" "dirOf"
    "true" "false" "null"
    "isNull" "toString"
    "fetchTarball" "import"
    "map" "removeAttrs"))

(defconst nix-warning-keywords
  '("assert" "abort" "throw"))

(defconst nix-re-file-path
  "[a-zA-Z0-9._\\+-]*\\(/[a-zA-Z0-9._\\+-]+\\)+")

(defconst nix-re-url
  "[a-zA-Z][a-zA-Z0-9\\+-\\.]*:[a-zA-Z0-9%/\\?:@&=\\+\\$,_\\.!~\\*'-]+")

(defconst nix-re-bracket-path
  "<[a-zA-Z0-9._\\+-]+\\(/[a-zA-Z0-9._\\+-]+\\)*>")

(defconst nix-re-variable-assign
  "\\<\\([a-zA-Z_][a-zA-Z0-9_'\-\.]*\\)[ \t]*=[^=]")

(defconst nix-font-lock-keywords
  `(
    (,(regexp-opt nix-keywords 'symbols) 0 'nix-keyword-face)
    (,(regexp-opt nix-warning-keywords 'symbols) 0 'nix-keyword-warning-face)
    (,(regexp-opt nix-builtins 'symbols) 0 'nix-builtin-face)
    (,nix-re-url 0 'nix-constant-face)
    (,nix-re-file-path 0 'nix-constant-face)
    (,nix-re-variable-assign 1 'nix-attribute-face)
    (,nix-re-bracket-path 0 'nix-constant-face)
    (nix--syntax-match-antiquote 0 'nix-antiquote-face t)
    )
  "Font lock keywords for nix.")

(defconst nix--variable-char "[a-zA-Z0-9_'\-]")

(defvar nix-mode-abbrev-table
  (make-abbrev-table)
  "Abbrev table for Nix mode.")

(makunbound 'nix-mode-syntax-table)

(defvar nix-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?/ ". 14" table)
    (modify-syntax-entry ?* ". 23" table)
    (modify-syntax-entry ?# "< b" table)
    (modify-syntax-entry ?\n "> b" table)
    ;; We handle strings
    (modify-syntax-entry ?\" "." table)
    ;; We handle escapes
    (modify-syntax-entry ?\\ "." table)
    table)
  "Syntax table for Nix mode.")

(defun nix--syntax-match-antiquote (limit)
  "Find antiquote within a Nix expression up to LIMIT."
  (unless (> (point) limit)
    (if (get-text-property (point) 'nix-syntax-antiquote)
        (progn
          (set-match-data (list (point) (1+ (point))))
          (forward-char 1)
          t)
      (let ((pos (next-single-char-property-change (point) 'nix-syntax-antiquote
                                                   nil limit)))
        (when (and pos (not (> pos limit)))
          (goto-char pos)
          (let ((char (char-after pos)))
            (pcase char
              (`?{
               (forward-char 1)
               (set-match-data (list (1- pos) (point)))
               t)
              (`?}
               (forward-char 1)
               (set-match-data (list pos (point)))
               t))))))))

(defun nix--mark-string (pos string-type)
  "Mark string as a Nix string.

POS position of start of string
STRING-TYPE type of string based off of Emacs syntax table types"
  (put-text-property pos (1+ pos)
                     'syntax-table (string-to-syntax "|"))
  (put-text-property pos (1+ pos)
                     'nix-string-type string-type))

(defun nix--get-parse-state (pos)
  "Get the result of `syntax-ppss' at POS."
  (save-excursion (save-match-data (syntax-ppss pos))))

(defun nix--get-string-type (parse-state)
  "Get the type of string based on PARSE-STATE."
  (let ((string-start (nth 8 parse-state)))
    (and string-start (get-text-property string-start 'nix-string-type))))

(defun nix--open-brace-string-type (parse-state)
  "Determine if this is an open brace string type based on PARSE-STATE."
  (let ((open-brace (nth 1 parse-state)))
    (and open-brace (get-text-property open-brace 'nix-string-type))))

(defun nix--open-brace-antiquote-p (parse-state)
  "Determine if this is an open brace antiquote based on PARSE-STATE."
  (let ((open-brace (nth 1 parse-state)))
    (and open-brace (get-text-property open-brace 'nix-syntax-antiquote))))

(defun nix--single-quotes ()
  "Handle Nix single quotes."
  (let* ((start (match-beginning 0))
         (end (match-end 0))
         (context (nix--get-parse-state start))
         (string-type (nix--get-string-type context)))
    (unless (or (equal string-type ?\")
                (and (equal string-type nil)
                     (< 1 start)
                     (string-match-p nix--variable-char
                                     (buffer-substring (1- start) start))))
      (when (equal string-type nil)
        (nix--mark-string start ?\')
        (setq start (+ 2 start)))
      (when (equal (mod (- end start) 3) 2)
        (let ((str-peek (buffer-substring end (min (point-max) (+ 2 end)))))
          (if (member str-peek '("${" "\\n" "\\r" "\\t"))
              (goto-char (+ 2 end))
            (nix--mark-string (1- end) ?\')))))))

(defun nix--escaped-antiquote-dq-style ()
  "Handle Nix escaped antiquote dq style."
  (let* ((start (match-beginning 0))
         (ps (nix--get-parse-state start))
         (string-type (nix--get-string-type ps)))
    (when (equal string-type ?\')
      (nix--antiquote-open-at (1+ start) ?\'))))

(defun nix--double-quotes ()
  "Handle Nix double quotes."
  (let* ((pos (match-beginning 0))
         (ps (nix--get-parse-state pos))
         (string-type (nix--get-string-type ps)))
    (unless (equal string-type ?\')
      (nix--mark-string pos ?\"))))

(defun nix--antiquote-open-at (pos string-type)
  "Handle Nix antiquote open at based on POS and STRING-TYPE."
  (put-text-property pos (1+ pos)
                     'syntax-table (string-to-syntax "|"))
  (put-text-property pos (+ 2 pos)
                     'nix-string-type string-type)
  (put-text-property (1+ pos) (+ 2 pos)
                     'nix-syntax-antiquote t))

(defun nix--antiquote-open ()
  "Handle Nix antiquote open."
  (let* ((start (match-beginning 0))
         (ps (nix--get-parse-state start))
         (string-type (nix--get-string-type ps)))
    (when string-type
      (nix--antiquote-open-at start string-type))))

(defun nix--antiquote-close-open ()
  "Handle Nix antiquote close then open."
  (let* ((start (match-beginning 0))
         (ps (nix--get-parse-state start))
         (string-type (nix--get-string-type ps)))
    (if string-type
        (nix--antiquote-open-at (1+ start) string-type)
      (when (nix--open-brace-antiquote-p ps)
        (let ((string-type (nix--open-brace-string-type ps)))
          (put-text-property start (+ 3 start)
                             'nix-string-type string-type)
          (put-text-property start (1+ start)
                             'nix-syntax-antiquote t)
          (put-text-property (+ 2 start) (+ 3 start)
                             'nix-syntax-antiquote t))))))

(defun nix--antiquote-close ()
  "Handle Nix antiquote close."
  (let* ((start (match-beginning 0))
         (ps (nix--get-parse-state start)))
    (unless (nix--get-string-type ps)
      (let ((string-type (nix--open-brace-string-type ps)))
        (when string-type
          (put-text-property start (1+ start)
                             'nix-string-type string-type)
          (put-text-property start (1+ start)
                             'nix-syntax-antiquote t)
          (let ((ahead (buffer-substring (1+ start) (min (point-max) (+ 5 start)))))
            (pcase string-type
              (`?\" (cond
                     ((or (string-match "^\\\\\"" ahead)
                          (string-match "^\\\\\\${" ahead))
                      (nix--mark-string (1+ start) string-type)
                      (goto-char (+ start (match-end 0) 1)))
                     ((string-match-p "^\"" ahead)
                      (goto-char (+ 2 start)))
                     ((< (1+ start) (point-max))
                      (nix--mark-string (1+ start) string-type)
                      (goto-char (+ 2 start)))))
              (`?\' (cond
                     ((or (string-match "^'''" ahead)
                          (string-match "^''\\${" ahead)
                          (string-match "^''\\\\[nrt]" ahead))
                      (nix--mark-string (1+ start) string-type)
                      (goto-char (+ start (match-end 0) 1)))
                     ((string-match-p "^''" ahead)
                      (goto-char (+ 3 start)))
                     ((< (1+ start) (point-max))
                      (nix--mark-string (1+ start) string-type)
                      (goto-char (+ 2 start))))))))))))

(defun nix-syntax-propertize (start end)
  "Special syntax properties for Nix from START to END."
  (goto-char start)
  (remove-text-properties start end
                          '(syntax-table nil nix-string-type nil nix-syntax-antiquote nil))
  (funcall
   (syntax-propertize-rules
    ("\\\\\\\\"
     (0 nil))
    ("\\\\\""
     (0 nil))
    ("\\\\\\${"
     (0 (ignore (nix--escaped-antiquote-dq-style))))
    ("'\\{2,\\}"
     (0 (ignore (nix--single-quotes))))
    ("}\\${"
     (0 (ignore (nix--antiquote-close-open))))
    ("\\${"
     (0 (ignore (nix--antiquote-open))))
    ("}"
     (0 (ignore (nix--antiquote-close))))
    ("\""
     (0 (ignore (nix--double-quotes)))))
   start end))

;;; Indentation

(defun nix-indent-level-parens ()
  "Find indent level based on parens."
  (save-excursion
    (beginning-of-line)

    (let ((p1 (point))
          (p2 (nth 1 (syntax-ppss)))
          (n 0))

      ;; prevent moving beyond buffer
      (if (eq p2 1)
          (setq n (1+ n)))

      (while (and p2 (not (eq p2 1))) ;; make sure p2 > 1
        (goto-char p2)
        (backward-char)
        (let ((l1 (line-number-at-pos p1))
              (l2 (line-number-at-pos p2)))
          (if (not (eq l1 l2))
              (setq n (1+ n))))
        (setq p1 p2)
        (setq p2 (nth 1 (syntax-ppss)))

        ;; make sure we don't go beyond buffer
        (if (eq p2 1)
            (setq n (1+ n))))

      n)))

(defun nix-indent-level-is-closing ()
  "Go forward from beginning of line."
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward "[:space:]")

    (or ;; any of these should -1 indent level
     (looking-at ")")
     (looking-at "}")
     (looking-at "]")
     (looking-at "''")
     (looking-at ",")
     (looking-at "in[[:space:]]")
     (looking-at "in$"))))

(defun nix-indent-level-is-hanging ()
  "Is hanging?"
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward "[:space:]")

    (if (or
         ;; (looking-at ",")
         (looking-at "{")) nil

      (forward-line -1)
      (end-of-line)
      (skip-chars-backward "\n[:space:]")

      ;; skip through any comments in the way
      (while (nth 4 (syntax-ppss))
        (goto-char (nth 8 (syntax-ppss)))
        (skip-chars-backward "\n[:space:]"))

      (not (or
            (looking-back "{" 1)
            (looking-back "}" 1)
            (looking-back ":" 1)
            (looking-back ";" 1))))))

(defun nix-indent-prev-level-is-hanging ()
  "Is the previous level hanging?"
  (save-excursion
    (beginning-of-line)
    (skip-chars-backward "\n[:space:]")
    (nix-indent-level-is-hanging)))

(defun nix-indent-prev-level ()
  "Get the indent level of the previous line."
  (save-excursion
    (beginning-of-line)
    (skip-chars-backward "\n[:space:]")
    (current-indentation)))

(defun nix-indent-level ()
  "Get current indent level."
  (if (nix-indent-level-is-hanging)
      (+ (nix-indent-prev-level)
         (* tab-width (+ (if (nix-indent-prev-level-is-hanging) 0 1)
                         (if (nix-indent-level-is-closing) -1 0))))
    (* tab-width (+ (nix-indent-level-parens)
                    (if (nix-indent-level-is-closing) -1 0)))))

(defun nix-indent-line ()
  "Indent current line in a Nix expression."
  (interactive)
  (cond

   ;; comment
   ((save-excursion
      (beginning-of-line)
      (nth 4 (syntax-ppss)))
    (indent-line-to (nix-indent-prev-level)))

   ;; string
   ((save-excursion
      (beginning-of-line)
      (nth 3 (syntax-ppss)))
    (indent-line-to (+ (nix-indent-prev-level)
                       (* tab-width (+ (if (save-excursion
                                             (forward-line -1)
                                             (end-of-line)
                                             (skip-chars-backward "[:space:]")
                                             (looking-back "''" 0)) 1 0)
                                       (if (save-excursion
                                             (beginning-of-line)
                                             (skip-chars-forward
                                              "[:space:]")
                                             (looking-at "''")
                                             ) -1 0)
                                       )))))

   ;; else
   (t
    (indent-line-to (nix-indent-level)))))

;; Key maps

(defvar nix-mode-menu (make-sparse-keymap "Nix")
  "Menu for Nix mode.")

(defvar nix-mode-map (make-sparse-keymap)
  "Local keymap used for Nix mode.")

(defun nix-create-keymap ()
  "Create the keymap associated with the Nix mode."
  (define-key nix-mode-map "\C-c\C-r" 'nix-format-buffer))

(defun nix-create-menu ()
  "Create the Nix menu as shown in the menu bar."
  (let ((m '("Nix"
	     ["Format buffer" nix-format-buffer t])
	   ))
    (easy-menu-define ada-mode-menu nix-mode-map "Menu keymap for Nix mode" m)))

(nix-create-keymap)
(nix-create-menu)

(when (require 'company nil 'noerror) (require 'nix-company nil 'noerror))

(when (require 'mmm-mode nil 'noerror) (require 'nix-mode-mmm nil 'noerror))

;;;###autoload
(define-derived-mode nix-mode prog-mode "Nix"
  "Major mode for editing Nix expressions.

The following commands may be useful:

  '\\[newline-and-indent]'
    Insert a newline and move the cursor to align with the previous
    non-empty line.

  '\\[fill-paragraph]'
    Refill a paragraph so that all lines are at most `fill-column'
    lines long.  This should do the right thing for comments beginning
    with `#'.  However, this command doesn't work properly yet if the
    comment is adjacent to code (i.e., no intervening empty lines).
    In that case, select the text to be refilled and use
    `\\[fill-region]' instead.

The hook `nix-mode-hook' is run when Nix mode is started.

\\{nix-mode-map}
"
  :group 'nix-mode
  :syntax-table nix-mode-syntax-table
  :abbrev-table nix-mode-abbrev-table

  ;; Disable hard tabs and set tab to 2 spaces
  ;; Recommended by nixpkgs manual: https://nixos.org/nixpkgs/manual/#sec-syntax
  (setq-local indent-tabs-mode nil)
  (setq-local tab-width 2)

  ;; Font lock support.
  (setq-local font-lock-defaults '(nix-font-lock-keywords))

  ;; Special syntax properties for Nix
  (setq-local syntax-propertize-function 'nix-syntax-propertize)

  ;; Look at text properties when parsing
  (setq-local parse-sexp-lookup-properties t)

  ;; Automatic indentation [C-j]
  (setq-local indent-line-function 'nix-indent-line)

  ;; Indenting of comments
  (setq-local comment-start "# ")
  (setq-local comment-end "")
  (setq-local comment-start-skip "\\(^\\|\\s-\\);?#+ *")
  (setq-local comment-multi-line t)

  ;; Filling of comments
  (setq-local adaptive-fill-mode t)
  (setq-local paragraph-start "[ \t]*\\(#+[ \t]*\\)?$")
  (setq-local paragraph-separate paragraph-start)

  (easy-menu-add nix-mode-menu nix-mode-map))

;;;###autoload
(progn
  (add-to-list 'auto-mode-alist '("\\.nix\\'" . nix-mode))
  (add-to-list 'auto-mode-alist '("\\.nix.in\\'" . nix-mode)))

(provide 'nix-mode)
;;; nix-mode.el ends here
