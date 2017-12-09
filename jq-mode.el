;;; jq-mode.el --- Edit jq scripts.

;; Copyright (C) 2015--2017 Bjarte Johansen

;; Author: Bjarte Johansen <Bjarte dot Johansen at gmail dot com>
;; Homepage: https://github.com/ljos/jq-mode
;; Package-Requires: ((emacs "25.1"))
;; Version: 0.3.0

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with jq-mode. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Mode for editing jq queries.

;;; Usage:

;; Add to your Emacs config:

;;  (add-to-list 'load-path "/path/to/jq-mode-dir")
;;  (autoload 'jq-mode "jq-mode.el"
;;   "Major mode for editing jq files" t)
;;  (add-to-list 'auto-mode-alist '("\\.jq\\'" . jq-mode))

;;; Code:
(defgroup jq nil
  "Major mode for editing jq queries."
  :group 'languages)

(defcustom jq-indent-offset 2
  "*Indentation offset for `jq-mode'."
  :group 'jq
  :type 'integer)

(defconst jq--keywords
  '("as"
    "break"
    "catch"
    "def"
    "elif" "else" "end"
    "foreach"
    "if" "import" "include"
    "label"
    "module"
    "reduce"
    "then" "try")
  "The keywords used in jq.")

(defun jq-indent-line ()
  "Indent current line as a jq-script."
  (interactive)
  (let ((indent-column 0)
        (current (current-indentation)))
    (save-mark-and-excursion
     (if (> 0 (forward-line -1))
         (setq indent-column (current-indentation))
       (end-of-line)
       (or (search-backward ";" (line-beginning-position) t)
           (back-to-indentation))
       (skip-chars-forward "[:space:]" (line-end-position))
       (when (looking-at-p
              (concat (regexp-opt (remove "end" jq--keywords)) "\\b"))
         (setq indent-column (+ indent-column jq-indent-offset)))))
    (save-mark-and-excursion
     (back-to-indentation)
     (save-mark-and-excursion
      (ignore-errors
        (up-list -1)
        (when (looking-at-p "(\\|{\\|\\[")
          (setq indent-column (1+ (current-column))))))
     (when (looking-at-p "|")
       (setq indent-column (+ indent-column jq-indent-offset)))
     (end-of-line)
     (delete-horizontal-space)
     (indent-line-to indent-column)))
  (when (let ((search-spaces-regexp t))
          (string-match-p "^ *$"
                          (buffer-substring-no-properties
                           (line-beginning-position)
                           (point))))
    (skip-chars-forward "[:space:]" (line-end-position))))

(defconst jq--builtins
  '("add" "all" "and" "any" "arrays" "ascii_upcase" "ascii_downcase"
    "booleans" "bsearch"
    "capture" "combinations" "contains"
    "debug" "del"
    "empty" "endswith" "env" "error" "explode"
    "finites" "first" "flatten" "floor" "from_entries" "fromdate"
    "fromdateiso8601" "fromjson" "fromstream"
    "getpath" "gmtime" "group_by" "gsub"
    "has"
    "implode" "in" "index" "indicies" "infinite" "input" "input_filename"
    "input_line_number" "inputs" "inside" "isfinite" "isinfinite" "isnan"
    "isnormal" "iterables"
    "join"
    "keys" "keys_unsorted"
    "last" "leaf_paths" "length" "limit" "ltrimstr"
    "map" "map_values" "match" "max" "max_by" "min" "min_by" "mktime"
    "modulemeta"
    "nan" "normals" "not" "now" "nth" "nulls" "numbers"
    "objects" "or"
    "path" "paths"
    "range" "recurse" "recurse_down" "reverse" "rindex" "rtrimstr"
    "scalars" "scan" "select" "setpath" "sort" "sort_by" "split" "split"
    "splits" "sqrt" "startswith" "strftime" "strings" "strptime" "sub"
    "test" "to_entries" "todate" "todateiso8601" "tojson" "tonumber" "tostream"
    "tostring" "transpose" "truncate_stream" "type"
    "unique" "unique_by" "until"
    "values"
    "walk" "while" "with_entries")
  "All builtin functions in jq.")

(defconst jq--escapings
  '("text" "json" "html" "uri" "csv" "tsv" "sh" "base64")
  "Jq escaping directives.")

(defconst jq-font-lock-keywords
  `( ;; Variables
    ("\\$\\w+" 0 font-lock-variable-name-face)
    ;; Format strings and escaping
    (,(concat "@" (regexp-opt jq--escapings) "\\b") . font-lock-type-face)
    ;; Keywords
    ,(concat "\\b" (regexp-opt jq--keywords) "\\b")))

(defvar jq-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `jq-mode'.")

(defvar jq-mode-syntax-table
  (let ((syntax-table (make-syntax-table)))
    ;; Strings
    (modify-syntax-entry ?\" "\"\"" syntax-table)

    ;; Comments
    (modify-syntax-entry ?# "<" syntax-table)
    (modify-syntax-entry ?\n ">" syntax-table)
    syntax-table)
  "Syntax table for `jq-mode.'")

(with-eval-after-load 'company-keywords
  (add-to-list 'company-keywords-alist
               `(jq-mode . ,(append jq--keywords
                                    jq--builtins))))

;;;###autoload
(define-derived-mode jq-mode prog-mode "jq"
  "Major mode for jq scripts.
\\{jq-mode-map}"
  :group 'jq
  (setq-local indent-line-function #'jq-indent-line)
  (setq-local font-lock-defaults '(jq-font-lock-keywords))
  (setq-local comment-start "# "))

;;; jq-interactively
(defgroup jq-interactive nil
  "Major mode for editing json with jq."
  :group 'languages)

(defcustom jq-interactive-command "jq"
  "Command to use for calling jq."
  :group 'jq-interactive
  :type 'string)

(defcustom jq-interactive-default-options ""
  "Command line options to pass to jq."
  :group 'jq-interactive
  :type 'string)

(defcustom jq-interactive-default-prompt "jq: "
  "Default prompt to use in minibuffer."
  :group 'jq-interactive
  :type 'string)

(defvar jq-interactive-history nil)

(defvar jq-interactive--last-minibuffer-contents "")
(defvar jq-interactive--positions nil)
(defvar jq-interactive--buffer nil)
(defvar jq-interactive--overlay nil)

(defun jq-interactive--run-command ()
  (with-temp-buffer
    (let ((output (current-buffer)))
      (with-current-buffer jq-interactive--buffer
        (call-process-region
         (point-min)
         (point-max)
         shell-file-name
         nil
         output
         nil
         shell-command-switch
         (format "%s %s %s"
                 jq-interactive-command
                 jq-interactive-default-options
                 (shell-quote-argument
                  jq-interactive--last-minibuffer-contents))))
      (ignore-errors
        (json-mode)
        (font-lock-fontify-region (point-min) (point-max)))
      (buffer-string))))

(defun jq-interactive--feedback ()
  (save-mark-and-excursion
   (let ((font-lock-defaults '(jq-font-lock-keywords)))
     (font-lock-fontify-region (point) (point-max))))
  (with-current-buffer jq-interactive--buffer
    (overlay-put jq-interactive--overlay
                 'after-string
                 (jq-interactive--run-command))))

(defun jq-interactive--minibuffer-setup ()
  (setq-local font-lock-defaults '(jq-font-lock-keywords)))

(defun jq-interactive--quit ()
  (remove-hook 'after-change-functions #'jq-interactive--update)
  (remove-hook 'minibuffer-setup-hook #'jq-interactive--minibuffer-setup)
  (delete-overlay jq-interactive--overlay))

(defun jq-interactive--update (beg end len)
  (let ((contents (minibuffer-contents-no-properties)))
    (unless (or (not (minibufferp))
                (and (string= "" contents)
                     (equal last-command 'previous-history-element))
                (string= contents jq-interactive--last-minibuffer-contents))
      (setq jq-interactive--last-minibuffer-contents contents)
      (jq-interactive--feedback))))

(defun jq-interactive-indent-line ()
  "Indents a jq expression in the jq-interactive mini-buffer."
  (interactive)
  (jq-indent-line)
  (save-mark-and-excursion
   (beginning-of-line)
   (insert-char ?\s (length jq-interactive-default-prompt)))
  (skip-chars-forward "[:space:]"))

(defvar jq-interactive-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map minibuffer-local-map)
    (define-key map (kbd "<tab>") #'jq-interactive-indent-line)
    (define-key map (kbd "C-j") #'electric-newline-and-maybe-indent)
    map)
  "Keymap for `jq-interactively'.")

;;;###autoload
(defun jq-interactively (beg end)
  "Runs jq interactively on a json buffer."
  (interactive
   (if (region-active-p)
       (list (region-beginning)
             (region-end))
     (list (point-min)
           (point-max))))
  (unwind-protect
      (progn
        (setq jq-interactive--overlay (make-overlay beg end))
        (overlay-put jq-interactive--overlay 'invisible t)
        (setq jq-interactive--positions (cons beg end))
        (setq jq-interactive--buffer (current-buffer))
        (setq jq-interactive--last-minibuffer-contents "")
        (jq-interactive--feedback)
        (add-hook 'after-change-functions #'jq-interactive--update)
        (add-hook 'minibuffer-setup-hook #'jq-interactive--minibuffer-setup)
        (save-mark-and-excursion
         (deactivate-mark)
         (read-from-minibuffer
          jq-interactive-default-prompt
          nil
          jq-interactive-map
          nil
          jq-interactive-history))
        (goto-char beg)
        (delete-region beg end)
        (insert (plist-get (overlay-properties jq-interactive--overlay)
                           'after-string)))
    (jq-interactive--quit)))

(provide 'jq-mode)

;;; jq-mode.el ends here
