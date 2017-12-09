;;; nginx-mode.el --- major mode for editing nginx config files

;; Copyright 2010 Andrew J Cosgriff <andrew@cosgriff.name>

;; Author: Andrew J Cosgriff <andrew@cosgriff.name>
;; Maintainer: Andrew J Cosgriff <andrew@cosgriff.name>
;; Created: 15 Oct 2010
;; Version: 1.1.9
;; Keywords: languages, nginx

;; available from http://github.com/ajc/nginx-mode

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a quick mode for editing Nginx config files, as I didn't find
;; anything else around that did quite this much.

;; Many thanks to the authors of puppet-mode.el, from where I found a
;; useful indentation function that I've modified to suit this situation.

;; Put this file into your load-path and the following into your ~/.emacs:
;;   (require 'nginx-mode)

;;; Code:


;;;;##########################################################################
;;;;  User Options, Variables
;;;;##########################################################################

(defcustom nginx-indent-level 4
  "*Indentation of Nginx statements."
  :type 'integer :group 'nginx)

(defcustom nginx-indent-tabs-mode nil
  "*Indentation can insert tabs in nginx mode if this is non-nil."
  :type 'boolean :group 'nginx)

(defvar nginx-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?# "< b" table)
    (modify-syntax-entry ?\n "> b" table)
    table)
  "Syntax table for `nginx-mode'.")

(defvar nginx-font-lock-keywords
  (list '("^\\([ \t]+\\)?\\([A-Za-z09_]+\\)" 2 font-lock-keyword-face t)
	;; uncomment the next one if you want your eyes to bleed
	;; (it'll highlight parentheses and curly braces)
	;;'("\\(\{\\|\}\\|\(\\|\)\\)" . font-lock-pseudo-keyword-face)
	'("^\\([ \t]+\\)?rewrite[ \t]+.+[ \t]+\\(permanent\\|redirect\\|break\\|last\\);$" 2 font-lock-function-name-face)
	'("\\(\$[0-9]+\\)[^0-9]" 1 font-lock-constant-face)
	'("\$[A-Za-z0-9_\-]+" . font-lock-variable-name-face)
	'("[ \t]+\\(on\\|off\\);$" 1 font-lock-constant-face)
	'("[A-Za-z0-9_\-]+\\([ \t]+[^ \t\n]+\\)?[ \t]+\\([^ \t\n]+\\)[ \t]+{" 2 font-lock-function-name-face)))


;;;;##########################################################################
;;;;  Code
;;;;##########################################################################

(defun nginx-block-indent ()
  "If point is in a block, return the indentation of the first line of that
block (the line containing the opening brace).  Used to set the indentation
of the closing brace of a block."
  (save-excursion
    (save-match-data
      (let ((opoint (point))
            (apoint (search-backward "{" nil t)))
        (when apoint
          ;; This is a bit of a hack and doesn't allow for strings.  We really
          ;; want to parse by sexps at some point.
          (let ((close-braces (count-matches "}" apoint opoint))
                (open-braces 0))
            (while (and apoint (> close-braces open-braces))
              (setq apoint (search-backward "{" nil t))
              (when apoint
                (setq close-braces (count-matches "}" apoint opoint))
                (setq open-braces (1+ open-braces)))))
          (if apoint
              (current-indentation)
            nil))))))


(defun nginx-comment-line-p ()
  "Return non-nil iff this line is a comment."
  (save-excursion
    (save-match-data
      (beginning-of-line)
      (looking-at "^\\s-*#"))))

(defun nginx-indent-line ()
  "Indent current line as nginx code."
  (interactive)
  (beginning-of-line)
  (if (bobp)
      (indent-line-to 0)                ; First line is always non-indented
    (let ((not-indented t)
          (block-indent (nginx-block-indent))
          cur-indent)
      (cond
       ((and (looking-at "^\\s-*}\\s-*$") block-indent)
        ;; This line contains a closing brace and we're at the inner
        ;; block, so we should indent it matching the indentation of
        ;; the opening brace of the block.
        (setq cur-indent block-indent))
       (t
        ;; Otherwise, we did not start on a block-ending-only line.
        (save-excursion
          ;; Iterate backwards until we find an indentation hint
          (while not-indented
            (forward-line -1)
            (cond
             ;; Comment lines are ignored unless we're at the start of the
             ;; buffer.
             ((nginx-comment-line-p)
              (if (bobp)
                  (setq not-indented nil)))

             ;; Brace or paren on a line by itself will already be indented to
             ;; the right level, so we can cheat and stop there.
             ((looking-at "^\\s-*}\\s-*")
              (setq cur-indent (current-indentation))
              (setq not-indented nil))

             ;; Indent by one level more than the start of our block.  We lose
             ;; if there is more than one block opened and closed on the same
             ;; line but it's still unbalanced; hopefully people don't do that.
             ((looking-at "^.*{[^\n}]*$")
              (setq cur-indent (+ (current-indentation) nginx-indent-level))
              (setq not-indented nil))

             ;; Start of buffer.
             ((bobp)
              (setq not-indented nil)))))))

      ;; We've figured out the indentation, so do it.
      (if (and cur-indent (> cur-indent 0))
	  (indent-line-to cur-indent)
        (indent-line-to 0)))))


(defvar nginx-mode-map
  (let
      ((map (make-sparse-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    (define-key map "\C-m" 'newline-and-indent)
    map)
  "Keymap for editing nginx config files.")

;;;###autoload
(define-derived-mode nginx-mode prog-mode "Nginx"
  "Major mode for highlighting nginx config files.

The variable nginx-indent-level controls the amount of indentation.
\\{nginx-mode-map}"
  :syntax-table nginx-mode-syntax-table

  (use-local-map nginx-mode-map)

  (set (make-local-variable 'comment-start) "# ")
  (set (make-local-variable 'comment-start-skip) "#+ *")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-auto-fill-only-comments) t)

  (set (make-local-variable 'indent-line-function) 'nginx-indent-line)
  (set (make-local-variable 'indent-tabs-mode) nginx-indent-tabs-mode)
  (set (make-local-variable 'require-final-newline) t)
  (set (make-local-variable 'paragraph-ignore-fill-prefix) t)
  (set (make-local-variable 'paragraph-start) "\f\\|[ 	]*$\\|#$")
  (set (make-local-variable 'paragraph-separate) "\\([ 	\f]*\\|#\\)$")

  (set (make-local-variable 'font-lock-defaults)
       '(nginx-font-lock-keywords nil)))

;;;###autoload
(add-to-list 'auto-mode-alist '("nginx\\.conf\\'"  . nginx-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("/nginx/.+\\.conf\\'" . nginx-mode))
;;;###autoload
(add-to-list
 'magic-fallback-mode-alist
 '("\\(?:.*\n\\)*\\(?:http\\|server\\|location .+\\|upstream .+\\)[ \n\t]+{"
   . nginx-mode))

(provide 'nginx-mode)

;;; nginx-mode.el ends here
