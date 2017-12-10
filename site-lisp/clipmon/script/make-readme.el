;;; make-readme.el --- Convert elisp docs to markdown

; this file needs lots of refactoring
; or try the other packages


;; Copyright (C) 2011, Mitchel Humpherys
;; Copyright (C) 2013, Justine Tunney
;; Copyright (C) 2014 Brian Burns


;; Author: Mitchel Humpherys <mitch.special@gmail.com>
;; Keywords: tools, convenience
;; Version: 0.1.20141227

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This tool will let you easily convert elisp file headers to markdown text so
;; long as the file comments and documentation follow standard conventions
;; (like this file). This is because when you're writing an elisp module, the
;; module itself should be the canonical source of documentation. But it's not
;; very user-friendly or good marketing for your project to have an empty
;; README.md that refers people to your source code, and it's even worse if you
;; have to maintain two separate files that say the same thing.

;;; Installation:

;; None

;;; Usage:

;; The recommended way to use this tool is by putting the following code in
;; your Makefile and running `make README.md` (You don't even have to clone the
;; repository!):
;;
;;     README.md: make-readme.el YOUR-MODULE.el
;;     	emacs --script $< <YOUR-MODULE.el >$@ 2>/dev/null
;;
;;     make-readme.el:
;;     	wget -q -O $@ https://raw.github.com/mgalgs/make-readme/master/make-readme.el
;;
;;     .INTERMEDIATE: make-readme.el
;;
;; You can also invoke it directly with `emacs --script`:
;;
;;     $ emacs --script make-readme.el <elisp-file-to-parse.el 2>/dev/null
;;
;; All functions and macros in your module with docstrings will be documented
;; in the output unless they've been marked as private. Convention dictates
;; that private elisp functions have two hypens, like `cup--noodle`.

;;; Syntax:

;; In order for this module to do you any good, you should write your
;; file header comments in a way that make-readme.el
;; understands. An attempt has been made to support the most common
;; file header comment style, so hopefully you shouldn't have to do
;; anything... The following patterns at the beginning of a line are
;; special:
;;
;; o `;;; My Header` :: Creates a header
;; o `;; o My list item` :: Creates a list item
;; o `;; * My list item` :: Also creates a list item
;; o `;; - My list item` :: Also creates a list item
;;
;; Everything else is stripped of its leading semicolons and first
;; space and is passed directly out. Note that you can embed markdown
;; syntax directly in your comments. This means that you can embed
;; blocks of code in your comments by leading the line with 4 spaces
;; (in addition to the first space directly following the last
;; semicolon). For example:
;;
;;     (defun strip-comments (line)
;;       "Stip elisp comments from line"
;;       (replace-regexp-in-string "^;+ ?" "" line))
;;
;; We parse everything between `;;; Commentary:` and `;;; Code`. See
;; make-readme.el for an example (you might already be
;; looking at it... whoa, this is really getting meta...).
;;
;; If there's some more syntax you would like to see supported, submit
;; an issue at https://github.com/mgalgs/make-readme/issues

;;; Code:

(setq case-fold-search t)  ;; Ignore case in regexps.

(defun strip-comments (line)
  "Strip elisp comments from LINE."
  (replace-regexp-in-string "^;+ ?" "" line))

(defun trim-string (line)
  "Trim spaces from beginning and end of string LINE."
  (replace-regexp-in-string " +$" ""
                            (replace-regexp-in-string "^ +" "" line)))

(defun fix-symbol-references (line)
  "Fix refs like `this' so they don't turn adjacent text into code."
  (replace-regexp-in-string "`[^`\t ]+\\('\\)" "`" line nil nil 1))

(defun make-section (line level)
  "Makes a markdown section using the `#' syntax."
  (setq line (replace-regexp-in-string ":?[ \t]*$" "" line))
  (setq line (replace-regexp-in-string " --- " " – " line))
  (format "%s %s" (make-string level ?#) line))

(defun print-section (line level)
  "Prints a section made with `make-section'."
  (princ (make-section line level))
  (princ "\n"))

(defun slurp ()
  "Read all text from stdin as a list of lines."
  (let (line lines)
    (condition-case nil
        (while (setq line (read-from-minibuffer ""))
          (setq lines (cons line lines)))
      (error nil))
    (reverse lines)))

(defun print-formatted-line (line)
  "Prints a line formatted as markdown."
  (setq line (fix-symbol-references line))
  (let ((stripped-line (strip-comments line)))
    (cond

     ;; Header line (starts with ";;; ")
     ((string-match "^;;; " line)
      (print-section stripped-line 3))

     ;; list line (starts with " o ")
     ((string-match "^ *o " stripped-line)
      (let ((line (replace-regexp-in-string "^ *\o" "*" stripped-line)))
        (princ line)))

     ;; default (just print it)
     (t
      (princ stripped-line))))

  ;; and a newline
  (princ "\n"))
;; eo print-formatted-line

(defun document-a-function ()
  "Search for next defun/macro and print markdown documentation."
  (unless (search-forward-regexp
           "^(\\(defun\\|defmacro\\) \\([^ ]+\\) " nil t)
    (throw 'no-more-funcs nil))
  (let ((func (buffer-substring-no-properties
               (match-beginning 2)
               (match-end 2))))
    (when (not (string-match "--" func))
      (move-beginning-of-line 1)
      (let ((start (point)))
        (forward-sexp)
        (eval-region start (point)))
      (let ((text (describe-function
                   (eval (read (format "(function %s)" func))))))
        (if (and (not (string-match "Not documented\\." text))
                 (string-match "(" text))
            (with-temp-buffer
              (insert text)
              (goto-char (match-beginning 0))
              (forward-line)
              (let* ((title-txt (replace-regexp-in-string "\n"
                                                          ""
                                                          (buffer-substring (point)
                                                                            (progn (forward-sexp) (point)))))
                     (rest (buffer-substring (point)
                                             (point-max)))
                     (cleaned-rest (fix-symbol-references rest))
                     (printable (concat (make-section (format "`%s`" title-txt) 4)
                                        cleaned-rest
                                        "\n\n")))
                (princ printable))))))))



(defun get-meta (name)
  (save-excursion
    (goto-char 0)
    (re-search-forward (concat "^;; \\(" name ".*\\)") nil t)
    (match-string-no-properties 1)))

(defun println (&rest args)
  (princ (apply 'concat args))
  (princ "\n"))


; ----------------------------------------

(let* ((line nil)
       (title nil)
       (title-lines)
       (lines (slurp))
       (started-output nil)
       (code (concat "(progn\n" (mapconcat 'identity lines "\n") "\n)"))
       title-parts title-name title-description)

  ;; The first line should be like ";;; lol.el --- does stuff".
  ; (while (if (string-match "^;;;" (car lines))
  ;            (setq title-lines (cons (strip-comments (car lines)) title-lines)
  ;                  lines (cdr lines))))
  ; (setq title (mapconcat 'identity (reverse title-lines) " "))

  (if (string-match "^;;;" (car lines))
      (setq title (strip-comments (car lines))))

  (unless (string= title "")
    (setq title-parts (split-string title " --- ")
           title-name (car title-parts)
           title-description (cadr title-parts))
      (princ "\n")

      ; (princ "## ")
      ; (princ title-name)
      ; (princ "\n")
      ; (princ (concat "## " title-name " "))
      (princ title-name)
      (princ " ")
      (princ "[![Travis build status](https://secure.travis-ci.org/bburns/clipmon.png?branch=master)](http://travis-ci.org/bburns/clipmon)")
      (princ " ")
      (princ "[![melpa.org](http://melpa.org/packages/clipmon-badge.svg)](http://melpa.org/#/clipmon)")
      (princ " ")
      (princ "[![GPL-3.0](http://img.shields.io/:license-gpl-blue.svg)](http://opensource.org/licenses/GPL-3.0)")
      (princ "\n")
      (princ (make-string 76 ?-))

      (princ "\n")
      (princ "\n")
      ; (when (cdr title-parts)
        ; (princ (format "*%s*\n\n" (cadr title-parts))))
      ; (princ "---\n")
      )

  ;; Process everything else.
  (catch 'break
    (while (setq line (car lines))
      (cond

       ;; Wait until we reach the commentary section.
       ((string-match "^;;; Commentary:?$" line)
        (setq started-output t))

       ;; Once we hit code, attempt to document functions/macros.
       ((string-match "^;;; Code:?$" line)
        ; (print-section "Function Documentation" 3)
        ; (princ "\n\n")
        (with-temp-buffer
          (insert code)
          ; (goto-char 0)
          ; (lisp-mode)
          ; (catch 'no-more-funcs
            ; (while t
              ; (condition-case exc
                  ; (document-a-function)
                ; (error (princ (format "<!-- Error: %s -->\n\n" exc)))))))
          (println "----")
          (println)
          ; (println (get-meta "Author") "  ")
          (println "Author: Brian Burns  ") 
          (println (get-meta "URL") "  ")
          (println (get-meta "Version") "  ")
          (println)
          (println "This file was generated from commentary in " title-name " - do not edit!")
          (println)
          (println "----")
          (println)
          )
        (throw 'break nil))

       ;; Otherwise print out all the documentation.
       (started-output
        (print-formatted-line line)))

      (setq lines (cdr lines))))

  )


; (princ "-----

; <div style=\"padding-top:15px;color: #d0d0d0;\">
; Markdown README file generated by
; <a href=\"https://github.com/mgalgs/make-readme\">make-readme.el</a>
; </div>\n")

;;; make-readme.el ends here
