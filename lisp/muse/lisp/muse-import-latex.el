;;; muse-import-latex.el --- convert a LaTex file into a Muse file

;; Copyright (C) 2004, 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Helper commands for converting a LaTeX file into a Muse file.

;;; Contributors:

;;; Code:

(require 'muse)
(require 'muse-regexps)

(defun muse-i-l-write-citation (note author citation pages)
  (save-excursion
    (goto-char (point-max))
    (if (= note 1)
        (insert "\nFootnotes:\n\n"))
    (let ((beg (point)))
      (insert "\n[" (number-to-string note) "]  " author)
      (if (and citation pages)
          (insert ", " citation ", " pages))
      (insert "\n")
      (goto-char beg)
      (while (re-search-forward (concat "p.\\\\[" muse-regexp-blank "\n]+")
                                nil t)
        (replace-match "p."))
      (goto-char beg)
      (while (re-search-forward "--" nil t)
        (replace-match "-")))))

(defun muse-i-l-write-footnote (note text)
  (save-excursion
    (goto-char (point-max))
    (if (= note 1)
        (insert "\nFootnotes:\n\n"))
    (insert "\n[" (number-to-string note) "]  " text ?\n)))

;;;###autoload
(defun muse-import-latex ()
  (interactive)
  (goto-char (point-min))
  (while (not (eobp))
    (cond
     ((or (looking-at "^\\\\documentclass")
          (looking-at "^\\\\input")
          (looking-at "^\\\\begin{document}")
          (looking-at "^\\\\end{document}")
          (looking-at "^\\\\author")
          (looking-at "^\\\\\\(med\\|big\\|small\\)skip")
          (looking-at "^\\\\maketitle"))
      (delete-region (point) (muse-line-end-position)))
     ((looking-at "^\\\\title{\\(.+\\)}")
      (delete-region (match-end 1) (muse-line-end-position))
      (delete-region (point) (match-beginning 1))
      (insert "#title ")))
    (forward-line))
  (goto-char (point-min))
  (while (re-search-forward "\\\\\\(l\\)?dots{}" nil t)
    (replace-match (concat (and (string= (match-string 1) "l") ".")
                           "...")))
  (goto-char (point-min))
  (while (re-search-forward "\\(``\\|''\\)" nil t)
    (replace-match "\""))
  (goto-char (point-min))
  (while (re-search-forward "---" nil t)
    (replace-match " -- "))
  (goto-char (point-min))
  (while (re-search-forward "\\\\tableofcontents" nil t)
    (replace-match "<contents>"))
  (goto-char (point-min))
  (while (re-search-forward "\\\\\\\\" nil t)
    (replace-match ""))
  (goto-char (point-min))
  (while (re-search-forward "\\\\\\(sub\\)?section{\\([^}]+\\)}" nil t)
    (replace-match (concat (if (string= (match-string 1) "sub")
                               "**" "*")
                           " " (match-string 2))))
  (goto-char (point-min))
  (while (re-search-forward "\\\\\\(begin\\|end\\){verse}" nil t)
    (replace-match (concat "<" (if (string= (match-string 1) "end") "/")
                           "verse>")))
  (goto-char (point-min))
  (while (re-search-forward "\\\\\\(begin\\|end\\){quote}\n" nil t)
    (replace-match ""))
  (goto-char (point-min))
  (while (re-search-forward
          "\\\\\\(emph\\|textbf\\){\\([^}]+?\\)\\(\\\\/\\)?}" nil t)
    (replace-match
     (if (string= (match-string 1) "emph") "*\\2*" "**\\2**")))
  (let ((footnote-index 1))
    (goto-char (point-min))
    (while (re-search-forward
            (concat "\\\\\\(q\\)?\\(footnote\\|excerpt\\)\\(np\\)?"
                    "\\({\\([^}]+\\)}\\)?"
                    "\\({\\([^}]+\\)}{\\([^}]+\\)}\\)?{\\([^}]+\\)}") nil t)
      (let ((beg (match-beginning 0))
            (end (match-end 0)))
        (unless (string= (match-string 2) "footnote")
          (if (null (match-string 1))
              (insert "  " (match-string 9))
            (let ((b (point)) e)
              (insert "\"" (match-string 9) "\"")
              (setq e (point-marker))
              (save-match-data
                (save-excursion
                  (goto-char b)
                  (while (< (point) e)
                    (if (looking-at "\\s-+")
                        (delete-region (match-beginning 0)
                                       (match-end 0)))
                    (forward-line))))
              (set-marker e nil))))
        (insert "[" (number-to-string footnote-index) "]")
        (if (string= (match-string 2) "footnote")
            (muse-i-l-write-footnote footnote-index (match-string 9))
          (muse-i-l-write-citation footnote-index (match-string 5)
                                   (match-string 7) (match-string 8)))
        (setq footnote-index (1+ footnote-index))
        (delete-region beg end))))
  (goto-char (point-min))
  (while (looking-at "\n") (delete-char 1))
  (goto-char (point-min))
  (while (re-search-forward "\n\n+" nil t)
    (replace-match "\n\n")))

(provide 'muse-import-latex)

;;; muse-import-latex.el ends here
