;;; muse-book.el --- publish entries into a compilation

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

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Book Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-project)
(require 'muse-latex)
(require 'muse-regexps)

(defgroup muse-book nil
  "Module for publishing a series of Muse pages as a complete book.
Each page will become a separate chapter in the book, unless the
style keyword :nochapters is used, in which case they are all run
together as if one giant chapter."
  :group 'muse-publish)

(defcustom muse-book-before-publish-hook nil
  "A hook run in the book buffer before it is marked up."
  :type 'hook
  :group 'muse-book)

(defcustom muse-book-after-publish-hook nil
  "A hook run in the book buffer after it is marked up."
  :type 'hook
  :group 'muse-book)

(defcustom muse-book-latex-header
  "\\documentclass{book}

\\usepackage[english]{babel}
\\usepackage[latin1]{inputenc}
\\usepackage[T1]{fontenc}

\\begin{document}

\\title{<lisp>(muse-publishing-directive \"title\")</lisp>}
\\author{<lisp>(muse-publishing-directive \"author\")</lisp>}
\\date{<lisp>(muse-publishing-directive \"date\")</lisp>}

\\maketitle

\\tableofcontents\n"
  "Header used for publishing books to LaTeX.  This may be text or a filename."
  :type 'string
  :group 'muse-book)

(defcustom muse-book-latex-footer
  "<lisp>(muse-latex-bibliography)</lisp>
\\end{document}"
  "Footer used for publishing books to LaTeX.  This may be text or a filename."
  :type 'string
  :group 'muse-book)

(defun muse-book-publish-chapter (title entry style &optional nochapters)
  "Publish the chapter TITLE for the file ENTRY using STYLE.
TITLE is a string, ENTRY is a cons of the form (PAGE-NAME .
FILE), and STYLE is a Muse style list.

This routine does the same basic work as `muse-publish-markup-buffer',
but treating the page as if it were a single chapter within a book."
  (let ((muse-publishing-directives (list (cons "title" title)))
        (muse-publishing-current-file (cdr entry))
        (beg (point)) end)
    (muse-insert-file-contents (cdr entry))
    (setq end (copy-marker (point-max) t))
    (muse-publish-markup-region beg end (car entry) style)
    (goto-char beg)
    (unless (or nochapters
                (muse-style-element :nochapters style))
      (insert "\n")
      (muse-insert-markup (muse-markup-text 'chapter))
      (insert (let ((chap (muse-publishing-directive "title")))
                (if (string= chap title)
                    (car entry)
                  chap)))
      (muse-insert-markup (muse-markup-text 'chapter-end))
      (insert "\n\n"))
    (save-restriction
      (narrow-to-region beg end)
      (muse-publish-markup (or title "")
                           '((100 "<\\(lisp\\)>" 0
                              muse-publish-markup-tag)))
      (muse-style-run-hooks :after style))
    (goto-char end)))

(defun muse-book-publish-p (project target)
  "Determine whether the book in PROJECT is out-of-date."
  (let ((pats (cadr project)))
    (catch 'publish
      (while pats
        (if (symbolp (car pats))
            (if (eq :book-end (car pats))
                (throw 'publish nil)
              ;; skip past symbol-value pair
              (setq pats (cddr pats)))
          (dolist (entry (muse-project-file-entries (car pats)))
            (when (and (not (muse-project-private-p (cdr entry)))
                       (file-newer-than-file-p (cdr entry) target))
              (throw 'publish t)))
          (setq pats (cdr pats)))))))

(defun muse-book-get-directives (file)
  "Interpret any publishing directives contained in FILE.
This is meant to be called in a temp buffer that will later be
used for publishing."
  (save-restriction
    (narrow-to-region (point) (point))
    (unwind-protect
        (progn
          (muse-insert-file-contents file)
          (muse-publish-markup
           "attributes"
           `(;; Remove leading and trailing whitespace from the file
             (100 "\\(\\`\n+\\|\n+\\'\\)" 0 "")
             ;; Remove trailing whitespace from all lines
             (200 ,(concat "[" muse-regexp-blank "]+$") 0 "")
             ;; Handle any leading #directives
             (300 "\\`#\\([a-zA-Z-]+\\)\\s-+\\(.+\\)\n+"
                  0 muse-publish-markup-directive))))
      (delete-region (point-min) (point-max)))))

(defun muse-book-publish-project
  (project book title style &optional output-dir force)
  "Publish PROJECT under the name BOOK with the given TITLE and STYLE.
BOOK should be a page name, i.e., letting the style determine the
prefix and/or suffix.  The book is published to OUTPUT-DIR.  If FORCE
is nil, the book is only published if at least one of its component
pages has changed since it was last published."
  (interactive
   (let ((project (muse-read-project "Publish project as book: " nil t)))
     (append (list project
                   (read-string "Basename of book (without extension): ")
                   (read-string "Title of book: "))
             (muse-publish-get-info))))
  (setq project (muse-project project))
  (let ((muse-current-project project))
    ;; See if any of the project's files need saving first
    (muse-project-save-buffers project)
    ;; Publish the book
    (muse-book-publish book style output-dir force title)))

(defun muse-book-publish (file style &optional output-dir force title)
  "Publish FILE as a book with the given TITLE and STYLE.
The book is published to OUTPUT-DIR.  If FORCE is nil, the book
is only published if at least one of its component pages has
changed since it was last published."
  ;; Cleanup some of the arguments
  (let ((style-name style))
    (setq style (muse-style style))
    (unless style
      (error "There is no style '%s' defined" style-name)))
  ;; Publish each page in the project as a chapter in one large book
  (let* ((output-path (muse-publish-output-file file output-dir style))
         (output-suffix (muse-style-element :osuffix style))
         (target output-path)
         (project muse-current-project)
         (published nil))
    (when output-suffix
      (setq target (concat (muse-path-sans-extension target)
                           output-suffix)))
    ;; Unless force is non-nil, determine if the book needs publishing
    (if (and (not force)
             (not (muse-book-publish-p project target)))
        (message "The book \"%s\" is up-to-date." file)
      ;; Create the book from all its component parts
      (muse-with-temp-buffer
        (let ((style-final  (muse-style-element :final  style t))
              (style-header (muse-style-element :header style))
              (style-footer (muse-style-element :footer style))
              (muse-publishing-current-style style)
              (muse-publishing-directives
               (list (cons "title" (or title (muse-page-name file)))
                     (cons "date" (format-time-string "%B %e, %Y"))))
              (muse-publishing-p t)
              (muse-current-project project)
              (pats (cadr project))
              (nochapters nil))
          (run-hooks 'muse-before-book-publish-hook)
          (let ((style-final style-final)
                (style-header style-header)
                (style-footer style-footer))
            (unless title
              (muse-book-get-directives file)
              (setq title (muse-publishing-directive "title")))
            (while pats
              (if (symbolp (car pats))
                  (cond
                   ((eq :book-part (car pats))
                    (insert "\n")
                    (muse-insert-markup (muse-markup-text 'part))
                    (insert (cadr pats))
                    (muse-insert-markup (muse-markup-text 'part-end))
                    (insert "\n")
                    (setq pats (cddr pats)))
                   ((eq :book-chapter (car pats))
                    (insert "\n")
                    (muse-insert-markup (muse-markup-text 'chapter))
                    (insert (cadr pats))
                    (muse-insert-markup (muse-markup-text 'chapter-end))
                    (insert "\n")
                    (setq pats (cddr pats)))
                   ((eq :nochapters (car pats))
                    (setq nochapters t
                          pats (cddr pats)))
                   ((eq :book-style (car pats))
                    (setq style (muse-style (cadr pats)))
                    (setq style-final  (muse-style-element :final  style t)
                          style-header (muse-style-element :header style)
                          style-footer (muse-style-element :footer style)
                          muse-publishing-current-style style)
                    (setq pats (cddr pats)))
                   ((eq :book-funcall (car pats))
                    (funcall (cadr pats))
                    (setq pats (cddr pats)))
                   ((eq :book-end (car pats))
                    (setq pats nil))
                   (t
                    (setq pats (cddr pats))))
                (let ((entries (muse-project-file-entries (car pats))))
                  (while (and entries (car entries) (caar entries))
                    (unless (muse-project-private-p (cdar entries))
                      (muse-book-publish-chapter title (car entries)
                                                 style nochapters)
                      (setq published t))
                    (setq entries (cdr entries))))
                (setq pats (cdr pats)))))
          (goto-char (point-min))
          (if style-header (muse-insert-file-or-string style-header file))
          (goto-char (point-max))
          (if style-footer (muse-insert-file-or-string style-footer file))
          (run-hooks 'muse-after-book-publish-hook)
          (if (muse-write-file output-path)
              (if style-final
                  (funcall style-final file output-path target))
            (setq published nil)))))
    (if published
        (message "The book \"%s\" has been published." file))
    published))

;;; Register the Muse BOOK Publishers

(muse-derive-style "book-latex" "latex"
                   :header 'muse-book-latex-header
                   :footer 'muse-book-latex-footer
                   :publish 'muse-book-publish)

(muse-derive-style "book-pdf" "pdf"
                   :header 'muse-book-latex-header
                   :footer 'muse-book-latex-footer
                   :publish 'muse-book-publish)

(provide 'muse-book)

;;; muse-book.el ends here
