;;; muse-texinfo.el --- publish entries to Texinfo format or PDF

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
;; Muse Texinfo Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-latex)
(require 'texnfo-upd)

(defgroup muse-texinfo nil
  "Rules for marking up a Muse file as a Texinfo article."
  :group 'muse-publish)

(defcustom muse-texinfo-process-natively nil
  "If non-nil, use the Emacs `texinfmt' module to make Info files."
  :type 'boolean
  :require 'texinfmt
  :group 'muse-texinfo)

(defcustom muse-texinfo-extension ".texi"
  "Default file extension for publishing Texinfo files."
  :type 'string
  :group 'muse-texinfo)

(defcustom muse-texinfo-info-extension ".info"
  "Default file extension for publishing Info files."
  :type 'string
  :group 'muse-texinfo)

(defcustom muse-texinfo-pdf-extension ".pdf"
  "Default file extension for publishing PDF files."
  :type 'string
  :group 'muse-texinfo)

(defcustom muse-texinfo-header
  "\\input texinfo  @c -*-texinfo-*-

@setfilename <lisp>(concat (muse-page-name) \".info\")</lisp>
@settitle <lisp>(muse-publishing-directive \"title\")</lisp>

@documentencoding iso-8859-1

@iftex
@finalout
@end iftex

@titlepage
@title <lisp>(muse-publishing-directive \"title\")</lisp>
@author <lisp>(muse-publishing-directive \"author\")</lisp>
@end titlepage

<lisp>(and muse-publish-generate-contents \"@contents\")</lisp>

@node Top, Overview, , (dir)
@top Overview
@c Page published by Emacs Muse begins here\n\n"
  "Text to prepend to a Muse page being published as Texinfo.
This may be text or a filename.
It may contain <lisp> markup tags."
  :type 'string
  :group 'muse-texinfo)

(defcustom muse-texinfo-footer
  "\n@c Page published by Emacs Muse ends here
@bye\n"
  "Text to append to a Muse page being published as Texinfo.
This may be text or a filename.
It may contain <lisp> markup tags."
  :type 'string
  :group 'muse-texinfo)

(defcustom muse-texinfo-markup-regexps nil
  "List of markup rules for publishing a Muse page to Texinfo.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-texinfo)

(defcustom muse-texinfo-markup-functions
  '((table . muse-texinfo-markup-table)
    (heading . muse-texinfo-markup-heading))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-texinfo)

(defcustom muse-texinfo-markup-strings
  '((image-with-desc . "@center @image{%1%, , , %3%, %2%}@*\n@center %3%")
    (image           . "@noindent @image{%s, , , , %s}")
    (image-link      . "@uref{%s, %s.%s}")
    (anchor-ref      . "@ref{%s, %s}")
    (url             . "@uref{%s, %s}")
    (link            . "@ref{Top, %2%, , %1%, }")
    (link-and-anchor . "@ref{%3%, %2%, , %1%, %3%}")
    (email-addr      . "@email{%s}")
    (anchor          . "@anchor{%s} ")
    (emdash          . "---")
    (comment-begin   . "@ignore\n")
    (comment-end     . "\n@end ignore\n")
    (rule            . "@sp 1")
    (no-break-space  . "@w{ }")
    (line-break      . "@*")
    (enddots         . "@enddots{}")
    (dots            . "@dots{}")
    (section         . "@chapter ")
    (subsection      . "@section ")
    (subsubsection   . "@subsection ")
    (section-other   . "@subsubheading ")
    (footnote        . "@footnote{")
    (footnote-end    . "}")
    (begin-underline . "_")
    (end-underline   . "_")
    (begin-literal   . "@samp{")
    (end-literal     . "}")
    (begin-emph      . "@emph{")
    (end-emph        . "}")
    (begin-more-emph . "@strong{")
    (end-more-emph   . "}")
    (begin-most-emph . "@strong{@emph{")
    (end-most-emph   . "}}")
    (begin-verse     . "@display\n")
    (end-verse-line  . "")
    (verse-space     . "@ @ ")
    (end-verse       . "\n@end display")
    (begin-example   . "@example\n")
    (end-example     . "\n@end example")
    (begin-center    . "@quotation\n")
    (end-center      . "\n@end quotation")
    (begin-quote     . "@quotation\n")
    (end-quote       . "\n@end quotation")
    (begin-cite     . "")
    (begin-cite-author . "")
    (begin-cite-year . "")
    (end-cite        . "")
    (begin-uli       . "@itemize @bullet\n")
    (end-uli         . "\n@end itemize")
    (begin-uli-item  . "@item\n")
    (begin-oli       . "@enumerate\n")
    (end-oli         . "\n@end enumerate")
    (begin-oli-item  . "@item\n")
    (begin-dl        . "@table @strong\n")
    (end-dl          . "\n@end table")
    (begin-ddt       . "@item "))
  "Strings used for marking up text.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-texinfo)

(defcustom muse-texinfo-markup-specials
  '((?@ . "@@")
    (?{ . "@{")
    (?} . "@}"))
  "A table of characters which must be represented specially."
  :type '(alist :key-type character :value-type string)
  :group 'muse-texinfo)

(defcustom muse-texinfo-markup-specials-url
  '((?@ . "@@")
    (?{ . "@{")
    (?} . "@}")
    (?, . "@comma{}"))
  "A table of characters which must be represented specially.
These are applied to URLs."
  :type '(alist :key-type character :value-type string)
  :group 'muse-texinfo)

(defun muse-texinfo-decide-specials (context)
  "Determine the specials to escape, depending on CONTEXT."
  (cond ((memq context '(underline literal emphasis email url url-desc image
                                   footnote))
         muse-texinfo-markup-specials-url)
        (t muse-texinfo-markup-specials)))

(defun muse-texinfo-markup-table ()
  (let* ((table-info (muse-publish-table-fields (match-beginning 0)
                                                (match-end 0)))
         (row-len (car table-info))
         (field-list (cdr table-info)))
    (when table-info
      (muse-insert-markup "@multitable @columnfractions")
      (dotimes (field row-len)
        (muse-insert-markup " " (number-to-string (/ 1.0 row-len))))
      (dolist (fields field-list)
        (let ((type (car fields)))
          (unless (eq type 'hline)
            (setq fields (cdr fields))
            (if (= type 2)
                (muse-insert-markup "\n@headitem ")
              (muse-insert-markup "\n@item "))
            (insert (car fields))
            (setq fields (cdr fields))
            (dolist (field fields)
              (muse-insert-markup " @tab ")
              (insert field)))))
      (muse-insert-markup "\n@end multitable")
      (insert ?\n))))

(defun muse-texinfo-remove-links (string)
  "Remove explicit links from STRING, replacing them with the link
description.

If no description exists for the link, use the link itself."
  (let ((start nil))
    (while (setq start (string-match muse-explicit-link-regexp string
                                     start))
      (setq string
            (replace-match (or (match-string 2 string)
                               (match-string 1 string))
                           t t string)))
    string))

(defun muse-texinfo-protect-wikiwords (start end)
  "Protect all wikiwords from START to END from further processing."
  (and (boundp 'muse-wiki-wikiword-regexp)
       (featurep 'muse-wiki)
       (save-excursion
         (goto-char start)
         (while (re-search-forward muse-wiki-wikiword-regexp end t)
           (muse-publish-mark-read-only (match-beginning 0)
                                        (match-end 0))))))

(defun muse-texinfo-markup-heading ()
  (save-excursion
    (muse-publish-markup-heading))
  (let* ((eol (muse-line-end-position))
         (orig-heading (buffer-substring (point) eol))
         (beg (point)))
    (delete-region (point) eol)
    ;; don't allow links to be published in headings
    (insert (muse-texinfo-remove-links orig-heading))
    (muse-texinfo-protect-wikiwords beg (point))))

(defun muse-texinfo-munge-buffer ()
  (muse-latex-fixup-dquotes)
  (texinfo-insert-node-lines (point-min) (point-max) t)
  (texinfo-all-menus-update t))

(defun muse-texinfo-pdf-browse-file (file)
  (shell-command (concat "open " file)))

(defun muse-texinfo-info-generate (file output-path final-target)
  ;; The version of `texinfmt.el' that comes with Emacs 21 doesn't
  ;; support @documentencoding, so hack it in.
  (when (and (not (featurep 'xemacs))
             (eq emacs-major-version 21))
    (put 'documentencoding 'texinfo-format
         'texinfo-discard-line-with-args))
  ;; Most versions of `texinfmt.el' do not support @headitem, so hack
  ;; it in.
  (unless (get 'headitem 'texinfo-format)
    (put 'headitem 'texinfo-format 'texinfo-multitable-item))
  (muse-publish-transform-output
   file output-path final-target "Info"
   (function
    (lambda (file output-path)
      (if muse-texinfo-process-natively
          (save-window-excursion
            (save-excursion
              (find-file file)
              (let ((inhibit-read-only t))
                (texinfo-format-buffer))
              (save-buffer)
              (kill-buffer (current-buffer))
              (let ((buf (get-file-buffer file)))
                (with-current-buffer buf
                  (set-buffer-modified-p nil)
                  (kill-buffer (current-buffer))))
              t))
        (let ((result (shell-command
                       (concat "makeinfo --enable-encoding --output="
                               output-path " " file))))
          (if (or (not (numberp result))
                  (eq result 0))
              t
            nil)))))))

(defun muse-texinfo-pdf-generate (file output-path final-target)
  (let ((muse-latex-pdf-program "pdftex")
        (muse-latex-pdf-cruft '(".aux" ".cp" ".fn" ".ky" ".log" ".pg" ".toc"
                                ".tp" ".vr")))
    (muse-latex-pdf-generate file output-path final-target)))

;;; Register the Muse TEXINFO Publishers

(muse-define-style "texi"
                   :suffix    'muse-texinfo-extension
                   :regexps   'muse-texinfo-markup-regexps
                   :functions 'muse-texinfo-markup-functions
                   :strings   'muse-texinfo-markup-strings
                   :specials  'muse-texinfo-decide-specials
                   :after     'muse-texinfo-munge-buffer
                   :header    'muse-texinfo-header
                   :footer    'muse-texinfo-footer
                   :browser   'find-file)

(muse-derive-style "info" "texi"
                   :final   'muse-texinfo-info-generate
                   :link-suffix 'muse-texinfo-info-extension
                   :osuffix 'muse-texinfo-info-extension
                   :browser 'info)

(muse-derive-style "info-pdf" "texi"
                   :final   'muse-texinfo-pdf-generate
                   :link-suffix 'muse-texinfo-pdf-extension
                   :osuffix 'muse-texinfo-pdf-extension
                   :browser 'muse-texinfo-pdf-browse-file)

(provide 'muse-texinfo)

;;; muse-texinfo.el ends here
