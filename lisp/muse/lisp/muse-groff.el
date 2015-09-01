;;; muse-groff.el --- publish groff -mom -mwww files

;; Copyright (C) 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: Andrew J. Korty (ajk AT iu DOT edu)
;; Date: Tue 5-Jul-2005

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
;; Muse Publishing Using groff -mom -mwww
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)

(defgroup muse-groff nil
  "Rules for marking up a Muse file with groff -mom -mwww macros."
  :group 'muse-publish)

(defcustom muse-groff-extension ".groff"
  "Default file extension for publishing groff -mom -mwww files."
  :type 'string
  :group 'muse-groff)

(defcustom muse-groff-pdf-extension ".pdf"
  "Default file extension for publishing groff -mom -mwww files to PDF."
  :type 'string
  :group 'muse-groff)

(defcustom muse-groff-header
  ".TITLE \"<lisp>(muse-publishing-directive \"title\")</lisp>\"
.SUBTITLE \"<lisp>(muse-publishing-directive \"date\")</lisp>\"
.AUTHOR \"<lisp>(muse-publishing-directive \"author\")</lisp>\"
.PRINTSTYLE TYPESET
.de list
.    LIST \\$1
.    SHIFT_LIST \\$2
..
.PARA_INDENT 0
.START
<lisp>(and muse-publish-generate-contents \".TOC\n\")</lisp>\n"
  "Header used for publishing groff -mom -mwww files."
  :type '(choice string file)
  :group 'muse-groff)

(defcustom muse-groff-footer " "
  "Footer used for publishing groff -mom -mwww files."
  :type '(choice string file)
  :group 'muse-groff)

(defcustom muse-groff-markup-regexps
  `((10400 ,(concat "\\(\n</\\(blockquote\\|center\\)>\\)?\n"
                    "\\(["
                    muse-regexp-blank
                    "]*\n\\)+\\(<\\(blockquote\\|center\\)>\n\\)?")
           0 muse-groff-markup-paragraph))
"List of markup regexps for identifying regions in a Muse page.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-groff)

(defcustom muse-groff-markup-functions
  '((table . muse-groff-markup-table))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-groff)

(defcustom muse-groff-markup-tags
  '()
  "A list of tag specifications, for specially marking up GROFF."
  :type '(repeat (list (string :tag "Markup tag")
                       (boolean :tag "Expect closing tag" :value t)
                       (boolean :tag "Parse attributes" :value nil)
                       (boolean :tag "Nestable" :value nil)
                       function))
  :group 'muse-groff)

(defcustom muse-groff-markup-strings
  `((image-with-desc . "\n.MPIMG -R %s.%s\n")
    (image           . "\n.MPIMG -R %s.%s\n")
    (image-link      . "\n.\\\" %s\n.MPIMG -R %s.%s")
    (url             . "\n.URL %s %s\n\\z")
    (link            . "\n.URL %s %s\n\\z")
    (email-addr      . "\f[C]%s\f[]")
    (emdash          . "\\(em")
    (rule            . "\n.RULE\n")
    (no-break-space  . "\\h")
    (line-break      . "\\p")
    (enddots         . "....")
    (dots            . "...")
;;     (part            . "\\part{")
;;     (part-end        . "}")
;;     (chapter         . "\\chapter{")
;;     (chapter-end     . "}")
    (section         . ".HEAD \"")
    (section-end     . "\"")
    (subsection      . ".SUBHEAD \"")
    (subsection-end  . "\"")
    (subsubsection   . ".PARAHEAD \"")
    (subsubsection-end . "\"")
;;     (footnote        . "\\c\n.FOOTNOTE\n")
;;     (footnote-end    . "\n.FOOTNOTE OFF\n")
;;     (footnotemark    . "\\footnotemark[%d]")
;;     (footnotetext    . "\\footnotetext[%d]{")
;;     (footnotetext-end . "}")
    (begin-underline . "\n.UNDERSCORE \"")
    (end-underline   . "\"\n")
    (begin-literal   . "\\fC")
    (end-literal     . "\\fP")
    (begin-emph      . "\\fI")
    (end-emph        . "\\fP")
    (begin-more-emph . "\\fB")
    (end-more-emph   . "\\fP")
    (begin-most-emph . "\\f(BI")
    (end-most-emph   . "\\fP")
    (begin-verse     . ".QUOTE")
    (end-verse       . ".QUOTE OFF")
    (begin-center    . "\n.CENTER\n")
    (end-center      . "\n.QUAD L\n")
    (begin-example   . ,(concat
                         ".QUOTE_FONT CR\n.QUOTE_INDENT 1\n"".QUOTE_SIZE -2\n"
                         ".UNDERLINE_QUOTES OFF\n.QUOTE"))
    (end-example     . ".QUOTE OFF")
    (begin-quote     . ".BLOCKQUOTE")
    (end-quote       . ".BLOCKQUOTE OFF")
    (begin-cite     . "")
    (begin-cite-author . "")
    (begin-cite-year . "")
    (end-cite        . "")
    (begin-uli       . ".list BULLET\n.SHIFT_LIST 2m\n.ITEM\n")
    (end-uli         . "\n.LIST OFF")
    (begin-oli       . ".list DIGIT\n.SHIFT_LIST 2m\n.ITEM\n")
    (end-oli         . "\n.LIST OFF")
    (begin-ddt       . "\\fB")
    (begin-dde       . "\\fP\n.IR 4P\n")
    (end-ddt         . ".IRX CLEAR"))
  "Strings used for marking up text.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-groff)

(defcustom muse-groff-markup-specials
  '((?\\ . "\\e"))
  "A table of characters which must be represented specially."
  :type '(alist :key-type character :value-type string)
  :group 'muse-groff)

(defun muse-groff-markup-paragraph ()
  (let ((end (copy-marker (match-end 0) t)))
    (goto-char (1+ (match-beginning 0)))
    (delete-region (point) end)
    (unless (looking-at "\.\\(\\(\\(SUB\\|PARA\\)?HEAD \\)\\|RULE$\\)")
      (muse-insert-markup ".ALD .5v\n.PP\n.ne 2\n"))))

(defun muse-groff-protect-leading-chars ()
  "Protect leading periods and apostrophes from being interpreted as
command characters."
  (while (re-search-forward "^[.']" nil t)
    (replace-match "\\\\&\\&" t)))

(defun muse-groff-concat-lists ()
  "Join like lists."
  (let ((type "")
        arg begin)
    (while (re-search-forward "^\.LIST[ \t]+\\(.*\\)\n" nil t)
      (setq arg (match-string 1))
      (if (string= arg "OFF")
          (setq begin (match-beginning 0))
        (if (and begin (string= type arg))
            (delete-region begin (match-end 0))
          (setq type arg
                begin 0))))))

(defun muse-groff-fixup-dquotes ()
  "Fixup double quotes."
  (let ((open t))
    (while (search-forward "\"" nil t)
      (unless (get-text-property (match-beginning 0) 'read-only)
        (if (and (bolp) (eq (char-before) ?\n))
            (setq open t))
        (if open
            (progn
              (replace-match "``")
              (setq open nil))
          (replace-match "''")
          (setq open t))))))

(defun muse-groff-prepare-buffer ()
  (goto-char (point-min))
  (muse-groff-protect-leading-chars))

(defun muse-groff-munge-buffer ()
  (goto-char (point-min))
  (muse-groff-concat-lists))

(defun muse-groff-pdf-browse-file (file)
  (shell-command (concat "open " file)))

(defun muse-groff-pdf-generate (file output-path final-target)
  (muse-publish-transform-output
   file output-path final-target "PDF"
   (function
    (lambda (file output-path)
      (let ((command
             (format
              (concat "file=%s; ext=%s; cd %s && cp $file$ext $file.ref && "
                      "groff -mom -mwww -t $file$ext > $file.ps && "
                      "pstopdf $file.ps")
              (file-name-sans-extension file)
              muse-groff-extension
              (file-name-directory output-path))))
        (shell-command command))))
   ".ps"))

;;; Register the Muse GROFF Publisher

(muse-define-style "groff"
                   :suffix    'muse-groff-extension
                   :regexps   'muse-groff-markup-regexps
;;;		   :functions 'muse-groff-markup-functions
                   :strings   'muse-groff-markup-strings
                   :tags      'muse-groff-markup-tags
                   :specials  'muse-groff-markup-specials
                   :before    'muse-groff-prepare-buffer
                   :before-end 'muse-groff-munge-buffer
                   :header    'muse-groff-header
                   :footer    'muse-groff-footer
                   :browser   'find-file)

(muse-derive-style "groff-pdf" "groff"
                   :final   'muse-groff-pdf-generate
                   :browser 'muse-groff-pdf-browse-file
                   :osuffix 'muse-groff-pdf-extension)

(provide 'muse-groff)

;;; muse-groff.el ends here
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; End:
