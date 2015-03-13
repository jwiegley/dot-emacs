;;; muse-xml.el --- publish XML files

;; Copyright (C) 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: Michael Olson <mwolson@gnu.org>
;; Date: Sat 23-Jul-2005

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

;; James Clarke's nxml-mode can be used for editing and validating
;; Muse-generated XML files.  If you are in nxml-mode use the command
;; C-c C-s C-f to point to the schema in `contrib/muse.rnc', which
;; comes with Muse.  Say yes if you are asked if you want to copy the
;; file to your location.  C-c C-s C-a can then be used to reload the
;; schema if you make changes to the file.

;;; Contributors:

;; Peter K. Lee (saint AT corenova DOT com) made the initial
;; implementation of planner-publish.el, which was heavily borrowed
;; from.

;; Brad Collins (brad AT chenla DOT org) provided a Compact RelaxNG
;; schema.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse XML Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-regexps)
(require 'muse-xml-common)

(defgroup muse-xml nil
  "Options controlling the behavior of Muse XML publishing.
See `muse-xml' for more information."
  :group 'muse-publish)

(defcustom muse-xml-extension ".xml"
  "Default file extension for publishing XML files."
  :type 'string
  :group 'muse-xml)

(defcustom muse-xml-header
  "<?xml version=\"1.0\" encoding=\"<lisp>
  (muse-xml-encoding)</lisp>\"?>
<MUSE>
  <pageinfo>
    <title><lisp>(muse-publishing-directive \"title\")</lisp></title>
    <author><lisp>(muse-publishing-directive \"author\")</lisp></author>
    <maintainer><lisp>(muse-style-element :maintainer)</lisp></maintainer>
    <pubdate><lisp>(muse-publishing-directive \"date\")</lisp></pubdate>
  </pageinfo>
  <!-- Page published by Emacs Muse begins here -->\n"
  "Header used for publishing XML files.
This may be text or a filename."
  :type 'string
  :group 'muse-xml)

(defcustom muse-xml-footer "
  <!-- Page published by Emacs Muse ends here -->
</MUSE>\n"
  "Footer used for publishing XML files.
This may be text or a filename."
  :type 'string
  :group 'muse-xml)

(defcustom muse-xml-markup-regexps
  `(;; Beginning of doc, end of doc, or plain paragraph separator
    (10000 ,(concat "\\(\\(\n\\(?:[" muse-regexp-blank "]*\n\\)*"
                    "\\([" muse-regexp-blank "]*\n\\)\\)"
                    "\\|\\`\\s-*\\|\\s-*\\'\\)")
           ;; this is somewhat repetitive because we only require the
           ;; line just before the paragraph beginning to be not
           ;; read-only
           3 muse-xml-markup-paragraph))
  "List of markup rules for publishing a Muse page to XML.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-xml)

(defcustom muse-xml-markup-functions
  '((anchor . muse-xml-markup-anchor)
    (table . muse-xml-markup-table))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-xml)

(defcustom muse-xml-markup-strings
  '((image-with-desc . "<image href=\"%s.%s\">%s</image>")
    (image           . "<image href=\"%s.%s\"></image>")
    (image-link      . "<link type=\"image\" href=\"%s\">%s.%s</link>")
    (anchor-ref      . "<link type=\"url\" href=\"#%s\">%s</link>")
    (url             . "<link type=\"url\" href=\"%s\">%s</link>")
    (link            . "<link type=\"url\" href=\"%s\">%s</link>")
    (link-and-anchor . "<link type=\"url\" href=\"%s#%s\">%s</link>")
    (email-addr      . "<link type=\"email\" href=\"%s\">%s</link>")
    (anchor          . "<anchor id=\"%s\" />\n")
    (emdash          . "%s--%s")
    (comment-begin   . "<!-- ")
    (comment-end     . " -->")
    (rule            . "<hr />")
    (fn-sep          . "<hr />\n")
    (no-break-space  . "&nbsp;")
    (line-break      . "<br>")
    (enddots         . "....")
    (dots            . "...")
    (section         . "<section level=\"1\"><title>")
    (section-end     . "</title>")
    (subsection      . "<section level=\"2\"><title>")
    (subsection-end  . "</title>")
    (subsubsection   . "<section level=\"3\"><title>")
    (subsubsection-end . "</title>")
    (section-other   . "<section level=\"%s\"><title>")
    (section-other-end . "</title>")
    (section-close   . "</section>")
    (footnote        . "<footnote>")
    (footnote-end    . "</footnote>")
    (begin-underline . "<format type=\"underline\">")
    (end-underline   . "</format>")
    (begin-literal   . "<code>")
    (end-literal     . "</code>")
    (begin-emph      . "<format type=\"emphasis\" level=\"1\">")
    (end-emph        . "</format>")
    (begin-more-emph . "<format type=\"emphasis\" level=\"2\">")
    (end-more-emph   . "</format>")
    (begin-most-emph . "<format type=\"emphasis\" level=\"3\">")
    (end-most-emph   . "</format>")
    (begin-verse     . "<verse>\n")
    (begin-verse-line . "<line>")
    (end-verse-line  . "</line>")
    (empty-verse-line . "<line />")
    (begin-last-stanza-line . "<line>")
    (end-last-stanza-line . "</line>")
    (end-verse       . "</verse>")
    (begin-example   . "<example>")
    (end-example     . "</example>")
    (begin-center    . "<p><format type=\"center\">\n")
    (end-center      . "\n</format></p>")
    (begin-quote     . "<blockquote>\n")
    (end-quote       . "\n</blockquote>")
    (begin-cite      . "<cite>")
    (begin-cite-author . "<cite type=\"author\">")
    (begin-cite-year . "<cite type=\"year\">")
    (end-cite        . "</cite>")
    (begin-quote-item . "<p>")
    (end-quote-item  . "</p>")
    (begin-uli       . "<list type=\"unordered\">\n")
    (end-uli         . "\n</list>")
    (begin-uli-item  . "<item>")
    (end-uli-item    . "</item>")
    (begin-oli       . "<list type=\"ordered\">\n")
    (end-oli         . "\n</list>")
    (begin-oli-item  . "<item>")
    (end-oli-item    . "</item>")
    (begin-dl        . "<list type=\"definition\">\n")
    (end-dl          . "\n</list>")
    (begin-dl-item   . "<item>\n")
    (end-dl-item     . "\n</item>")
    (begin-ddt       . "<term>")
    (end-ddt         . "</term>")
    (begin-dde       . "<definition>")
    (end-dde         . "</definition>")
    (begin-table     . "<table%s>\n")
    (end-table       . "</table>")
    (begin-table-row . "    <tr>\n")
    (end-table-row   . "    </tr>\n")
    (begin-table-entry . "      <%s>")
    (end-table-entry . "</%s>\n"))
  "Strings used for marking up text.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-xml)

(defcustom muse-xml-encoding-default 'utf-8
  "The default Emacs buffer encoding to use in published files.
This will be used if no special characters are found."
  :type 'symbol
  :group 'muse-xml)

(defcustom muse-xml-charset-default "utf-8"
  "The default XML charset to use if no translation is
found in `muse-xml-encoding-map'."
  :type 'string
  :group 'muse-xml)

(defun muse-xml-encoding ()
  (muse-xml-transform-content-type
   (or (and (boundp 'buffer-file-coding-system)
            buffer-file-coding-system)
       muse-xml-encoding-default)
   muse-xml-charset-default))

(defun muse-xml-markup-paragraph ()
  (let ((end (copy-marker (match-end 0) t)))
    (goto-char (match-beginning 0))
    (when (save-excursion
            (save-match-data
              (and (not (get-text-property (max (point-min) (1- (point)))
                                           'muse-no-paragraph))
                   (re-search-backward "<\\(/?\\)p[ >]" nil t)
                   (not (string-equal (match-string 1) "/")))))
      (when (get-text-property (1- (point)) 'muse-end-list)
        (goto-char (previous-single-property-change (1- (point))
                                                    'muse-end-list)))
      (muse-insert-markup "</p>"))
    (goto-char end))
  (cond
   ((eobp)
    (unless (bolp)
      (insert "\n")))
   ((get-text-property (point) 'muse-no-paragraph)
    (forward-char 1)
    nil)
   ((eq (char-after) ?\<)
    (when (looking-at (concat "<\\(format\\|code\\|link\\|image"
                              "\\|anchor\\|footnote\\)[ >]"))
      (muse-insert-markup "<p>")))
   (t
    (muse-insert-markup "<p>"))))

(defun muse-xml-finalize-buffer ()
  (when (boundp 'buffer-file-coding-system)
    (when (memq buffer-file-coding-system '(no-conversion undecided-unix))
      ;; make it agree with the default charset
      (setq buffer-file-coding-system muse-xml-encoding-default))))

;;; Register the Muse XML Publisher

(muse-define-style "xml"
                   :suffix     'muse-xml-extension
                   :regexps    'muse-xml-markup-regexps
                   :functions  'muse-xml-markup-functions
                   :strings    'muse-xml-markup-strings
                   :specials   'muse-xml-decide-specials
                   :after      'muse-xml-finalize-buffer
                   :header     'muse-xml-header
                   :footer     'muse-xml-footer
                   :browser    'find-file)

(provide 'muse-xml)

;;; muse-xml.el ends here
