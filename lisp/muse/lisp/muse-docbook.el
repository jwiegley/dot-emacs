;;; muse-docbook.el --- publish DocBook files

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

;; Dale P. Smith (dpsm AT en DOT com) improved the markup
;; significantly and made many valuable suggestions.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse DocBook XML Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-regexps)
(require 'muse-xml-common)

(defgroup muse-docbook nil
  "Options controlling the behavior of Muse DocBook XML publishing.
See `muse-docbook' for more information."
  :group 'muse-publish)

(defcustom muse-docbook-extension ".xml"
  "Default file extension for publishing DocBook XML files."
  :type 'string
  :group 'muse-docbook)

(defcustom muse-docbook-header
  "<?xml version=\"1.0\" encoding=\"<lisp>
  (muse-docbook-encoding)</lisp>\"?>
<!DOCTYPE article PUBLIC \"-//OASIS//DTD DocBook V4.2//EN\"
                  \"http://www.oasis-open.org/docbook/xml/4.2/docbookx.dtd\"<lisp>(muse-docbook-entities)</lisp>>
<article>
  <articleinfo>
    <title><lisp>(muse-publishing-directive \"title\")</lisp></title>
    <author><lisp>(muse-docbook-get-author
                    (muse-publishing-directive \"author\"))</lisp></author>
    <pubdate><lisp>(muse-publishing-directive \"date\")</lisp></pubdate>
  </articleinfo>
  <!-- Page published by Emacs Muse begins here -->\n"
  "Header used for publishing DocBook XML files.
This may be text or a filename."
  :type 'string
  :group 'muse-docbook)

(defcustom muse-docbook-footer "
  <!-- Page published by Emacs Muse ends here -->
<lisp>(muse-docbook-bibliography)</lisp></article>\n"
  "Footer used for publishing DocBook XML files.
This may be text or a filename."
  :type 'string
  :group 'muse-docbook)

(defcustom muse-docbook-markup-regexps
  `(;; Beginning of doc, end of doc, or plain paragraph separator
    (10000 ,(concat "\\(\\(\n\\(?:[" muse-regexp-blank "]*\n\\)*"
                    "\\([" muse-regexp-blank "]*\n\\)\\)"
                    "\\|\\`\\s-*\\|\\s-*\\'\\)")
           3 muse-docbook-markup-paragraph))
  "List of markup rules for publishing a Muse page to DocBook XML.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-docbook)

(defcustom muse-docbook-markup-functions
  '((anchor . muse-xml-markup-anchor)
    (table . muse-xml-markup-table))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-docbook)

(defcustom muse-docbook-markup-strings
  '((image-with-desc . "<mediaobject>
<imageobject>
<imagedata fileref=\"%1%.%2%\" format=\"%2%\" />
</imageobject>
<caption><para>%3%</para></caption>
</mediaobject>")
    (image           . "<inlinemediaobject><imageobject>
<imagedata fileref=\"%1%.%2%\" format=\"%2%\" />
</imageobject></inlinemediaobject>")
    (image-link      . "<ulink url=\"%1%\"><inlinemediaobject><imageobject>
<imagedata fileref=\"%2%.%3%\" format=\"%3%\" />
</imageobject></inlinemediaobject></ulink>")
    (anchor-ref      . "<link linkend=\"%s\">%s</link>")
    (url             . "<ulink url=\"%s\">%s</ulink>")
    (link            . "<ulink url=\"%s\">%s</ulink>")
    (link-and-anchor . "<ulink url=\"%s#%s\">%s</ulink>")
    (email-addr      . "<email>%s</email>")
    (anchor          . "<anchor id=\"%s\" />\n")
    (emdash          . "%s&mdash;%s")
    (comment-begin   . "<!-- ")
    (comment-end     . " -->")
    (rule            . "")
    (no-break-space  . "&nbsp;")
    (enddots         . "....")
    (dots            . "...")
    (section         . "<section><title>")
    (section-end     . "</title>")
    (subsection      . "<section><title>")
    (subsection-end  . "</title>")
    (subsubsection   . "<section><title>")
    (subsubsection-end . "</title>")
    (section-other   . "<section><title>")
    (section-other-end . "</title>")
    (section-close   . "</section>")
    (footnote        . "<footnote><para>")
    (footnote-end    . "</para></footnote>")
    (begin-underline . "")
    (end-underline   . "")
    (begin-literal   . "<systemitem>")
    (end-literal     . "</systemitem>")
    (begin-emph      . "<emphasis>")
    (end-emph        . "</emphasis>")
    (begin-more-emph . "<emphasis role=\"strong\">")
    (end-more-emph   . "</emphasis>")
    (begin-most-emph . "<emphasis role=\"strong\"><emphasis>")
    (end-most-emph   . "</emphasis></emphasis>")
    (begin-verse     . "<literallayout>\n")
    (verse-space     . "  ")
    (end-verse       . "</literallayout>")
    (begin-example   . "<programlisting>")
    (end-example     . "</programlisting>")
    (begin-center    . "<para role=\"centered\">\n")
    (end-center      . "\n</para>")
    (begin-quote     . "<blockquote>\n")
    (end-quote       . "\n</blockquote>")
    (begin-cite      . "<citation role=\"%s\">")
    (begin-cite-author . "<citation role=\"%s\">A:")
    (begin-cite-year . "<citation role=\"%s\">Y:")
    (end-cite        . "</citation>")
    (begin-quote-item . "<para>")
    (end-quote-item  . "</para>")
    (begin-uli       . "<itemizedlist mark=\"bullet\">\n")
    (end-uli         . "\n</itemizedlist>")
    (begin-uli-item  . "<listitem><para>")
    (end-uli-item    . "</para></listitem>")
    (begin-oli       . "<orderedlist>\n")
    (end-oli         . "\n</orderedlist>")
    (begin-oli-item  . "<listitem><para>")
    (end-oli-item    . "</para></listitem>")
    (begin-dl        . "<variablelist>\n")
    (end-dl          . "\n</variablelist>")
    (begin-dl-item   . "<varlistentry>\n")
    (end-dl-item     . "\n</varlistentry>")
    (begin-ddt       . "<term>")
    (end-ddt         . "</term>")
    (begin-dde       . "<listitem><para>")
    (end-dde         . "</para></listitem>")
    (begin-table     . "<informaltable>\n")
    (end-table       . "</informaltable>")
    (begin-table-group . "  <tgroup cols='%s'>\n")
    (end-table-group . "  </tgroup>\n")
    (begin-table-row . "    <row>\n")
    (end-table-row   . "    </row>\n")
    (begin-table-entry . "      <entry>")
    (end-table-entry . "</entry>\n"))
  "Strings used for marking up text.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-docbook)

(defcustom muse-docbook-encoding-default 'utf-8
  "The default Emacs buffer encoding to use in published files.
This will be used if no special characters are found."
  :type 'symbol
  :group 'muse-docbook)

(defcustom muse-docbook-charset-default "utf-8"
  "The default DocBook XML charset to use if no translation is
found in `muse-docbook-encoding-map'."
  :type 'string
  :group 'muse-docbook)

(defun muse-docbook-encoding ()
  (muse-xml-transform-content-type
   (or (and (boundp 'buffer-file-coding-system)
            buffer-file-coding-system)
       muse-docbook-encoding-default)
   muse-docbook-charset-default))

(defun muse-docbook-markup-paragraph ()
  (catch 'bail-out
    (let ((end (copy-marker (match-end 0) t)))
      (goto-char (match-beginning 0))
      (when (save-excursion
              (save-match-data
                (and (not (get-text-property (max (point-min) (1- (point)))
                                             'muse-no-paragraph))
                     (re-search-backward
                      "<\\(/?\\)\\(para\\|footnote\\|literallayout\\)[ >]"
                      nil t)
                     (cond ((string= (match-string 2) "literallayout")
                            (and (not (string= (match-string 1) "/"))
                                 (throw 'bail-out t)))
                           ((string= (match-string 2) "para")
                            (and
                             (not (string= (match-string 1) "/"))
                             ;; don't mess up nested lists
                             (not (and (muse-looking-back "<listitem>")
                                       (throw 'bail-out t)))))
                           ((string= (match-string 2) "footnote")
                            (string= (match-string 1) "/"))
                           (t nil)))))
        (when (get-text-property (1- (point)) 'muse-end-list)
          (goto-char (previous-single-property-change (1- (point))
                                                      'muse-end-list)))
        (muse-insert-markup "</para>"))
      (goto-char end))
    (cond
     ((eobp)
      (unless (bolp)
        (insert "\n")))
     ((get-text-property (point) 'muse-no-paragraph)
      (forward-char 1)
      nil)
     ((eq (char-after) ?\<)
      (when (looking-at (concat "<\\(emphasis\\|systemitem\\|inlinemediaobject"
                                "\\|u?link\\|anchor\\|email\\)[ >]"))
        (muse-insert-markup "<para>")))
     (t
      (muse-insert-markup "<para>")))))

(defun muse-docbook-get-author (&optional author)
  "Split the AUTHOR directive into separate fields.
AUTHOR should be of the form: \"Firstname Other Names Lastname\",
and anything after `Firstname' is optional."
  (setq author (save-match-data (split-string author)))
  (let ((num-el (length author)))
    (cond ((eq num-el 1)
           (concat "<firstname>" (car author) "</firstname>"))
          ((eq num-el 2)
           (concat "<firstname>" (nth 0 author) "</firstname>"
                   "<surname>" (nth 1 author) "</surname>"))
          ((eq num-el 3)
           (concat "<firstname>" (nth 0 author) "</firstname>"
                   "<othername>" (nth 1 author) "</othername>"
                   "<surname>" (nth 2 author) "</surname>"))
          (t
           (let (first last)
             (setq first (car author))
             (setq author (nreverse (cdr author)))
             (setq last (car author))
             (setq author (nreverse (cdr author)))
             (concat "<firstname>" first "</firstname>"
                     "<othername>"
                     (mapconcat 'identity author " ")
                     "</othername>"
                     "<surname>" last "</surname>"))))))

(defun muse-docbook-fixup-images ()
  (goto-char (point-min))
  (while (re-search-forward (concat "<imagedata fileref=\"[^\"]+\""
                                    " format=\"\\([^\"]+\\)\" />$")
                            nil t)
    (replace-match (upcase (match-string 1)) t t nil 1)))

(defun muse-docbook-fixup-citations ()
  ;; remove the role attribute if there is no role
  (goto-char (point-min))
  (while (re-search-forward "<\\(citation role=\"nil\"\\)>" nil t)
    (replace-match "citation" t t nil 1))
  ;; replace colons in multi-head citations with semicolons
  (goto-char (point-min))
  (while (re-search-forward "<citation.*>" nil t)
    (let ((start (point))
          (end (re-search-forward "</citation>")))
      (save-restriction
        (narrow-to-region start end)
        (goto-char (point-min))
        (while (re-search-forward "," nil t)
          (replace-match ";"))))))

(defun muse-docbook-munge-buffer ()
  (muse-docbook-fixup-images)
  (muse-docbook-fixup-citations))

(defun muse-docbook-entities ()
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "<citation" nil t)
        (concat
         " [\n<!ENTITY bibliography SYSTEM \""
         (if (string-match ".short$" (muse-page-name))
             (substring (muse-page-name) 0 -6)
           (muse-page-name))
         ".bib.xml\">\n]")
      "")))

(defun muse-docbook-bibliography ()
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "<citation" nil t)
        "&bibliography;\n"
      "")))

(defun muse-docbook-finalize-buffer ()
  (when (boundp 'buffer-file-coding-system)
    (when (memq buffer-file-coding-system '(no-conversion undecided-unix))
      ;; make it agree with the default charset
      (setq buffer-file-coding-system muse-docbook-encoding-default))))

;;; Register the Muse DocBook XML Publisher

(muse-define-style "docbook"
                   :suffix     'muse-docbook-extension
                   :regexps    'muse-docbook-markup-regexps
                   :functions  'muse-docbook-markup-functions
                   :strings    'muse-docbook-markup-strings
                   :specials   'muse-xml-decide-specials
                   :before-end 'muse-docbook-munge-buffer
                   :after      'muse-docbook-finalize-buffer
                   :header     'muse-docbook-header
                   :footer     'muse-docbook-footer
                   :browser    'find-file)

(provide 'muse-docbook)

;;; muse-docbook.el ends here
