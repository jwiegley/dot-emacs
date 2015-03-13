;;; muse-html.el --- publish to HTML and XHTML

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

;; Zhiqiang Ye (yezq AT mail DOT cbi DOT pku DOT edu DOT cn) suggested
;; appending an 'encoding="..."' fragment to the first line of the
;; sample publishing header so that when editing the resulting XHTML
;; file, Emacs would use the proper encoding.

;; Sun Jiyang (sunyijiang AT gmail DOT com) came up with the idea for
;; the <src> tag and provided an implementation for emacs-wiki.

;; Charles Wang (wcy123 AT gmail DOT com) provided an initial
;; implementation of the <src> tag for Muse.

;; Clinton Ebadi (clinton AT unknownlamer DOT org) provided further
;; ideas for the implementation of the <src> tag.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse HTML Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-regexps)
(require 'muse-xml-common)

(defgroup muse-html nil
  "Options controlling the behavior of Muse HTML publishing."
  :group 'muse-publish)

(defcustom muse-html-extension ".html"
  "Default file extension for publishing HTML files."
  :type 'string
  :group 'muse-html)

(defcustom muse-xhtml-extension ".html"
  "Default file extension for publishing XHTML files."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-style-sheet
  "<style type=\"text/css\">
body {
  background: white; color: black;
  margin-left: 3%; margin-right: 7%;
}

p { margin-top: 1% }
p.verse { margin-left: 3% }

.example { margin-left: 3% }

h2 {
  margin-top: 25px;
  margin-bottom: 0px;
}
h3 { margin-bottom: 0px; }
    </style>"
  "Store your stylesheet definitions here.
This is used in `muse-html-header'.
You can put raw CSS in here or a <link> tag to an external stylesheet.
This text may contain <lisp> markup tags.

An example of using <link> is as follows.

<link rel=\"stylesheet\" type=\"text/css\" charset=\"utf-8\" media=\"all\" href=\"/default.css\">"
  :type 'string
  :group 'muse-html)

(defcustom muse-xhtml-style-sheet
  "<style type=\"text/css\">
body {
  background: white; color: black;
  margin-left: 3%; margin-right: 7%;
}

p { margin-top: 1% }
p.verse { margin-left: 3% }

.example { margin-left: 3% }

h2 {
  margin-top: 25px;
  margin-bottom: 0px;
}
h3 { margin-bottom: 0px; }
    </style>"
  "Store your stylesheet definitions here.
This is used in `muse-xhtml-header'.
You can put raw CSS in here or a <link> tag to an external stylesheet.
This text may contain <lisp> markup tags.

An example of using <link> is as follows.

<link rel=\"stylesheet\" type=\"text/css\" charset=\"utf-8\" media=\"all\" href=\"/default.css\" />"
  :type 'string
  :group 'muse-html)

(defcustom muse-html-header
  "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0 Transitional//EN\">
<html>
  <head>
    <title><lisp>
  (concat (muse-publishing-directive \"title\")
          (let ((author (muse-publishing-directive \"author\")))
            (if (not (string= author (user-full-name)))
                (concat \" (by \" author \")\"))))</lisp></title>
    <meta name=\"generator\" content=\"muse.el\">
    <meta http-equiv=\"<lisp>muse-html-meta-http-equiv</lisp>\"
          content=\"<lisp>muse-html-meta-content-type</lisp>\">
    <lisp>
      (let ((maintainer (muse-style-element :maintainer)))
        (when maintainer
          (concat \"<link rev=\\\"made\\\" href=\\\"\" maintainer \"\\\">\")))
    </lisp><lisp>
      (muse-style-element :style-sheet muse-publishing-current-style)
    </lisp>
  </head>
  <body>
    <h1><lisp>
  (concat (muse-publishing-directive \"title\")
          (let ((author (muse-publishing-directive \"author\")))
            (if (not (string= author (user-full-name)))
                (concat \" (by \" author \")\"))))</lisp></h1>
    <!-- Page published by Emacs Muse begins here -->\n"
  "Header used for publishing HTML files.  This may be text or a filename."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-footer "
<!-- Page published by Emacs Muse ends here -->
  </body>
</html>\n"
  "Footer used for publishing HTML files.  This may be text or a filename."
  :type 'string
  :group 'muse-html)

(defcustom muse-xhtml-header
  "<?xml version=\"1.0\" encoding=\"<lisp>
  (muse-html-encoding)</lisp>\"?>
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
    \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
  <head>
    <title><lisp>
  (concat (muse-publishing-directive \"title\")
          (let ((author (muse-publishing-directive \"author\")))
            (if (not (string= author (user-full-name)))
                (concat \" (by \" author \")\"))))</lisp></title>
    <meta name=\"generator\" content=\"muse.el\" />
    <meta http-equiv=\"<lisp>muse-html-meta-http-equiv</lisp>\"
          content=\"<lisp>muse-html-meta-content-type</lisp>\" />
    <lisp>
      (let ((maintainer (muse-style-element :maintainer)))
        (when maintainer
          (concat \"<link rev=\\\"made\\\" href=\\\"\" maintainer \"\\\" />\")))
    </lisp><lisp>
      (muse-style-element :style-sheet muse-publishing-current-style)
    </lisp>
  </head>
  <body>
    <h1><lisp>
  (concat (muse-publishing-directive \"title\")
          (let ((author (muse-publishing-directive \"author\")))
            (if (not (string= author (user-full-name)))
                (concat \" (by \" author \")\"))))</lisp></h1>
    <!-- Page published by Emacs Muse begins here -->\n"
  "Header used for publishing XHTML files.  This may be text or a filename."
  :type 'string
  :group 'muse-html)

(defcustom muse-xhtml-footer "
<!-- Page published by Emacs Muse ends here -->
  </body>
</html>\n"
  "Footer used for publishing XHTML files.  This may be text or a filename."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-anchor-on-word nil
  "When true, anchors surround the closest word. This allows you
to select them in a browser (i.e. for pasting), but has the
side-effect of marking up headers in multiple colors if your
header style is different from your link style."
  :type 'boolean
  :group 'muse-html)

(defcustom muse-html-table-attributes
  " class=\"muse-table\" border=\"2\" cellpadding=\"5\""
  "The attribute to be used with HTML <table> tags.
Note that Muse supports insertion of raw HTML tags, as long
as you wrap the region in <literal></literal>."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-markup-regexps
  `(;; Beginning of doc, end of doc, or plain paragraph separator
    (10000 ,(concat "\\(\\(\n\\(?:[" muse-regexp-blank "]*\n\\)*"
                    "\\([" muse-regexp-blank "]*\n\\)\\)"
                    "\\|\\`\\s-*\\|\\s-*\\'\\)")
           ;; this is somewhat repetitive because we only require the
           ;; line just before the paragraph beginning to be not
           ;; read-only
           3 muse-html-markup-paragraph))
  "List of markup rules for publishing a Muse page to HTML.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-html)

(defcustom muse-html-markup-functions
  '((anchor   . muse-html-markup-anchor)
    (table    . muse-html-markup-table)
    (footnote . muse-html-markup-footnote))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-html)

(defcustom muse-html-markup-strings
  '((image-with-desc . "<table class=\"image\" width=\"100%%\">
  <tr><td align=\"center\"><img src=\"%1%.%2%\" alt=\"%3%\"></td></tr>
  <tr><td align=\"center\" class=\"image-caption\">%3%</td></tr>
</table>")
    (image           . "<img src=\"%s.%s\" alt=\"\">")
    (image-link      . "<a class=\"image-link\" href=\"%s\">
<img src=\"%s.%s\"></a>")
    (anchor-ref      . "<a href=\"#%s\">%s</a>")
    (url             . "<a href=\"%s\">%s</a>")
    (link            . "<a href=\"%s\">%s</a>")
    (link-and-anchor . "<a href=\"%s#%s\">%s</a>")
    (email-addr      . "<a href=\"mailto:%s\">%s</a>")
    (anchor          . "<a name=\"%1%\" id=\"%1%\">")
    (emdash          . "%s&mdash;%s")
    (comment-begin   . "<!-- ")
    (comment-end     . " -->")
    (rule            . "<hr>")
    (fn-sep          . "<hr>\n")
    (no-break-space  . "&nbsp;")
    (line-break      . "<br>")
    (enddots         . "....")
    (dots            . "...")
    (section         . "<h2>")
    (section-end     . "</h2>")
    (subsection      . "<h3>")
    (subsection-end  . "</h3>")
    (subsubsection   . "<h4>")
    (subsubsection-end . "</h4>")
    (section-other   . "<h5>")
    (section-other-end . "</h5>")
    (begin-underline . "<u>")
    (end-underline   . "</u>")
    (begin-literal   . "<code>")
    (end-literal     . "</code>")
    (begin-cite      . "<span class=\"citation\">")
    (begin-cite-author . "<span class=\"citation-author\">")
    (begin-cite-year . "<span class=\"citation-year\">")
    (end-cite        . "</span>")
    (begin-emph      . "<em>")
    (end-emph        . "</em>")
    (begin-more-emph . "<strong>")
    (end-more-emph   . "</strong>")
    (begin-most-emph . "<strong><em>")
    (end-most-emph   . "</em></strong>")
    (begin-verse     . "<p class=\"verse\">\n")
    (verse-space     . "&nbsp;&nbsp;")
    (end-verse-line  . "<br>")
    (end-last-stanza-line . "<br>")
    (empty-verse-line . "<br>")
    (end-verse       . "</p>")
    (begin-example   . "<pre class=\"example\">")
    (end-example     . "</pre>")
    (begin-center    . "<center>\n<p>")
    (end-center      . "</p>\n</center>")
    (begin-quote     . "<blockquote>\n")
    (end-quote       . "\n</blockquote>")
    (begin-quote-item . "<p class=\"quoted\">")
    (end-quote-item  . "</p>")
    (begin-uli       . "<ul>\n")
    (end-uli         . "\n</ul>")
    (begin-uli-item  . "<li>")
    (end-uli-item    . "</li>")
    (begin-oli       . "<ol>\n")
    (end-oli         . "\n</ol>")
    (begin-oli-item  . "<li>")
    (end-oli-item    . "</li>")
    (begin-dl        . "<dl>\n")
    (end-dl          . "\n</dl>")
    (begin-ddt       . "<dt><strong>")
    (end-ddt         . "</strong></dt>")
    (begin-dde       . "<dd>")
    (end-dde         . "</dd>")
    (begin-table     . "<table%s>\n")
    (end-table       . "</table>")
    (begin-table-row . "    <tr>\n")
    (end-table-row   . "    </tr>\n")
    (begin-table-entry . "      <%s>")
    (end-table-entry . "</%s>\n"))
  "Strings used for marking up text as HTML.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-html)

(defcustom muse-xhtml-markup-strings
  '((image-with-desc . "<table class=\"image\" width=\"100%%\">
  <tr><td align=\"center\"><img src=\"%1%.%2%\" alt=\"%3%\" /></td></tr>
  <tr><td align=\"center\" class=\"image-caption\">%3%</td></tr>
</table>")
    (image           . "<img src=\"%s.%s\" alt=\"\" />")
    (image-link      . "<a class=\"image-link\" href=\"%s\">
<img src=\"%s.%s\" alt=\"\" /></a>")
    (rule            . "<hr />")
    (fn-sep          . "<hr />\n")
    (line-break      . "<br />")
    (begin-underline . "<span style=\"text-decoration: underline;\">")
    (end-underline   . "</span>")
    (begin-center    . "<p style=\"text-align: center;\">\n")
    (end-center      . "\n</p>")
    (end-verse-line  . "<br />")
    (end-last-stanza-line . "<br />")
    (empty-verse-line . "<br />"))
  "Strings used for marking up text as XHTML.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles.

If a markup rule is not found here, `muse-html-markup-strings' is
searched."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-html)

(defcustom muse-xhtml1.1-markup-strings
  '((anchor          . "<a id=\"%s\">"))
  "Strings used for marking up text as XHTML 1.1.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles.

If a markup rule is not found here, `muse-xhtml-markup-strings'
and `muse-html-markup-strings' are searched."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-html)

(defcustom muse-html-markup-tags
  '(("class" t t   t muse-html-class-tag)
    ("div"   t t   t muse-html-div-tag)
    ("src"   t t nil muse-html-src-tag))
 "A list of tag specifications, for specially marking up HTML."
  :type '(repeat (list (string :tag "Markup tag")
                       (boolean :tag "Expect closing tag" :value t)
                       (boolean :tag "Parse attributes" :value nil)
                       (boolean :tag "Nestable" :value nil)
                       function))
  :group 'muse-html)

(defcustom muse-html-meta-http-equiv "Content-Type"
  "The http-equiv attribute used for the HTML <meta> tag."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-meta-content-type "text/html"
  "The content type used for the HTML <meta> tag.
If you are striving for XHTML 1.1 compliance, you may want to
change this to \"application/xhtml+xml\"."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-meta-content-encoding (if (featurep 'mule)
                                              'detect
                                            "iso-8859-1")
  "The charset to append to the HTML <meta> tag.
If set to the symbol 'detect, use `muse-html-encoding-map' to try
and determine the HTML charset from emacs's coding.  If set to a
string, this string will be used to force a particular charset"
  :type '(choice string symbol)
  :group 'muse-html)

(defcustom muse-html-encoding-default 'iso-8859-1
  "The default Emacs buffer encoding to use in published files.
This will be used if no special characters are found."
  :type 'symbol
  :group 'muse-html)

(defcustom muse-html-charset-default "iso-8859-1"
  "The default HTML meta charset to use if no translation is found in
`muse-html-encoding-map'."
  :type 'string
  :group 'muse-html)

(defcustom muse-html-src-allowed-modes t
  "Modes that we allow the <src> tag to colorize.
If t, permit the <src> tag to colorize any mode.

If a list of mode names, such as '(\"html\" \"latex\"), and the
lang argument to <src> is not in the list, then use fundamental
mode instead."
  :type '(choice (const :tag "Any" t)
                 (repeat (string :tag "Mode")))
  :group 'muse-html)

(defun muse-html-insert-anchor (anchor)
  "Insert an anchor, either around the word at point, or within a tag."
  (skip-chars-forward (concat muse-regexp-blank "\n"))
  (if (looking-at (concat "<\\([^" muse-regexp-blank "/>\n]+\\)>"))
      (let ((tag (match-string 1)))
        (goto-char (match-end 0))
        (muse-insert-markup (muse-markup-text 'anchor anchor))
        (when muse-html-anchor-on-word
          (or (and (search-forward (format "</%s>" tag)
                                   (muse-line-end-position) t)
                   (goto-char (match-beginning 0)))
              (forward-word 1)))
        (muse-insert-markup "</a>"))
    (muse-insert-markup (muse-markup-text 'anchor anchor))
    (when muse-html-anchor-on-word
      (forward-word 1))
    (muse-insert-markup "</a>\n")))

(defun muse-html-markup-anchor ()
  (unless (get-text-property (match-end 1) 'muse-link)
    (save-match-data
      (muse-html-insert-anchor (match-string 2)))
    (match-string 1)))

(defun muse-html-markup-paragraph ()
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
    (cond
     ((looking-at "<\\(em\\|strong\\|code\\|span\\)[ >]")
      (muse-insert-markup "<p>"))
     ((looking-at "<a ")
      (if (looking-at "<a[^>\n]+><img")
          (muse-insert-markup "<p class=\"image-link\">")
        (muse-insert-markup "<p>")))
     ((looking-at "<img[ >]")
      (muse-insert-markup "<p class=\"image\">"))
     (t
      (forward-char 1)
      nil)))
   ((muse-looking-back "\\(</h[1-4]>\\|<hr>\\)\n\n")
    (muse-insert-markup "<p class=\"first\">"))
   (t
    (muse-insert-markup "<p>"))))

(defun muse-html-markup-footnote ()
  (cond
   ((get-text-property (match-beginning 0) 'muse-link)
    nil)
   ((= (muse-line-beginning-position) (match-beginning 0))
    (prog1
        (let ((text (match-string 1)))
          (muse-insert-markup
           (concat "<p class=\"footnote\">"
                   "<a class=\"footnum\" name=\"fn." text
                   "\" href=\"#fnr." text "\">"
                   text ".</a>")))
      (save-excursion
        (save-match-data
          (let* ((beg (goto-char (match-end 0)))
                 (end (and (search-forward "\n\n" nil t)
                           (prog1
                               (copy-marker (match-beginning 0))
                             (goto-char beg)))))
            (while (re-search-forward (concat "^["
                                              muse-regexp-blank
                                              "]+\\([^\n]\\)")
                                      end t)
              (replace-match "\\1" t)))))
      (replace-match "")))
   (t (let ((text (match-string 1)))
        (muse-insert-markup
         (concat "<sup><a class=\"footref\" name=\"fnr." text
                 "\" href=\"#fn." text "\">"
                 text "</a></sup>")))
      (replace-match ""))))

(defun muse-html-markup-table ()
  (muse-xml-markup-table muse-html-table-attributes))

;; Handling of tags for HTML

(defun muse-html-strip-links (string)
  "Remove all HTML links from STRING."
  (muse-replace-regexp-in-string "\\(<a .*?>\\|</a>\\)" "" string nil t))

(defun muse-html-insert-contents (depth)
  "Scan the current document and generate a table of contents at point.
DEPTH indicates how many levels of headings to include.  The default is 2."
  (let ((max-depth (or depth 2))
        (index 1)
        base contents l end)
    (save-excursion
      (goto-char (point-min))
      (search-forward "Page published by Emacs Muse begins here" nil t)
      (catch 'done
        (while (re-search-forward "<h\\([0-9]+\\)>\\(.+?\\)</h\\1>$" nil t)
          (unless (and (get-text-property (point) 'read-only)
                       (not (get-text-property (match-beginning 0)
                                               'muse-contents)))
            (remove-text-properties (match-beginning 0) (match-end 0)
                                    '(muse-contents nil))
            (setq l (1- (string-to-number (match-string 1))))
            (if (null base)
                (setq base l)
              (if (< l base)
                  (throw 'done t)))
            (when (<= l max-depth)
              ;; escape specials now before copying the text, so that we
              ;; can deal sanely with both emphasis in titles and
              ;; special characters
              (goto-char (match-end 2))
              (setq end (point-marker))
              (muse-publish-escape-specials (match-beginning 2) end
                                            nil 'document)
              (muse-publish-mark-read-only (match-beginning 2) end)
              (setq contents (cons (cons l (buffer-substring-no-properties
                                            (match-beginning 2) end))
                                   contents))
              (set-marker end nil)
              (goto-char (match-beginning 2))
              (muse-html-insert-anchor (concat "sec" (int-to-string index)))
              (setq index (1+ index)))))))
    (setq index 1 contents (nreverse contents))
    (let ((depth 1) (sub-open 0) (p (point)))
      (muse-insert-markup "<div class=\"contents\">\n<dl>\n")
      (while contents
        (muse-insert-markup "<dt>\n"
                            "<a href=\"#sec" (int-to-string index) "\">"
                            (muse-html-strip-links (cdar contents))
                            "</a>\n"
                            "</dt>\n")
        (setq index (1+ index)
              depth (caar contents)
              contents (cdr contents))
        (when contents
          (cond
           ((< (caar contents) depth)
            (let ((idx (caar contents)))
              (while (< idx depth)
                (muse-insert-markup "</dl>\n</dd>\n")
                (setq sub-open (1- sub-open)
                      idx (1+ idx)))))
           ((> (caar contents) depth) ; can't jump more than one ahead
            (muse-insert-markup "<dd>\n<dl>\n")
            (setq sub-open (1+ sub-open))))))
      (while (> sub-open 0)
        (muse-insert-markup "</dl>\n</dd>\n")
        (setq sub-open (1- sub-open)))
      (muse-insert-markup "</dl>\n</div>\n")
      (muse-publish-mark-read-only p (point)))))

(defun muse-html-denote-headings ()
  "Place a text property on any headings in the current buffer.
This allows the headings to be picked up later on if publishing a
table of contents."
  (save-excursion
    (goto-char (point-min))
    (search-forward "Page published by Emacs Muse begins here" nil t)
    (while (re-search-forward "<h\\([0-9]+\\)>\\(.+?\\)</h\\1>$" nil t)
      (unless (get-text-property (point) 'read-only)
        (add-text-properties (match-beginning 0) (match-end 0)
                             '(muse-contents t))))))

(defun muse-html-class-tag (beg end attrs)
  (let ((name (cdr (assoc "name" attrs))))
    (when name
      (goto-char beg)
      (muse-insert-markup "<span class=\"" name "\">")
      (save-excursion
        (goto-char end)
        (muse-insert-markup "</span>")))))

(defun muse-html-div-tag (beg end attrs)
  "Publish a <div> tag for HTML."
  (let ((id (cdr (assoc "id" attrs)))
        (style (cdr (assoc "style" attrs))))
    (when (or id style)
      (goto-char beg)
      (if (null id)
          (muse-insert-markup "<div style=\"" style "\">")
        (muse-insert-markup "<div id=\"" id "\">"))
      (save-excursion
        (goto-char end)
        (muse-insert-markup "</div>")))))

(defun muse-html-src-tag (beg end attrs)
  "Publish the region using htmlize.
The language to use may be specified by the \"lang\" attribute.

Muse will look for a function named LANG-mode, where LANG is the
value of the \"lang\" attribute.

This tag requires htmlize 1.34 or later in order to work."
  (if (condition-case nil
          (progn
            (require 'htmlize)
            (if (fboundp 'htmlize-region-for-paste)
                nil
              (muse-display-warning
               (concat "The `htmlize-region-for-paste' function was not"
                       " found.\nThis is available in htmlize.el 1.34"
                       " or later."))
              t))
        (error nil t))
      ;; if htmlize.el was not found, treat this like an example tag
      (muse-publish-example-tag beg end)
    (muse-publish-ensure-block beg end)
    (let* ((lang (cdr (assoc "lang" attrs)))
           (mode (or (and (not (eq muse-html-src-allowed-modes t))
                          (not (member lang muse-html-src-allowed-modes))
                          'fundamental-mode)
                     (intern-soft (concat lang "-mode"))))
           (text (muse-delete-and-extract-region beg end))
           (htmltext
            (with-temp-buffer
              (insert text)
              (if (functionp mode)
                  (funcall mode)
                (fundamental-mode))
              (font-lock-fontify-buffer)
              ;; silence the byte-compiler
              (when (fboundp 'htmlize-region-for-paste)
                ;; transform the region to HTML
                (htmlize-region-for-paste (point-min) (point-max))))))
      (save-restriction
        (narrow-to-region (point) (point))
        (insert htmltext)
        (goto-char (point-min))
        (re-search-forward "<pre\\([^>]*\\)>\n?" nil t)
        (replace-match "<pre class=\"src\">")
        (goto-char (point-max))
        (muse-publish-mark-read-only (point-min) (point-max))))))

;; Register the Muse HTML Publisher

(defun muse-html-browse-file (file)
  (browse-url (concat "file:" file)))

(defun muse-html-encoding ()
  (if (stringp muse-html-meta-content-encoding)
      muse-html-meta-content-encoding
    (muse-xml-transform-content-type
     (or (and (boundp 'buffer-file-coding-system)
              buffer-file-coding-system)
         muse-html-encoding-default)
     muse-html-charset-default)))

(defun muse-html-prepare-buffer ()
  (make-local-variable 'muse-html-meta-http-equiv)
  (set (make-local-variable 'muse-html-meta-content-type)
       (if (save-match-data
             (string-match "charset=" muse-html-meta-content-type))
           muse-html-meta-content-type
         (concat muse-html-meta-content-type "; charset="
                 (muse-html-encoding)))))

(defun muse-html-munge-buffer ()
  (if muse-publish-generate-contents
      (progn
        (goto-char (car muse-publish-generate-contents))
        (muse-html-insert-contents (cdr muse-publish-generate-contents))
        (setq muse-publish-generate-contents nil))
    (muse-html-denote-headings)))

(defun muse-html-finalize-buffer ()
  (when (and (boundp 'buffer-file-coding-system)
             (memq buffer-file-coding-system '(no-conversion undecided-unix)))
    ;; make it agree with the default charset
    (setq buffer-file-coding-system muse-html-encoding-default)))

;;; Register the Muse HTML and XHTML Publishers

(muse-define-style "html"
                   :suffix    'muse-html-extension
                   :regexps   'muse-html-markup-regexps
                   :functions 'muse-html-markup-functions
                   :strings   'muse-html-markup-strings
                   :tags      'muse-html-markup-tags
                   :specials  'muse-xml-decide-specials
                   :before    'muse-html-prepare-buffer
                   :before-end 'muse-html-munge-buffer
                   :after     'muse-html-finalize-buffer
                   :header    'muse-html-header
                   :footer    'muse-html-footer
                   :style-sheet 'muse-html-style-sheet
                   :browser   'muse-html-browse-file)

(muse-derive-style "xhtml" "html"
                   :suffix    'muse-xhtml-extension
                   :strings   'muse-xhtml-markup-strings
                   :header    'muse-xhtml-header
                   :footer    'muse-xhtml-footer
                   :style-sheet 'muse-xhtml-style-sheet)

;; xhtml1.0 is an alias for xhtml
(muse-derive-style "xhtml1.0" "xhtml")

;; xhtml1.1 has some quirks that need attention from us
(muse-derive-style "xhtml1.1" "xhtml"
                   :strings   'muse-xhtml1.1-markup-strings)

(provide 'muse-html)

;;; muse-html.el ends here
