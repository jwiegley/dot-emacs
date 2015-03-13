;;; muse-journal.el --- keep and publish a journal

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

;; The module facilitates the keeping and publication of a journal.
;; When publishing to HTML, it assumes the form of a web log, or blog.
;;
;; The input format for each entry is as follows:
;;
;;   * 20040317: Title of entry
;;
;;   Text for the entry.
;;
;;   <qotd>
;;   "You know who you are. It comes down to a simple gut check: You
;;   either love what you do or you don't. Period." -- P. Bronson
;;   </qotd>
;;
;; The "qotd", or Quote of the Day, is entirely optional.  When
;; generated to HTML, this entry is rendered as:
;;
;;   <div class="entry">
;;     <div class="entry-qotd">
;;       <h3>Quote of the Day:</h3>
;;       <p>"You know who you are. It comes down to a simple gut
;;         check: You either love what you do or you don't. Period."
;;         -- P. Bronson</p>
;;     </div>
;;     <div class="entry-body">
;;       <div class="entry-head">
;;         <div class="entry-date">
;;           <span class="date">March 17, 2004</span>
;;         </div>
;;         <div class="entry-title">
;;           <h2>Title of entry</h2>
;;         </div>
;;       </div>
;;       <div class="entry-text">
;;         <p>Text for the entry.</p>
;;       </div>
;;     </div>
;;   </div>
;;
;; The plurality of "div" tags makes it possible to display the
;; entries in any form you wish, using a CSS style.
;;
;; Also, an .RDF file can be generated from your journal by publishing
;; it with the "rdf" style.  It uses the first two sentences of the
;; first paragraph of each entry as its "description", and
;; autogenerates tags for linking to the various entries.

;;; Contributors:

;; René Stadler (mail AT renestadler DOT de) provided a patch that
;; causes dates in RSS feeds to be generated in a format that RSS
;; readers can parse.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Journal Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-html)
(require 'muse-latex)
(require 'muse-book)

(defgroup muse-journal nil
  "Rules for transforming a journal into its final form."
  :group 'muse-publish)

(defcustom muse-journal-heading-regexp
  "\\(?:\\([0-9]+\\)\\(?:: \\)?\\)?\\(.+?\\)?"
  "A regexp that matches a journal heading.
Paren group 1 is the ISO date, group 2 is the optional category,
and group 3 is the optional heading for the entry."
  :type 'regexp
  :group 'muse-journal)

(defcustom muse-journal-date-format "%a, %e %b %Y"
  "Date format to use for journal entries."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-html-heading-regexp
  (concat "^<h2[^>\n]*>" muse-journal-heading-regexp "</h2>$")
  "A regexp that matches a journal heading from an HTML document.
Paren group 1 is the ISO date, group 2 is the optional category,
and group 3 is the optional heading for the entry."
  :type 'regexp
  :group 'muse-journal)

(defcustom muse-journal-rss-heading-regexp
  (concat "^\\* " muse-journal-heading-regexp "$")
  "A regexp that matches a journal heading from an HTML document.
Paren group 1 is the ISO date, group 2 is the optional category,
and group 3 is the optional heading for the entry."
  :type 'regexp
  :group 'muse-journal)

(defcustom muse-journal-html-entry-template
  "<div class=\"entry\">
  <a name=\"%anchor%\" style=\"text-decoration: none\">&nbsp;</a>
  <div class=\"entry-body\">
    <div class=\"entry-head\">
      <div class=\"entry-date\">
        <span class=\"date\">%date%</span>
      </div>
      <div class=\"entry-title\">
        <h2>%title%</h2>
      </div>
    </div>
    <div class=\"entry-text\">
      <div class=\"entry-qotd\">
        <p>%qotd%</p>
      </div>
%text%
    </div>
  </div>
</div>\n\n"
  "Template used to publish individual journal entries as HTML.
This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-latex-section
  "\\section*{%title% \\hfill {\\normalsize %date%}}
\\addcontentsline{toc}{chapter}{%title%}"
  "Template used to publish a LaTeX section."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-latex-subsection
  "\\subsection*{%title%}
\\addcontentsline{toc}{section}{%title%}"
  "Template used to publish a LaTeX subsection."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-markup-tags
  '(("qotd" t nil nil muse-journal-qotd-tag))
  "A list of tag specifications, for specially marking up Journal entries.
See `muse-publish-markup-tags' for more info.

This is used by journal-latex and its related styles, as well as
the journal-rss-entry style, which both journal-rdf and
journal-rss use."
  :type '(repeat (list (string :tag "Markup tag")
                       (boolean :tag "Expect closing tag" :value t)
                       (boolean :tag "Parse attributes" :value nil)
                       (boolean :tag "Nestable" :value nil)
                       function))
  :group 'muse-journal)

;; FIXME: This doesn't appear to be used.
(defun muse-journal-generate-pages ()
  (let ((output-dir (muse-style-element :path)))
    (goto-char (point-min))
    (while (re-search-forward muse-journal-heading-regexp nil t)
      (let* ((date (match-string 1))
             (category (match-string 1))
             (category-file (concat output-dir category "/index.html"))
             (heading (match-string 1)))
        t))))

(defcustom muse-journal-rdf-extension ".rdf"
  "Default file extension for publishing RDF (RSS 1.0) files."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rdf-base-url ""
  "The base URL of the website referenced by the RDF file."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rdf-header
  "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"
         xmlns=\"http://purl.org/rss/1.0/\"
         xmlns:dc=\"http://purl.org/dc/elements/1.1/\">
  <channel rdf:about=\"<lisp>(concat (muse-style-element :base-url)
                                     (muse-publish-link-name))</lisp>\">
    <title><lisp>(muse-publishing-directive \"title\")</lisp></title>
    <link><lisp>(concat (muse-style-element :base-url)
                       (concat (muse-page-name)
                               muse-html-extension))</lisp></link>
    <description><lisp>(muse-publishing-directive \"desc\")</lisp></description>
    <items>
      <rdf:Seq>
        <rdf:li resource=\"<lisp>
          (concat (muse-style-element :base-url)
                  (concat (muse-page-name)
                          muse-html-extension))</lisp>\"/>
      </rdf:Seq>
    </items>
  </channel>\n"
  "Header used for publishing RDF (RSS 1.0) files.
This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rdf-footer
  "</rdf:RDF>\n"
  "Footer used for publishing RDF (RSS 1.0) files.
This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rdf-date-format
  "%Y-%m-%dT%H:%M:%S"
  "Date format to use for RDF entries."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rdf-entry-template
  "\n  <item rdf:about=\"%link%#%anchor%\">
    <title>%title%</title>
    <description>
      %desc%
    </description>
    <link>%link%#%anchor%</link>
    <dc:date>%date%</dc:date>
    <dc:creator>%maintainer%</dc:creator>
  </item>\n"
  "Template used to publish individual journal entries as RDF.
This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rdf-summarize-entries nil
  "If non-nil, include only summaries in the RDF file, not the full data.

The default is nil, because this annoys some subscribers."
  :type 'boolean
  :group 'muse-journal)

(defcustom muse-journal-rss-extension ".xml"
  "Default file extension for publishing RSS 2.0 files."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rss-base-url ""
  "The base URL of the website referenced by the RSS file."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rss-header
  "<\?xml version=\"1.0\" encoding=\"<lisp>
  (muse-html-encoding)</lisp>\"?>
<rss version=\"2.0\">
  <channel>
    <title><lisp>(muse-publishing-directive \"title\")</lisp></title>
    <link><lisp>(concat (muse-style-element :base-url)
                        (concat (muse-page-name)
                                muse-html-extension))</lisp></link>
    <description><lisp>(muse-publishing-directive \"desc\")</lisp></description>
    <language>en-us</language>
    <generator>Emacs Muse</generator>\n\n"
  "Header used for publishing RSS 2.0 files.  This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rss-footer
  "\n\n  </channel>
</rss>\n"
  "Footer used for publishing RSS 2.0 files.  This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rss-date-format
  "%a, %d %b %Y %H:%M:%S %Z"
  "Date format to use for RSS 2.0 entries."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rss-entry-template
  "\n    <item>
      <title>%title%</title>
      <link>%link%#%anchor%</link>
      <description>%desc%</description>
      <author><lisp>(muse-publishing-directive \"author\")</lisp></author>
      <pubDate>%date%</pubDate>
      <guid>%link%#%anchor%</guid>
      %enclosure%
    </item>\n"
  "Template used to publish individual journal entries as RSS 2.0.
This may be text or a filename."
  :type 'string
  :group 'muse-journal)

(defcustom muse-journal-rss-enclosure-types-alist
  '(("mp3" . "audio/mpeg"))
  "File types that are accepted as RSS enclosures.
This is an alist that maps file extension to content type.
Useful for podcasting."
  :type '(alist :key-type string :value-type string)
  :group 'muse-journal)

(defcustom muse-journal-rss-summarize-entries nil
  "If non-nil, include only summaries in the RSS file, not the full data.

The default is nil, because this annoys some subscribers."
  :type 'boolean
  :group 'muse-journal)

(defcustom muse-journal-rss-markup-regexps
  '((10000 muse-explicit-link-regexp 0 "\\2"))
  "List of markup rules for publishing a Muse journal page to RSS 2.0.
For more information on the structure of this list, see
`muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-journal)

(defcustom muse-journal-rss-markup-functions
  '((email . ignore)
    (link  . ignore)
    (url   . ignore))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-journal)

(defun muse-journal-anchorize-title (title)
  "This strips tags from TITLE, truncates TITLE at begin parenthesis,
and escapes any remaining non-alphanumeric characters."
  (save-match-data
    (if (string-match "(" title)
        (setq title (substring title 0 (match-beginning 0))))
    (if (string-match "<[^>]+>" title)
        (setq title (replace-match "" nil nil title)))
    (let (pos code len ch)
      (while (setq pos (string-match (concat "[^" muse-regexp-alnum "_]")
                                     title pos))
          (setq ch (aref title pos)
                code (format "%%%02X" (cond ((fboundp 'char-to-ucs)
                                             (char-to-ucs ch))
                                            ((fboundp 'char-to-int)
                                             (char-to-int ch))
                                            (t ch)))
                len (length code)
                title (concat (substring title 0 pos)
                              code
                              (when (< pos (length title))
                                (substring title (1+ pos) nil)))
                pos (+ len pos)))
        title)))

(defun muse-journal-sort-entries (&optional direction)
  (interactive "P")
  (sort-subr
   direction
   (function
    (lambda ()
      (if (re-search-forward "^\\* [0-9]+" nil t)
          (goto-char (match-beginning 0))
        (goto-char (point-max)))))
   (function
    (lambda ()
      (if (re-search-forward "^\\* [0-9]+" nil t)
          (goto-char (1- (match-beginning 0)))
        (goto-char (point-max)))))
   (function
    (lambda ()
      (forward-char 2)))
   (function
    (lambda ()
      (end-of-line)))))

(defun muse-journal-qotd-tag (beg end)
  (muse-publish-ensure-block beg end)
  (muse-insert-markup (muse-markup-text 'begin-quote))
  (muse-insert-markup (muse-markup-text 'begin-quote-item))
  (goto-char end)
  (muse-insert-markup (muse-markup-text 'end-quote-item))
  (muse-insert-markup (muse-markup-text 'end-quote)))

(defun muse-journal-html-munge-buffer ()
  (goto-char (point-min))
  (let ((heading-regexp muse-journal-html-heading-regexp)
        (inhibit-read-only t))
    (while (re-search-forward heading-regexp nil t)
      (let* ((date (match-string 1))
             (orig-date date)
             (title (match-string 2))
             (clean-title title)
             datestamp qotd text)
        (delete-region (match-beginning 0) (match-end 0))
        (if clean-title
            (save-match-data
              (while (string-match "\\(^<[^>]+>\\|<[^>]+>$\\)" clean-title)
                (setq clean-title (replace-match "" nil nil clean-title)))))
        (save-match-data
          (when (and date
                     (string-match
                      (concat "\\`\\([1-9][0-9][0-9][0-9]\\)[./]?"
                              "\\([0-1][0-9]\\)[./]?\\([0-3][0-9]\\)") date))
            (setq datestamp
                  (encode-time
                   0 0 0
                   (string-to-number (match-string 3 date))
                   (string-to-number (match-string 2 date))
                   (string-to-number (match-string 1 date))
                   nil)
                  date (concat (format-time-string
                                muse-journal-date-format datestamp)
                               (substring date (match-end 0))))))
        (save-restriction
          (narrow-to-region
           (point) (if (re-search-forward
                        (concat "\\(^<hr>$\\|"
                                heading-regexp "\\)") nil t)
                       (match-beginning 0)
                     (point-max)))
          (goto-char (point-max))
          (while (and (not (bobp))
                      (eq ?\  (char-syntax (char-before))))
            (delete-char -1))
          (goto-char (point-min))
          (while (and (not (eobp))
                      (eq ?\  (char-syntax (char-after))))
            (delete-char 1))
          (save-excursion
            (when (search-forward "<qotd>" nil t)
              (let ((tag-beg (match-beginning 0))
                    (beg (match-end 0))
                    end)
                (re-search-forward "</qotd>\n*")
                (setq end (point-marker))
                (save-restriction
                  (narrow-to-region beg (match-beginning 0))
                  (muse-publish-escape-specials (point-min) (point-max)
                                                nil 'document)
                  (setq qotd (buffer-substring-no-properties
                              (point-min) (point-max))))
                (delete-region tag-beg end)
                (set-marker end nil))))
          (setq text (buffer-string))
          (delete-region (point-min) (point-max))
          (let ((entry muse-journal-html-entry-template))
            (muse-insert-file-or-string entry)
            (muse-publish-mark-read-only (point-min) (point-max))
            (goto-char (point-min))
            (while (search-forward "%date%" nil t)
              (remove-text-properties (match-beginning 0) (match-end 0)
                                      '(read-only nil rear-nonsticky nil))
              (replace-match (or date "") nil t))
            (goto-char (point-min))
            (while (search-forward "%title%" nil t)
              (remove-text-properties (match-beginning 0) (match-end 0)
                                      '(read-only nil rear-nonsticky nil))
              (replace-match (or title "&nbsp;") nil t))
            (goto-char (point-min))
            (while (search-forward "%anchor%" nil t)
              (replace-match (muse-journal-anchorize-title
                              (or clean-title orig-date))
                             nil t))
            (goto-char (point-min))
            (while (search-forward "%qotd%" nil t)
              (save-restriction
                (narrow-to-region (match-beginning 0) (match-end 0))
                (delete-region (point-min) (point-max))
                (when qotd (muse-insert-markup qotd))))
            (goto-char (point-min))
            (while (search-forward "%text%" nil t)
              (remove-text-properties (match-beginning 0) (match-end 0)
                                      '(read-only nil rear-nonsticky nil))
              (replace-match text nil t))
            (when (null qotd)
              (goto-char (point-min))
              (when (search-forward "<div class=\"entry-qotd\">" nil t)
                (let ((beg (match-beginning 0)))
                  (re-search-forward "</div>\n*" nil t)
                  (delete-region beg (point))))))))))
  ;; indicate that we are to continue the :before-end processing
  nil)

(defun muse-journal-latex-munge-buffer ()
  (goto-char (point-min))
  (let ((heading-regexp
         (concat "^" (regexp-quote (muse-markup-text 'section))
                 muse-journal-heading-regexp
                 (regexp-quote (muse-markup-text 'section-end)) "$"))
        (inhibit-read-only t))
    (when (re-search-forward heading-regexp nil t)
      (goto-char (match-beginning 0))
      (sort-subr nil
                 (function
                  (lambda ()
                    (if (re-search-forward heading-regexp nil t)
                        (goto-char (match-beginning 0))
                      (goto-char (point-max)))))
                 (function
                  (lambda ()
                    (if (re-search-forward heading-regexp nil t)
                        (goto-char (1- (match-beginning 0)))
                      (goto-char (point-max)))))
                 (function
                  (lambda ()
                    (forward-char 2)))
                 (function
                  (lambda ()
                    (end-of-line)))))
    (while (re-search-forward heading-regexp nil t)
      (let ((date (match-string 1))
            (title (match-string 2))
            ;; FIXME: Nothing is done with qotd
            qotd section)
        (save-match-data
          (when (and date
                     (string-match
                      (concat "\\([1-9][0-9][0-9][0-9]\\)[./]?"
                              "\\([0-1][0-9]\\)[./]?\\([0-3][0-9]\\)") date))
            (setq date (encode-time
                        0 0 0
                        (string-to-number (match-string 3 date))
                        (string-to-number (match-string 2 date))
                        (string-to-number (match-string 1 date))
                        nil)
                  date (format-time-string
                        muse-journal-date-format date))))
        (save-restriction
          (narrow-to-region (match-beginning 0) (match-end 0))
          (delete-region (point-min) (point-max))
          (muse-insert-markup muse-journal-latex-section)
          (goto-char (point-min))
          (while (search-forward "%title%" nil t)
            (replace-match (or title "Untitled") nil t))
          (goto-char (point-min))
          (while (search-forward "%date%" nil t)
            (replace-match (or date "") nil t))))))
  (goto-char (point-min))
  (let ((subheading-regexp
         (concat "^" (regexp-quote (muse-markup-text 'subsection))
                 "\\([^\n}]+\\)"
                 (regexp-quote (muse-markup-text 'subsection-end)) "$"))
        (inhibit-read-only t))
    (while (re-search-forward subheading-regexp nil t)
      (let ((title (match-string 1)))
        (save-restriction
          (narrow-to-region (match-beginning 0) (match-end 0))
          (delete-region (point-min) (point-max))
          (muse-insert-markup muse-journal-latex-subsection)
          (goto-char (point-min))
          (while (search-forward "%title%" nil t)
            (replace-match title nil t))))))
  ;; indicate that we are to continue the :before-end processing
  nil)

(defun muse-journal-rss-munge-buffer ()
  (goto-char (point-min))
  (let ((heading-regexp muse-journal-rss-heading-regexp)
        (inhibit-read-only t))
    (while (re-search-forward heading-regexp nil t)
      (let* ((date (match-string 1))
             (orig-date date)
             (title (match-string 2))
             ;; FIXME: Nothing is done with qotd
             enclosure qotd desc)
        (if title
            (save-match-data
              (if (string-match muse-explicit-link-regexp title)
                  (setq enclosure (muse-get-link title)
                        title (muse-get-link-desc title)))))
        (save-match-data
          (when (and date
                     (string-match
                      (concat "\\([1-9][0-9][0-9][0-9]\\)[./]?"
                              "\\([0-1][0-9]\\)[./]?\\([0-3][0-9]\\)") date))
            (setq date (encode-time 0 0 0
                                    (string-to-number (match-string 3 date))
                                    (string-to-number (match-string 2 date))
                                    (string-to-number (match-string 1 date))
                                    nil)
                  ;; make sure that date is in a format that RSS
                  ;; readers can handle
                  date (let ((system-time-locale "C"))
                         (format-time-string
                          (muse-style-element :date-format) date)))))
        (save-restriction
          (narrow-to-region
           (match-beginning 0)
           (if (re-search-forward heading-regexp nil t)
               (match-beginning 0)
             (if (re-search-forward "^Footnotes:" nil t)
                 (match-beginning 0)
               (point-max))))
          (goto-char (point-min))
          (delete-region (point) (muse-line-end-position))
          (re-search-forward "</qotd>\n+" nil t)
          (while (and (char-after)
                      (eq ?\  (char-syntax (char-after))))
            (delete-char 1))
          (let ((beg (point)))
            (if (muse-style-element :summarize)
                (progn
                  (forward-sentence 2)
                  (setq desc (concat (buffer-substring beg (point)) "...")))
              (save-restriction
                (muse-publish-markup-buffer "rss-entry" "journal-rss-entry")
                (goto-char (point-min))
                (if (re-search-forward "Page published by Emacs Muse" nil t)
                    (goto-char (muse-line-end-position))
                  (muse-display-warning
                   (concat
                    "Cannot find 'Page published by Emacs Muse begins here'.\n"
                    "You will probably need this text in your header."))
                  (goto-char (point-min)))
                (setq beg (point))
                (if (re-search-forward "Page published by Emacs Muse" nil t)
                    (goto-char (muse-line-beginning-position))
                  (muse-display-warning
                   (concat
                    "Cannot find 'Page published by Emacs Muse ends here'.\n"
                    "You will probably need this text in your footer."))
                  (goto-char (point-max)))
                (setq desc (buffer-substring beg (point))))))
          (unless (string= desc "")
            (setq desc (concat "<![CDATA[" desc "]]>")))
          (delete-region (point-min) (point-max))
          (let ((entry (muse-style-element :entry-template)))
            (muse-insert-file-or-string entry)
            (goto-char (point-min))
            (while (search-forward "%date%" nil t)
              (replace-match (or date "") nil t))
            (goto-char (point-min))
            (while (search-forward "%title%" nil t)
              (replace-match "")
              (save-restriction
                (narrow-to-region (point) (point))
                (insert (or title "Untitled"))
                (remove-text-properties (match-beginning 0) (match-end 0)
                                        '(read-only nil rear-nonsticky nil))
                (let ((muse-publishing-current-style (muse-style "html")))
                  (muse-publish-escape-specials (point-min) (point-max)
                                                nil 'document))))
            (goto-char (point-min))
            (while (search-forward "%desc%" nil t)
              (replace-match desc nil t))
            (goto-char (point-min))
            (while (search-forward "%enclosure%" nil t)
              (replace-match
               (if (null enclosure)
                   ""
                 (save-match-data
                   (format
                    "<enclosure url=\"%s\" %stype=\"%s\"/>"
                    (if (string-match "//" enclosure)
                        enclosure
                      (concat (muse-style-element :base-url)
                              enclosure))
                    (let ((file
                           (expand-file-name enclosure
                                             (muse-style-element :path))))
                      (if (file-readable-p file)
                          (format "length=\"%d\" "
                                  (nth 7 (file-attributes file)))
                        ""))
                    (if (string-match "\\.\\([^.]+\\)$" enclosure)
                        (let* ((ext (match-string 1 enclosure))
                               (type
                                (assoc
                                 ext muse-journal-rss-enclosure-types-alist)))
                          (if type
                              (cdr type)
                            "application/octet-stream"))))))
               nil t))
            (goto-char (point-min))
            (while (search-forward "%link%" nil t)
              (replace-match
               (concat (muse-style-element :base-url)
                       (concat (muse-page-name)
                               muse-html-extension))
               nil t))
            (goto-char (point-min))
            (while (search-forward "%anchor%" nil t)
              (replace-match
               (muse-journal-anchorize-title (or title orig-date))
               nil t))
            (goto-char (point-min))
            (while (search-forward "%maintainer%" nil t)
              (replace-match
               (or (muse-style-element :maintainer)
                   (concat "webmaster@" (system-name)))
               nil t)))))))
  ;; indicate that we are to continue the :before-end processing
  nil)


;;; Register the Muse Journal Publishers

(muse-derive-style "journal-html" "html"
                   :before-end 'muse-journal-html-munge-buffer)

(muse-derive-style "journal-xhtml" "xhtml"
                   :before-end 'muse-journal-html-munge-buffer)

(muse-derive-style "journal-latex" "latex"
                   :tags 'muse-journal-markup-tags
                   :before-end 'muse-journal-latex-munge-buffer)

(muse-derive-style "journal-pdf" "pdf"
                   :tags 'muse-journal-markup-tags
                   :before-end 'muse-journal-latex-munge-buffer)

(muse-derive-style "journal-book-latex" "book-latex"
                   ;;:nochapters
                   :tags 'muse-journal-markup-tags
                   :before-end 'muse-journal-latex-munge-buffer)

(muse-derive-style "journal-book-pdf" "book-pdf"
                   ;;:nochapters
                   :tags 'muse-journal-markup-tags
                   :before-end 'muse-journal-latex-munge-buffer)

(muse-define-style "journal-rdf"
                   :suffix         'muse-journal-rdf-extension
                   :regexps        'muse-journal-rss-markup-regexps
                   :functions      'muse-journal-rss-markup-functions
                   :before         'muse-journal-rss-munge-buffer
                   :header         'muse-journal-rdf-header
                   :footer         'muse-journal-rdf-footer
                   :date-format    'muse-journal-rdf-date-format
                   :entry-template 'muse-journal-rdf-entry-template
                   :base-url       'muse-journal-rdf-base-url
                   :summarize      'muse-journal-rdf-summarize-entries)

(muse-define-style "journal-rss"
                   :suffix         'muse-journal-rss-extension
                   :regexps        'muse-journal-rss-markup-regexps
                   :functions      'muse-journal-rss-markup-functions
                   :before         'muse-journal-rss-munge-buffer
                   :header         'muse-journal-rss-header
                   :footer         'muse-journal-rss-footer
                   :date-format    'muse-journal-rss-date-format
                   :entry-template 'muse-journal-rss-entry-template
                   :base-url       'muse-journal-rss-base-url
                   :summarize      'muse-journal-rss-summarize-entries)

;; Used by `muse-journal-rss-munge-buffer' to mark up individual entries
(muse-derive-style "journal-rss-entry" "html"
                   :tags 'muse-journal-markup-tags)

(provide 'muse-journal)

;;; muse-journal.el ends here
