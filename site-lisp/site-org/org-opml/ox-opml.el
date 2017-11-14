;;; ox-opml.el --- Export Org files to OPML

;; Copyright (C) 2014 Eric Davis

;; Author: Eric Davis <eric@davising.com>
;; Keywords: opml, xml

;; This file is not yet part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

(require 'ox)

(org-export-define-backend 'opml
  '((bold . org-opml-bold)
    (entity . org-opml-entity)
    (headline . org-opml-headline)
    (italic . org-opml-italic)
    (item . org-opml-item)
    (link . org-opml-link)
    (paragraph . org-opml-paragraph)
    (plain-list . (lambda (plain-list contents info) contents))
    (section . (lambda (section contents info) contents))
    (subscript . org-ascii-subscript)
    (superscript . org-ascii-superscript)
    (template . org-opml-template)
    (underline . org-opml-underline)
    ;; (center-block . org-ascii-center-block)
    ;; (clock . org-ascii-clock)
    ;; (code . org-ascii-code)
    ;; (comment . (lambda (&rest args) ""))
    ;; (comment-block . (lambda (&rest args) ""))
    ;; (drawer . org-ascii-drawer)
    ;; (dynamic-block . org-ascii-dynamic-block)
    ;; (example-block . org-ascii-example-block)
    ;; (export-block . org-ascii-export-block)
    ;; (export-snippet . org-ascii-export-snippet)
    ;; (fixed-width . org-ascii-fixed-width)
    ;; (footnote-reference . org-ascii-footnote-reference)
    ;; (horizontal-rule . org-ascii-horizontal-rule)
    ;; (inline-src-block . org-ascii-inline-src-block)
    ;; (inlinetask . org-ascii-inlinetask)
    ;; (inner-template . org-ascii-inner-template)
    ;; (keyword . org-ascii-keyword)
    ;; (latex-environment . org-ascii-latex-environment)
    ;; (latex-fragment . org-ascii-latex-fragment)
    ;; (line-break . org-ascii-line-break)
    ;; (plain-text . org-ascii-plain-text)
    ;; (planning . org-ascii-planning)
    ;; (quote-block . org-ascii-quote-block)
    ;; (quote-section . org-ascii-quote-section)
    ;; (radio-target . org-ascii-radio-target)
    ;; (special-block . org-ascii-special-block)
    ;; (src-block . org-ascii-src-block)
    ;; (statistics-cookie . org-ascii-statistics-cookie)
    ;; (strike-through . org-ascii-strike-through)
    ;; (table . org-ascii-table)
    ;; (table-cell . org-ascii-table-cell)
    ;; (table-row . org-ascii-table-row)
    ;; (target . org-ascii-target)
    ;; (timestamp . org-ascii-timestamp)
    ;; (verbatim . org-ascii-verbatim)
    ;; (verse-block . org-ascii-verse-block)
	)
  :options-alist '((:opml-link "OPML_LINK" nil nil t)
		   (:opml-owner-id "OPML_OWNER_ID" nil (if (boundp 'opml-owner-id) opml-owner-id nil) t))
  :menu-entry '(?m "Export to OPML"
		   (lambda (a s v b) (org-opml-export-to-opml a s v b)))
  :filters-alist '((:filter-final-output . org-opml-final-function)))

;;;###autoload
(defun org-opml-export-to-opml (&optional async subtreep visible-only body-only)
  (let ((file (org-export-output-file-name ".opml" subtreep)))
    (org-export-to-file 'opml file async subtreep visible-only body-only)))

(defun org-opml-entity (entity contents info)
  "Transcode an ENTITY object from Org to ASCII.
CONTENTS are the definition itself.  INFO is a plist holding
contextual information."
  (org-element-property
   (intern ":latex")
   entity))

(defun org-opml-build-attributes (headline)
  "Build a key=value string from all property nodes for a given headline."
  (let* ((pom (org-element-property :begin headline))
	 (properties (org-entry-properties pom))
	 (attributes (mapconcat (lambda (element)
				  (let ((key (car element))
					(value (cdr element))
					(case-fold-search nil))
				    (unless (string-match-p "\\`[A-Z]+\\'" key) ; skip all upcase keys
				      (format "%s=\"%s\"" key (clean-text value))))) properties " ")))
    attributes))

(defun org-opml-headline (headline contents info)
  (let ((text (clean-text (org-element-property :raw-value headline)))
	(attributes (org-opml-build-attributes headline))
	(contents (if (string= contents "\n") "" (or contents ""))))
    (format "<outline text='%s' structure=\"headline\" %s>%s</outline>" text attributes contents)))

(defun clean-text (str)
  "Remove problematic elements from STR.

1) Escape HTML entities (&, <, >, etc.)
2) Translate newlines into spaces
3) Remove any double spaces
4) Remove any trailing whitespace"
  (let* ((text (url-insert-entities-in-string str))
	 (text (replace-regexp-in-string "\n" " " text))
	 (text (replace-regexp-in-string "[']" "&apos;" text))
	 (text (replace-regexp-in-string "[ ][ ]+" " " text))
	 (text (replace-regexp-in-string " $" "" text)))
    text))

(defun org-opml-paragraph (paragraph contents info)
  (let* ((parent (org-element-type (org-export-get-parent paragraph)))
	 (text (clean-text contents)))
    ;; Only display paragraphs when not in a list item
    (unless (eq parent 'item)
      (format "<outline text='%s' structure=\"paragraph\"/>" text))))

(defun org-opml-item (item contents info)
  (let* ((p (car (org-element-contents item)))
  	 (elements (org-element-contents p))
  	 (text (mapconcat
  		(lambda (el)
  		  (cond ((stringp el) (clean-text el))
  			((equal (car el) 'link)
			 (let ((url (org-element-property :raw-link el))
			       (text (org-element-contents el)))
			   (clean-text (format "<a href=\"%s\">%s</a>" url (car text)))))
			((equal (car el) 'italic)
			 (format "/%s/" (car (org-element-contents el))))
			((equal (car el) 'bold)
			 (format "*%s*" (car (org-element-contents el))))
			((equal (car el) 'verbatim)
			 (format "=%s=" (org-element-property :value el)))))
		elements " ")))
    (format "<outline text='%s' structure='list'>%s</outline>" text contents)))

(defun org-opml-link (link contents info)
  (let ((url (org-element-property :raw-link link))
	(text (car (org-element-contents link))))
    (if text
	(format "[[%s][%s]]" url text)
      url)))

(defun org-opml-italic (italic contents info)
  (format "/%s/" contents))

(defun org-opml-bold (bold contents info)
  (format "*%s*" contents))

(defun org-opml-underline (underline contents info)
  (format "_%s_" contents))

(defun org-opml-add-header (key info &optional tag)
  (let ((tag (or tag (substring (symbol-name key) 1)))
	(value (plist-get info key)))
    (when value
      (format "<%s>%s</%s>" tag (if (listp value) (car value) value) tag))))

(defun org-opml-add-timestamp-headers ()
  (let* ((fmt "%a, %d %b %Y %H:%M:%S")
	 (attr (if (buffer-file-name) (file-attributes (buffer-file-name)) nil))
	 (modified (if attr (nth 5 attr) (current-time)))
	 (creation (current-time)))
    (concat
     (format "<dateModified>%s GMT</dateModified>" (format-time-string fmt modified t))
     (format "<dateCreated>%s GMT</dateCreated>" (format-time-string fmt creation t)))))

(defun org-opml-template (contents info)
  (concat
   "<?xml version='1.0'?>"
   (format "<!-- OPML generated by %s on %s GMT -->"
	   org-export-creator-string
	   (format-time-string "%a, %d %b %Y %H:%M:%S" (current-time) t))
   "<opml version='2.0'>"
   "<head>"
   (if (equal (plist-get info :title) " *Format Temp 0*")
       "<title>Untitled</title>"
     (org-opml-add-header :title info))
   (org-opml-add-header :description info)
   (org-opml-add-header :author info "ownerName")
   (org-opml-add-header :email info "ownerEmail")
   (org-opml-add-header :opml-owner-id info "ownerId")
   (org-opml-add-timestamp-headers)
   (org-opml-add-header :opml-link info "link")
   "<generator>https://github.com/edavis/org-opml</generator>"
   "<docs>http://dev.opml.org/spec2.html</docs>"
   "</head>"
   "<body>"
   contents
   "</body>"
   "</opml>"))

(defun org-opml-final-function (contents backend info)
  (with-temp-buffer
    (insert contents)
    (when (executable-find "xmllint")
      (shell-command-on-region (point-min) (point-max) "xmllint --format -" nil t))
    (buffer-substring-no-properties (point-min) (point-max))))

(provide 'ox-opml)
