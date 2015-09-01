;;; muse-xml-common.el --- common routines for XML-like publishing styles

;; Copyright (C) 2005, 2006, 2007, 2008, 2009, 2010
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
;; Muse XML Publishing - Common Elements
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)
(require 'muse-regexps)

(defcustom muse-xml-encoding-map
  '((iso-8859-1         . "iso-8859-1")
    (iso-2022-jp        . "iso-2022-jp")
    (utf-8              . "utf-8")
    (japanese-iso-8bit  . "euc-jp")
    (chinese-big5       . "big5")
    (mule-utf-8         . "utf-8")
    (chinese-iso-8bit   . "gb2312")
    (chinese-gbk        . "gbk"))
  "An alist mapping Emacs coding systems to appropriate XML charsets.
Use the base name of the coding system (i.e. without the -unix)."
  :type '(alist :key-type coding-system :value-type string)
  :group 'muse-xml)

(defun muse-xml-transform-content-type (content-type default)
  "Using `muse-xml-encoding-map', try and resolve an Emacs coding
system to an associated XML coding system.
If no match is found, the DEFAULT charset is used instead."
  (let ((match (and (fboundp 'coding-system-base)
                    (assoc (coding-system-base content-type)
                           muse-xml-encoding-map))))
    (if match
        (cdr match)
      default)))

(defcustom muse-xml-markup-specials
  '((?\" . "&quot;")
    (?\< . "&lt;")
    (?\> . "&gt;")
    (?\& . "&amp;"))
  "A table of characters which must be represented specially."
  :type '(alist :key-type character :value-type string)
  :group 'muse-xml)

(defcustom muse-xml-markup-specials-url-extra
  '((?\" . "&quot;")
    (?\< . "&lt;")
    (?\> . "&gt;")
    (?\& . "&amp;")
    (?\  . "%20")
    (?\n . "%0D%0A"))
  "A table of characters which must be represented specially.
These are extra characters that are escaped within URLs."
  :type '(alist :key-type character :value-type string)
  :group 'muse-xml)

(defun muse-xml-decide-specials (context)
  "Determine the specials to escape, depending on CONTEXT."
  (cond ((memq context '(email url image))
         'muse-xml-escape-url)
        ((eq context 'url-extra)
         muse-xml-markup-specials-url-extra)
        (t muse-xml-markup-specials)))

(defun muse-xml-escape-url (str)
  "Convert to character entities any non-alphanumeric characters
outside a few punctuation symbols, that risk being misinterpreted
if not escaped."
  (when str
    (setq str (muse-publish-escape-specials-in-string str 'url-extra))
    (let (pos code len ch)
      (save-match-data
        (while (setq pos (string-match (concat "[^-"
                                               muse-regexp-alnum
                                               "/:._=@\\?~#%\"\\+<>()&;]")
                                       str pos))
          (setq ch (aref str pos)
                code (concat "&#" (int-to-string
                                   (cond ((fboundp 'char-to-ucs)
                                          (char-to-ucs ch))
                                         ((fboundp 'char-to-int)
                                          (char-to-int ch))
                                         (t ch)))
                             ";")
                len (length code)
                str (concat (substring str 0 pos)
                            code
                            (when (< pos (length str))
                              (substring str (1+ pos) nil)))
                pos (+ len pos)))
        str))))

(defun muse-xml-markup-anchor ()
  (unless (get-text-property (match-end 1) 'muse-link)
    (let ((text (muse-markup-text 'anchor (match-string 2))))
      (save-match-data
        (skip-chars-forward (concat muse-regexp-blank "\n"))
        (when (looking-at (concat "<\\([^" muse-regexp-blank "/>\n]+\\)>"))
          (goto-char (match-end 0)))
        (muse-insert-markup text)))
    (match-string 1)))

(defun muse-xml-sort-table (table)
  "Sort the given table structure so that it validates properly."
  ;; Note that the decision matrix must have a nil diagonal, or else
  ;; elements with the same type will be reversed with respect to each
  ;; other.
  (let ((decisions '((nil nil nil)      ; body < header, body < footer
                     (t   nil t)        ; header stays where it is
                     (t   nil nil))))   ; footer < header
    (sort table #'(lambda (l r)
                    (and (integerp (car l)) (integerp (car r))
                         (nth (1- (car r))
                              (nth (1- (car l)) decisions)))))))

(defun muse-xml-markup-table (&optional attributes)
  "Publish the matched region into a table.
If a string ATTRIBUTES is given, pass it to the markup string begin-table."
  (let* ((table-info (muse-publish-table-fields (match-beginning 0)
                                                (match-end 0)))
         (row-len (car table-info))
         (supports-group (not (string= (muse-markup-text 'begin-table-group
                                                         row-len)
                                       "")))
         (field-list (muse-xml-sort-table (cdr table-info)))
         last-part)
    (when table-info
      (let ((beg (point)))
        (muse-publish-ensure-block beg))
      (muse-insert-markup (muse-markup-text 'begin-table (or attributes "")))
      (muse-insert-markup (muse-markup-text 'begin-table-group row-len))
      (dolist (fields field-list)
        (let* ((type (car fields))
               (part (cond ((eq type 'hline) nil)
                           ((= type 1) "tbody")
                           ((= type 2) "thead")
                           ((= type 3) "tfoot")))
               (col (cond ((eq type 'hline) nil)
                          ((= type 1) "td")
                          ((= type 2) "th")
                          ((= type 3) "td"))))
          (setq fields (cdr fields))
          (unless (and part last-part (string= part last-part))
            (when last-part
              (muse-insert-markup "  </" last-part ">\n")
              (when (eq type 'hline)
                ;; horizontal separators are represented by closing
                ;; the current table group and opening a new one
                (muse-insert-markup (muse-markup-text 'end-table-group))
                (muse-insert-markup (muse-markup-text 'begin-table-group
                                                      row-len))))
            (when part
              (muse-insert-markup "  <" part ">\n"))
            (setq last-part part))
          (unless (eq type 'hline)
            (muse-insert-markup (muse-markup-text 'begin-table-row))
            (dolist (field fields)
              (muse-insert-markup (muse-markup-text 'begin-table-entry  col))
              (insert field)
              (muse-insert-markup (muse-markup-text 'end-table-entry  col)))
            (muse-insert-markup (muse-markup-text 'end-table-row)))))
      (when last-part
        (muse-insert-markup "  </" last-part ">\n"))
      (muse-insert-markup (muse-markup-text 'end-table-group))
      (muse-insert-markup (muse-markup-text 'end-table))
      (insert ?\n))))

(defun muse-xml-prepare-buffer ()
  (set (make-local-variable 'muse-publish-url-transforms)
       (cons 'muse-xml-escape-string muse-publish-url-transforms)))

(provide 'muse-xml-common)

;;; muse-xml-common.el ends here
