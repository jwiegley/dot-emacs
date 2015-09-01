;;; muse-regexps.el --- define regexps used by Muse

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

;; This file is the part of the Muse project that describes regexps
;; that are used throughout the project.

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Regular Expressions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgroup muse-regexp nil
  "Regular expressions used in publishing and syntax highlighting."
  :group 'muse)

;;; Deal with the lack of character classes for regexps in Emacs21 and
;;; XEmacs

(defcustom muse-regexp-use-character-classes 'undecided
  "Indicate whether to use extended character classes like [:space:].
If 'undecided, Muse will use them if your emacs is known to support them.

Emacs 22 and Emacs 21.3.50 are known to support them.  XEmacs
does not support them.

Emacs 21.2 or higher support them, but with enough annoying edge
cases that the sanest default is to leave them disabled."
  :type '(choice (const :tag "Yes" t)
                 (const :tag "No" nil)
                 (const :tag "Let Muse decide" undecided))
  :group 'muse-regexp)

(defvar muse-regexp-emacs-revision
  (save-match-data
    (and (string-match "^[0-9]+\\.[0-9]+\\.\\([0-9]+\\)"
                       emacs-version)
         (match-string 1 emacs-version)
         (string-to-number (match-string 1 emacs-version))))
  "The revision number of this version of Emacs.")

(defun muse-extreg-usable-p ()
  "Return non-nil if extended character classes can be used,
nil otherwise.

This is used when deciding the initial values of the muse-regexp
options."
  (cond
   ((eq muse-regexp-use-character-classes t)
    t)
   ((eq muse-regexp-use-character-classes nil)
    nil)
   ((featurep 'xemacs) nil)             ; unusable on XEmacs
   ((> emacs-major-version 21) t)       ; usable if > 21
   ((< emacs-major-version 21) nil)
   ((< emacs-minor-version 3) nil)
   ;; don't use if version is of format 21.x
   ((null muse-regexp-emacs-revision) nil)
   ;; only trust 21.3.50 or higher
   ((>= muse-regexp-emacs-revision 50) t)
   (t nil)))

(defcustom muse-regexp-blank
  (if (muse-extreg-usable-p)
      "[:blank:]"
    " \t")
  "Regexp to use in place of \"[:blank:]\".
This should be something that matches spaces and tabs.

It is like a regexp, but should be embeddable inside brackets.
Muse will detect the appropriate value correctly most of
the time."
  :type 'string
  :options '("[:blank:]" " \t")
  :group 'muse-regexp)

(defcustom muse-regexp-alnum
  (if (muse-extreg-usable-p)
      "[:alnum:]"
    "A-Za-z0-9")
  "Regexp to use in place of \"[:alnum:]\".
This should be something that matches all letters and numbers.

It is like a regexp, but should be embeddable inside brackets.
muse will detect the appropriate value correctly most of
the time."
  :type 'string
  :options '("[:alnum:]" "A-Za-z0-9")
  :group 'muse-regexp)

(defcustom muse-regexp-lower
  (if (muse-extreg-usable-p)
      "[:lower:]"
    "a-z")
  "Regexp to use in place of \"[:lower:]\".
This should match all lowercase characters.

It is like a regexp, but should be embeddable inside brackets.
muse will detect the appropriate value correctly most of
the time."
  :type 'string
  :options '("[:lower:]" "a-z")
  :group 'muse-regexp)

(defcustom muse-regexp-upper
  (if (muse-extreg-usable-p)
      "[:upper:]"
    "A-Z")
  "Regexp to use in place of \"[:upper:]\".
This should match all uppercase characters.

It is like a regexp, but should be embeddable inside brackets.
muse will detect the appropriate value correctly most of
the time."
  :type 'string
  :options '("[:upper:]" "A-Z")
  :group 'muse-regexp)

;;; Regexps used to define Muse publishing syntax

(defcustom muse-list-item-regexp
  (concat "^%s\\(\\([^\n" muse-regexp-blank "].*?\\)?::"
          "\\(?:[" muse-regexp-blank "]+\\|$\\)"
          "\\|[" muse-regexp-blank "]-[" muse-regexp-blank "]*"
          "\\|[" muse-regexp-blank "][0-9]+\\.[" muse-regexp-blank "]*\\)")
  "Regexp used to match the beginning of a list item.
The '%s' will be replaced with a whitespace regexp when publishing."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-ol-item-regexp (concat "\\`[" muse-regexp-blank "]+[0-9]+\\.")
  "Regexp used to match an ordered list item."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-ul-item-regexp (concat "\\`[" muse-regexp-blank "]+-")
  "Regexp used to match an unordered list item."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-dl-term-regexp
  (concat "[" muse-regexp-blank "]*\\(.+?\\)["
          muse-regexp-blank "]+::\\(?:[" muse-regexp-blank "]+\\|$\\)")
  "Regexp used to match a definition list term.
The first match string must contain the term."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-dl-entry-regexp (concat "\\`[" muse-regexp-blank "]*::")
  "Regexp used to match a definition list entry."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-table-field-regexp
  (concat "[" muse-regexp-blank "]+\\(|+\\)\\(?:["
          muse-regexp-blank "]\\|$\\)")
  "Regexp used to match table separators when publishing."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-table-line-regexp (concat ".*" muse-table-field-regexp ".*")
  "Regexp used to match a table line when publishing."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-table-hline-regexp (concat "[" muse-regexp-blank
                                           "]*|[-+]+|[" muse-regexp-blank
                                           "]*")
  "Regexp used to match a horizontal separator line in a table."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-table-el-border-regexp (concat "[" muse-regexp-blank "]*"
                                               "\\+\\(-*\\+\\)+"
                                               "[" muse-regexp-blank "]*")
  "Regexp used to match the beginning and end of a table.el-style table."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-table-el-line-regexp (concat "[" muse-regexp-blank "]*"
                                             "|\\(.*|\\)*"
                                           "[" muse-regexp-blank "]*")
  "Regexp used to match a table line of a table.el-style table."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-tag-regexp
  (concat "<\\([^/" muse-regexp-blank "\n][^" muse-regexp-blank
          "</>\n]*\\)\\(\\s-+[^<>]+[^</>\n]\\)?\\(/\\)?>")
  "A regexp used to find XML-style tags within a buffer when publishing.
Group 1 should be the tag name, group 2 the properties, and group
3 the optional immediate ending slash."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-explicit-link-regexp
  "\\[\\[\\([^][\n]+\\)\\]\\(?:\\[\\([^][\n]+\\)\\]\\)?\\]"
  "Regexp used to match [[target][description]] links.
Paren group 1 must match the URL, and paren group 2 the description."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-implicit-link-regexp
  (concat "\\([^" muse-regexp-blank "\n]+\\)")
  "Regexp used to match an implicit link.
An implicit link is the largest block of text to be checked for
URLs and bare WikiNames by the `muse-link-at-point' function.
Paren group 1 is the text to be checked.

URLs are checked by default.  To get WikiNames, load
muse-wiki.el.

This is only used when you are using muse-mode.el, but not
muse-colors.el.

If the above applies, and you want to match things with spaces in
them, you will have to modify this."
  :type 'regexp
  :group 'muse-regexp)

;;; Regexps used to determine file types

(defcustom muse-file-regexp
  (concat "\\`[~/]\\|\\?\\|/\\'\\|\\."
          "\\(html?\\|pdf\\|mp3\\|el\\|zip\\|txt\\|tar\\)"
          "\\(\\.\\(gz\\|bz2\\)\\)?\\'")
  "A link matching this regexp will be regarded as a link to a file."
  :type 'regexp
  :group 'muse-regexp)

(defcustom muse-image-regexp
  "\\.\\(eps\\|gif\\|jp\\(e?g\\)\\|p\\(bm\\|ng\\)\\|tiff\\|x\\([bp]m\\)\\)\\'"
  "A link matching this regexp will be published inline as an image.
For example:

  [[./wife.jpg][A picture of my wife]]

If you omit the description, the alt tag of the resulting HTML
buffer will be the name of the file."
  :type 'regexp
  :group 'muse-regexp)

(provide 'muse-regexps)

;;; muse-regexps.el ends here
