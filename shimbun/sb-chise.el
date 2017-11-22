;;; sb-chise.el --- shimbun backend for chise.org

;; Copyright (C) 2012 Katsumi Yamaoka

;; Author: Katsumi Yamaoka <yamaoka@jpl.org>
;; Keywords: news

;; This file is a part of shimbun.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Code:

(eval-when-compile (require 'cl))
(require 'shimbun)
(require 'sb-mailman)

(luna-define-class shimbun-chise (shimbun-mailman) ())

(defvar shimbun-chise-url "http://lists.chise.org/pipermail/")

;; Note: each group includes -en and -ja.
(defvar shimbun-chise-groups '("apel" "emacs-mime" "chise"))

;; Overrides the default index-range value if it is non-nil.
(defvar shimbun-chise-index-range 'all)

(luna-define-method shimbun-index-url ((shimbun shimbun-chise))
  (shimbun-expand-url
   (concat (shimbun-current-group-internal shimbun) "/")
   (shimbun-url-internal shimbun)))

(luna-define-method shimbun-headers ((shimbun shimbun-chise) &optional range)
  (let ((headers
	 (let ((oindex (directory-file-name (shimbun-index-url shimbun)))
	       (ssi (symbol-function 'shimbun-search-id))
	       (range (or shimbun-chise-index-range range)))
	   (nconc
	    (shimbun-flet
	     ((shimbun-index-url (shimbun) (concat oindex "-en/"))
	      (shimbun-search-id
	       (shimbun id)
	       (funcall ssi shimbun
			(save-match-data
			  (string-match "@" id)
			  (concat (substring id 0 (match-beginning 0))
				  "-en"
				  (substring id (match-beginning 0)))))))
	     (shimbun-mailman-headers shimbun range))
	    (shimbun-flet
	     ((shimbun-index-url (shimbun) (concat oindex "-ja/"))
	      (shimbun-search-id
	       (shimbun id)
	       (funcall ssi shimbun
			(save-match-data
			  (string-match "@" id)
			  (concat (substring id 0 (match-beginning 0))
				  "-ja"
				  (substring id (match-beginning 0)))))))
	     (shimbun-mailman-headers shimbun range)))))
	xref lang month id)
    (dolist (header headers (shimbun-sort-headers headers))
      (setq xref (shimbun-header-xref header))
      (when (string-match "\
\\(-en\\|-ja\\)/\\([0-9][0-9][0-9][0-9]\\)-\\([^/]+\\)/[^/]+\\'" xref)
	(setq lang (match-string 1 xref)
	      month
	      (cdr
	       (assoc
		(match-string 3 xref)
		'(("January" . 1) ("February" . 2) ("March" . 3)
		  ("April" . 4) ("May" . 5) ("June" . 6)
		  ("July" . 7) ("August" . 8) ("September" . 9)
		  ("October" . 10) ("November" . 11) ("December" . 12)))))
	(when month
	  (shimbun-header-set-date
	   header
	   (shimbun-make-date-string (string-to-number (match-string 2 xref))
				     month 1))))
      (string-match "@" (setq id (shimbun-header-id header)))
      (shimbun-header-set-id header
			     (concat (substring id 0 (match-beginning 0)) lang
				     (substring id (match-beginning 0)))))))

(luna-define-method shimbun-make-contents ((shimbun shimbun-chise) header)
  (if (string-match "-ja/[0-9]+-[^/]+/[^/]+\\'" (shimbun-header-xref header))
      (shimbun-mailman-ja-make-contents shimbun header)
    (shimbun-mailman-make-contents shimbun header)))

(provide 'sb-chise)

;;; sb-chise.el ends here
