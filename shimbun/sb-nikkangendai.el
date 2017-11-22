;;; sb-nikkangendai.el --- shimbun backend for Nikkan Gendai -*- coding: utf-8; -*-

;; Copyright (C) 2015, 2016 Katsumi Yamaoka

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

;; Nikkan Gendai is an evening paper in Japan.

;;; Code:

(require 'shimbun)
(require 'sb-multi)

(luna-define-class shimbun-nikkangendai
		   (shimbun-japanese-newspaper shimbun-multi shimbun) ())

(defvar shimbun-nikkangendai-top-level-domain "www.nikkan-gendai.com"
  "Name of the top level domain for Nikkan Gendai.")

(defvar shimbun-nikkangendai-url
  (concat "http://" shimbun-nikkangendai-top-level-domain "/")
  "Name of the root url.")

(defvar shimbun-nikkangendai-server-name "日刊ゲンダイ")

(defvar shimbun-nikkangendai-group-table
  '(("top" "TOP")
    ("news" "ニュース")
    ("geino" "芸能")
    ("sports" "スポーツ")
    ("life" "ライフ")
    ("book" "BOOKS")
    ("gourmet" "グルメ")))

(defvar shimbun-nikkangendai-x-face-alist
  '(("default" . "\
Face: iVBORw0KGgoAAAANSUhEUgAAADAAAAAwAgMAAAAqbBEUAAAADFBMVEX////yo4H40cPrYQC
 60gGqAAABU0lEQVQoz5XSP07DMBQG8OdUKCodurBWniqiLjlCow4sLHAC2BjY2dCL4BCwQRkQt0i
 5QYREy9ZMzBmsNEJ1Pp7dqumEhKf89EXvj2XC3qF/wLZYIdf49LCjF9T98/IYYGp0yXXvzSjYzAG
 lOlkTGp8gD5eWYASjZxS65gA5qBmeYUakr/EO/1tK1Ac6HlZdHj6hCT3WYRkCeR+uQK3lA4n2ScF
 5jIpYxmFcYaZRBJupGcn4m3oOq0pyTigW/EwfuVHSl+EKRDI1CoUtCo0y9hhEt13AjB3mKrphlms
 w0nQ+jNjEOIWR2exAoOwUtRLoI14HixBl4GAkmSxRdB2+2Mimfmqrc9QHqSyTyWzsbjTVjVvBXWu
 RUVb7RE5iiYttYtUr4S7ZwMSJqh5mG3xwLmtuE2nYAkg7LRpSLWp13yKJFztUAWOHyQWwV82dfB/
 2r7fzC4CxojZUJhCfAAAAAElFTkSuQmCC")))

(defvar shimbun-nikkangendai-expiration-days nil)

(defvar shimbun-nikkangendai-japanese-hankaku t)

(luna-define-method shimbun-groups ((shimbun shimbun-nikkangendai))
  (mapcar 'car shimbun-nikkangendai-group-table))

(luna-define-method shimbun-current-group-name ((shimbun shimbun-nikkangendai))
  (nth 1 (assoc (shimbun-current-group-internal shimbun)
		shimbun-nikkangendai-group-table)))

(luna-define-method shimbun-index-url ((shimbun shimbun-nikkangendai))
  (let ((group (shimbun-current-group-internal shimbun))
	(base (shimbun-url-internal shimbun)))
    (if (string-equal group "top")
	base
      (shimbun-expand-url (concat "articles/index/" group) base))))

(luna-define-method shimbun-get-headers ((shimbun shimbun-nikkangendai)
					 &optional range)
  (if (string-equal (shimbun-current-group-internal shimbun) "top")
      (shimbun-nikkangendai-get-headers-top shimbun range)
    (shimbun-nikkangendai-get-headers shimbun range)))

(defun shimbun-nikkangendai-get-headers-top (shimbun range)
  (let ((base (shimbun-url-internal shimbun))
	year month day url group id subject from headers)
    (goto-char (point-min))
    (when (and
	   (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*class=\"article-wrap\"" nil t)
	   (shimbun-end-of-tag "div")
	   (progn
	     (narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
	     (re-search-forward "<time[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
datetime=\"\\(20[1-9][0-9]\\)-\\([01]?[0-9]\\)-\\([0-3]?[0-9]\\)\"" nil t)))
      (setq year (string-to-number (match-string 1))
	    month (string-to-number (match-string 2))
	    day (string-to-number (match-string 3)))

      ;; Main topic
      (when (and (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
class=\"main-topics[\t\n\r ]+clearfix\"" nil t)
		 (shimbun-end-of-tag "div"))
	(save-restriction
	  (narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
	  (when (and (re-search-forward "\
<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
href=\"\\(/articles/view/\\([^\t\n\r \"/>]+\\)/\\([0-9]+\\)\\)\"[^>]*>\
[\t\n\r ]*\\([^<]+\\)" nil t)
		     (progn
		       (setq url (shimbun-expand-url (match-string 1) base)
			     group (match-string 2)
			     id (concat "<" (match-string 3) ;; serial
					"." group "%"
					shimbun-nikkangendai-top-level-domain
					">")
			     subject (match-string 4))
		       (not (shimbun-search-id shimbun id))))
	    (setq from (concat shimbun-nikkangendai-server-name " ("
			       (or (cadr
				    (assoc group
					   shimbun-nikkangendai-group-table))
				   (cadr
				    (assoc (substring group 0 -1)
					   shimbun-nikkangendai-group-table))
				   group)
			       ")"))
	    (push (shimbun-create-header
		   0 subject from
		   (shimbun-make-date-string year month day)
		   id "" 0 0 url)
		  headers))
	  (goto-char (point-max))))

      ;; Topics
      (while (and (re-search-forward "\
<li[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*class=\"article-box\"" nil t)
		  (shimbun-end-of-tag "li"))
	(save-restriction
	  (narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
	  (when (and (re-search-forward "\
<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
href=\"\\(/articles/view/\\([^\t\n\r \"/>]+\\)/\\([0-9]+\\)\\)\"[^>]*>" nil t)
		     (progn
		       (setq url (shimbun-expand-url (match-string 1) base)
			     group (match-string 2)
			     id (concat "<" (match-string 3) ;; serial
					"." group "%"
					shimbun-nikkangendai-top-level-domain
					">"))
		       (not (shimbun-search-id shimbun id)))
		     (search-forward "<p>" nil t)
		     (shimbun-end-of-tag "p"))
	    (setq subject (match-string 2)
		  from (concat shimbun-nikkangendai-server-name " ("
			       (or (cadr
				    (assoc group
					   shimbun-nikkangendai-group-table))
				   (cadr
				    (assoc (substring group 0 -1)
					   shimbun-nikkangendai-group-table))
				   group)
			       ")"))
	    (push (shimbun-create-header
		   0 subject from
		   (shimbun-make-date-string year month day)
		   id "" 0 0 url)
		  headers))
	  (goto-char (point-max))))
      (widen)
      headers)))

(defun shimbun-nikkangendai-get-headers (shimbun range)
  (let ((base (shimbun-url-internal shimbun))
	url group id year month day subject from headers)
    (when (and (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
class=\"contents-wrapper[\t\n\r ]+clearfix\"" nil t)
	       (shimbun-end-of-tag "div"))
      (narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
      (while (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*class=\"category-title\"\
[^>]*>[\t\n\r ]*<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
href=\"\\([^\"]+\\)" nil t)
	(setq url (shimbun-expand-url (match-string 1) base))
	(with-temp-buffer
	  (shimbun-retrieve-url url)
	  (goto-char (point-min))
	  (while (and (re-search-forward "\
<li[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*class=\"article-box\"" nil t)
		      (shimbun-end-of-tag "li"))
	    (save-restriction
	      (narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
	      (when (and (re-search-forward "\
<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
href=\"\\(/articles/view/\\([^\t\n\r \"/>]+\\)/\\([0-9]+\\)\\)\"[^>]*>" nil t)
			 (progn
			   (setq url (shimbun-expand-url (match-string 1) base)
				 group (match-string 2)
				 id (concat
				     "<" (match-string 3) ;; serial
				     "." group "%"
				     shimbun-nikkangendai-top-level-domain
				     ">"))
			   (not (shimbun-search-id shimbun id)))
			 (progn
			   (goto-char (point-min))
			   (re-search-forward "\
<time[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
datetime=\"\\(20[1-9][0-9]\\)-\\([01]?[0-9]\\)-\\([0-3]?[0-9]\\)\"" nil t))
			 (progn
			   (setq year (string-to-number (match-string 1))
				 month (string-to-number (match-string 2))
				 day (string-to-number (match-string 3)))
			   (goto-char (point-min))
			   (re-search-forward "\
<span[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*class=\"entry-ttl\"" nil t))
			 (shimbun-end-of-tag "span"))
		(setq subject (match-string 2)
		      from (concat shimbun-nikkangendai-server-name " ("
				   (or (cadr
					(assoc
					 group
					 shimbun-nikkangendai-group-table))
				       (cadr
					(assoc
					 (substring group 0 -1)
					 shimbun-nikkangendai-group-table))
				       group)
				   ")"))
		(push (shimbun-create-header
		       0 subject from
		       (shimbun-make-date-string year month day)
		       id "" 0 0 url)
		      headers))
	      (goto-char (point-max))))))
      (goto-char (point-max)))
    headers))

(luna-define-method shimbun-multi-next-url ((shimbun shimbun-nikkangendai)
					    header url)
;;  (shimbun-nikkangendai-multi-next-url shimbun header url))
;;(defun shimbun-nikkangendai-multi-next-url (shimbun header url)
  (goto-char (point-min))
  (when (re-search-forward "<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
href=\"\\([^\"]+\\)\"[^>]*>[\t\n\r ]*次へ[\t\n\r ]*\
\\(?:<[^>]+>[\t\n\r ]*\\)?&gt;&gt;" nil t)
    (shimbun-expand-url (match-string 1) url)))

(luna-define-method shimbun-multi-clear-contents
  ((shimbun shimbun-nikkangendai) header has-previous-page has-next-page)
;;  (shimbun-nikkangendai-multi-clear-contents shimbun header
;;					     has-previous-page))
;;(defun shimbun-nikkangendai-multi-clear-contents (shimbun header
;;							  has-previous-page)
  (let (authinfo subttl)
    (unless has-previous-page
      (goto-char (point-min))
      (when (and (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
class=\"author-info-box[\t\n\r ]+clearfix" nil t)
		 (shimbun-end-of-tag "div"))
	(setq authinfo (match-string 0)))
      (goto-char (point-min))
      (when (and (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*class=\"column-name\"" nil t)
		 (shimbun-end-of-tag "div")
		 (progn
		   (goto-char (match-beginning 2))
		   (re-search-forward "\
<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*href=" (match-end 2) t))
		 (shimbun-end-of-tag "a"))
	(setq subttl (match-string 0))))
    (goto-char (point-min))
    (when (and (re-search-forward "\
<div[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
class=\"article-detail-box[\t\n\r ]+clearfix\"" nil t)
	       (shimbun-end-of-tag "div"))
      (delete-region (match-end 2) (point-max))
      (delete-region (goto-char (point-min)) (match-beginning 2))
      (when (and (re-search-forward "\
<p[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
class=\"full-text\"" nil t)
		 (shimbun-end-of-tag "p" t))
	(delete-region (match-end 3) (match-end 0))
	(insert "\n")
	(delete-region (goto-char (match-beginning 0)) (match-beginning 3))
	(insert "<br>\n"))
      (if has-previous-page
	  (progn
	    (goto-char (point-min))
	    (insert "&#012;\n"))
	(when subttl
	  (goto-char (point-min))
	  (insert subttl "<br><br>\n"))
	(when authinfo
	  (goto-char (point-min))
	  (insert authinfo "\n")))
      (goto-char (point-min))
      (while (re-search-forward "<img[\t\n\r ]+\\([^>]*\\)>" nil t)
	(insert "<br>\n")
	(goto-char (match-beginning 1))
	(if (re-search-forward "alt=\"\\([^\"]*\\)\"" (match-end 1) t)
	    (replace-match "alt=\"[写真]\"")
	  (goto-char (match-end 1))
	  (insert " alt=\"[写真]\"")))
      (unless (memq (shimbun-japanese-hankaku shimbun)
		    '(header subject nil))
	(shimbun-japanese-hankaku-buffer t))
      t)))

(luna-define-method shimbun-footer :around ((shimbun shimbun-nikkangendai)
					    header &optional html)
;;  (shimbun-nikkangendai-footer shimbun header))
;;(defun shimbun-nikkangendai-footer (shimbun header)
  (concat "<div align=\"left\">\n--&nbsp;<br>\n\
この記事の著作権は株式会社・日刊現代に帰属します。<br>\n原物は <a href=\""
	  (shimbun-article-base-url shimbun header)
	  "\">ここ</a> で公開されています。\n</div>\n"))

(provide 'sb-nikkangendai)

;;; sb-nikkangendai.el ends here
