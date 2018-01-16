;;; sb-yoshirin.el --- shimbun backend for Yoshinori Kobayashi Official Site -*- coding: iso-2022-7bit; -*-

;; Copyright (C) 2015, 2016 Katsumi Yamaoka

;; Author: Katsumi Yamaoka <yamaoka@jpl.org>
;; Keywords: news

;; This file is a part of shimbun.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'shimbun)

(luna-define-class shimbun-yoshirin (shimbun-japanese-newspaper shimbun) ())

(defvar shimbun-yoshirin-top-level-domain "yoshinori-kobayashi.com")

(defvar shimbun-yoshirin-url
  (concat "http://" shimbun-yoshirin-top-level-domain "/"))

(defvar shimbun-yoshirin-server-name "小林よしのり公式サイト")

(defvar shimbun-yoshirin-group-table
  '(("blog" "BLOG" "http://yoshinori-kobayashi.com/category/blog/"
     "小林よしのり")
    ("topics" "TOPICS" "http://yoshinori-kobayashi.com/category/topics/"
     "よしりん企画")))

(defvar shimbun-yoshirin-index-range 20
  "*The number of indices that should be checked to detect new articles.
`all' or nil is for all indices, `last' is for the last index, and an
integer N is for the last N pages of indices.  This overrides any other
index-range setting if it is non-nil.

If you want to increase this value or change the value to nil or `all',
you will need to re-create the group(s) (delete the group(s) completely
in advance).  If you don't do so, you will never get old articles.")

(defvar shimbun-yoshirin-x-face-alist
  '(("default" . "X-Face: SX1=HV&[cI##/uM,,hed]\"a1.(e<M21Jl\
2dAy1-JnWwb'yT9t|fq*~ZpiUV%bx\\@&sdy`Vb\n c5[lT$}jl2|X~V97O'\
I31<&o-eCYZDs~WZVK{m,T}x>b3T9PCilX3;\"*8oF;QS\"GCHWit%'u!of`\
\\p\n &ute*s]IuWa5co-wMr4X1dQqqx/PB3y,@P3~Cdc<:$9.Jp^X$-*DPC")
    ("\\`topics\\'" . "\
Face: iVBORw0KGgoAAAANSUhEUgAAADAAAAAwAgMAAAAqbBEUAAAADFBMVEUAAAD///9fX1/d3d1
 VizmfAAAB0UlEQVQoz22SQWsTURSFz0yYxRiykqEgWehiuhHcpbhRIjiIYiGjczIz6UyaVrKIEmm
 RQCO0pAUR3SiWp26UgkYL3QnBlSBKF/6AURG0uNCFWxUqVPS+CG0W3tX7uOede97lgayaLwEYsyQ
 EoCuHIQT4VxqmR6GC/8HGKMBFNdoFG8nRXSggwKhsDxyEe5BhDjCztK7hHRpyfv+bC8NehPGHNa/
 FhihQNcNnRZkd6uCRUWvdX4PDMiwk9tKhOztwJYmF0DbjAxKFP2CApwxulXNc7OrHnjRD1UO/Vi/
 nwbOY74lTeO+2C3HJwdhCob1d0EHt3pGNBo4lYr1vB1jPf17AdgnR1w9mvsYZNuxNROWc93Tt4DL
 98RkkzTPWdXKSU/vPI/n20bv1Z91isiLgXLRkjlKBv6oXkvm/OrL/y6vgi+DJd+oKfFB9mn2cZfz
 CRy1UszhlXonugYeYpUVOqzZ/jpVwKRsralGTN4nN6l37Gj0x8Ih+EPMcfeoQcLqT5I2EiqcF4om
 OiiYyDqHytjnga4d8I3fiqfaJNFVkQdw6abce9RVDi7hyQecaSLQSkRTlED4nK0rWb6fSaZGv9Ke
 YO07Ok5GrIewNrrpcOiz9v8e9pILarDM0AAAAAElFTkSuQmCC")))

(defvar shimbun-yoshirin-expiration-days 1000)

(luna-define-method shimbun-groups ((shimbun shimbun-yoshirin))
  (mapcar 'car shimbun-yoshirin-group-table))

(luna-define-method shimbun-current-group-name ((shimbun shimbun-yoshirin))
  (nth 1 (assoc (shimbun-current-group-internal shimbun)
		shimbun-yoshirin-group-table)))

(luna-define-method shimbun-index-url ((shimbun shimbun-yoshirin))
  shimbun-yoshirin-url)

(luna-define-method shimbun-get-headers ((shimbun shimbun-yoshirin)
					 &optional range)
  (shimbun-yoshirin-get-headers shimbun
				(or shimbun-yoshirin-index-range range)))

(luna-define-method shimbun-make-contents :before ((shimbun shimbun-yoshirin)
						   header)
  (shimbun-yoshirin-make-contents shimbun header))

(luna-define-method shimbun-clear-contents :around ((shimbun shimbun-yoshirin)
						    header)
  t) ;; Force inserting footer.

(luna-define-method shimbun-footer :around ((shimbun shimbun-yoshirin)
					    header &optional html)
  (shimbun-yoshirin-footer shimbun header))
(defun shimbun-yoshirin-footer (shimbun header)
  (concat "<div align=\"left\">\n--&nbsp;<br>\n\
この記事の諸権利は"
	  (if (equal (shimbun-current-group-internal shimbun) "blog")
	      "小林よしのりさん"
	    "小林よしのりさん、またはよしりん企画")
	  "に帰属するはずです。<br>
原物は<a href=\""
	  (shimbun-article-base-url shimbun header)
	  "\"><u>ここ</u></a>で公開されています。\n</div>\n"))

(defvar shimbun-yoshirin-header-regexp
  (concat
   "<a\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n ]+href=\""
   ;; 1. url
   "\\([^\n\"]+/"
   ;; 2. serial
   "\\([0-9]+\\)"
   "/?\\)"
   "\"[^>]*>[\t\n\r ]*"
   ;; 3. year
   "\\(20[1-9][0-9]\\)"
   "\\."
   ;; 4. month
   "\\([01][0-9]\\)"
   "\\."
   ;; 5. day
   "\\([0-3][0-9]\\)"
   "[^\n]*<br />[\t\n\r ]*"
   ;; 6. subject
   "\\([^<]+\\)"
   "</a>"))

(defun shimbun-yoshirin-get-thumnail (limit)
  "Get a thumnail of the article in the area from LIMIT to the header."
  (save-excursion
    (and (re-search-backward "\
<div\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class=\"thumnail\"" limit t)
	 (shimbun-end-of-tag "div")
	 (save-restriction
	   (narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
	   (re-search-forward "<img[\t\n\r ]+[^>]+>" nil t))
	 (list (cons 'Thumnail
		     (base64-encode-string
		      (encode-coding-string (match-string 0) 'utf-8)
		      t))))))

(defun shimbun-yoshirin-get-headers-top (shimbun)
  "Get headers for the latest articles in the group of SHIMBUN."
  (let* ((group (shimbun-current-group-internal shimbun))
	 (from (nth 3 (assoc group shimbun-yoshirin-group-table)))
	 limit url serial year month day subject id headers)
    (when (and (re-search-forward
		(concat "\
<div\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class=\"top-"
			group "\"[^>]*>")
		nil t)
	       (shimbun-end-of-tag "div"))
      (save-restriction
	(narrow-to-region (goto-char (match-beginning 2)) (match-end 2))
	(setq limit (point))
	(while (re-search-forward shimbun-yoshirin-header-regexp nil t)
	  (setq url (match-string 1)
		serial (match-string 2)
		year (match-string 3)
		month (match-string 4)
		day (match-string 5)
		subject (match-string 6))
	  (setq id (concat "<" serial "." group "%"
			   shimbun-yoshirin-top-level-domain ">"))
	  (unless (shimbun-search-id shimbun id)
	    (push (shimbun-create-header
		   0 subject from
		   (shimbun-make-date-string (string-to-number year)
					     (string-to-number month)
					     (string-to-number day))
		   id "" 0 0 url
		   (shimbun-yoshirin-get-thumnail limit))
		  headers))
	  (setq limit (point)))))
    headers))

(defun shimbun-yoshirin-get-headers (shimbun range)
  "Get headers for articles in the group of SHIMBUN in RANGE."
  (let ((headers (shimbun-yoshirin-get-headers-top shimbun))
	(count (cond ((memq range '(0 nil all)) nil)
		     ((natnump range) range)
		     (t 1))))
    (when (and headers (or (not count) (> count 0)))
      (erase-buffer)
      (let* ((group (shimbun-current-group-internal shimbun))
	     (from (nth 3 (assoc group shimbun-yoshirin-group-table)))
	     limit url serial year month day subject id)
	(shimbun-retrieve-url
	 (nth 2 (assoc group shimbun-yoshirin-group-table)))
	(catch 'stop
	  (while t
	    (setq limit (point))
	    (while (re-search-forward shimbun-yoshirin-header-regexp nil t)
	      (setq url (match-string 1)
		    serial (match-string 2)
		    year (match-string 3)
		    month (match-string 4)
		    day (match-string 5)
		    subject (match-string 6))
	      (setq id (concat "<" serial "." group "%"
			       shimbun-yoshirin-top-level-domain ">"))
	      (when (shimbun-search-id shimbun id)
		(throw 'stop nil))
	      (push (shimbun-create-header
		     0 subject from
		     (shimbun-make-date-string (string-to-number year)
					       (string-to-number month)
					       (string-to-number day))
		     id "" 0 0 url
		     (shimbun-yoshirin-get-thumnail limit))
		    headers)
	      (setq limit (point)))
	    (when (and count (<= (setq count (1- count)) 0))
	      (throw 'stop nil))
	    (goto-char (point-min))
	    (when (and (or (re-search-forward "\
<div\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class='wp-pagenavi'" nil t)
			   (re-search-forward "\
<div\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class=\"pagination cf\"" nil t))
		       (shimbun-end-of-tag "div"))
	      (save-restriction
		(narrow-to-region (goto-char (match-beginning 2))
				  (match-end 2))
		(unless (re-search-forward "\
<span\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class='current'[^>]*>\
[\t\n\r ]*[0-9]+[\t\n\r ]*</span>[\t\n\r ]*\
<a\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+href=\"\\([^\"]+\\)"
					   nil t)
		  (throw 'stop nil)))
	      (shimbun-retrieve-url (prog1
					(match-string 1)
				      (erase-buffer))))))))
    headers))

(defun shimbun-yoshirin-make-contents (shimbun header)
  "Make an html article."
  (when (and (re-search-forward "\
<div\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class=\"entry\"" nil t)
	     (shimbun-end-of-tag "div"))
    (delete-region (match-end 2) (point-max))
    (delete-region (goto-char (point-min)) (match-beginning 2))
    (when (and (re-search-forward "\
<h3\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class=\"blog-ttl\"" nil t)
	       (shimbun-end-of-tag "h3"))
      (delete-region (point-min) (match-end 0))
      (when (looking-at "[\t\n\r ]*<p>&nbsp;</p>[\t\n\r ]*")
	(delete-region (point) (match-end 0)))
      (when (re-search-forward "\\(?:[\t\n\r ]*<p>&nbsp;</p>\\)*[\t\n\r ]*\
<div\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+class=\"post_facebook\"" nil t)
	(delete-region (match-beginning 0) (point-max))))
    (let ((thumnail (cdr (assq 'Thumnail (shimbun-header-extra header))))
	  (case-fold-search t)
	  src caption)
      (when (and thumnail
		 (progn
		   (setq thumnail (decode-coding-string
				   (base64-decode-string thumnail) 'utf-8))
		   (string-match "src=\"[^\"]+\"" thumnail))
		 (progn
		   (setq src (regexp-quote (match-string 0 thumnail)))
		   (goto-char (point-min))
		   (not (re-search-forward (concat "\
<img\\(?:[\t\n\r ]+[^\t\n\r >]+\\)*[\t\n\r ]+" src) nil t))))
	(when (string-match "[\t ]+alt=\"\\([^\"]+\\)\"" thumnail)
	  (setq caption (match-string 1 thumnail)
		thumnail (concat (substring thumnail 0 (match-beginning 0))
				 (substring thumnail (match-end 0))))
	  (when (string-match "\\`\\(?:%[0-9a-f][0-9a-f:]\\)+\\'" caption)
	    (setq caption (w3m-url-decode-string caption 'utf-8)))
	  (insert caption "<br>\n"))
	(insert thumnail "\n")))))

(provide 'sb-yoshirin)

;; sb-yoshirin.el ends here
