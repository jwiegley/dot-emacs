;; rs-gnus-summary.el -- Auxiliary summary mode commands for Gnus
;; $Id: rs-gnus-summary.el,v 1.29 2007/10/20 15:00:06 ste Exp $

;; Author: Reiner Steib <Reiner.Steib@gmx.de>
;; Keywords: news
;; X-URL: http://theotp1.physik.uni-ulm.de/~ste/comp/emacs/gnus/rs-gnus-summary.el

;;; This program is free software; you can redistribute it and/or modify
;;; it under the terms of the GNU General Public License as published by
;;; the Free Software Foundation; either version 2 of the License, or
;;; (at your option) any later version.
;;;
;;; This program is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.
;;;
;;; You should have received a copy of the GNU General Public License
;;; along with this program; if not, write to the Free Software
;;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; Some additional summary mode commands for Gnus

;;; Installation:

;; Put this file in a directory that's in your `load-path',
;; e.g. ~/lisp:
;;   (add-to-list 'load-path "~/lisp")
;; and load it with
;;   (require 'rs-gnus-summary)

;; Usage:

;; Setup all:
;; (rs-gnus-summary-line-initialize)

;; Usage for the format functions:

;; ;; Alias for the content-type function:
;; (defalias 'gnus-user-format-function-ct 'rs-gnus-summary-line-content-type)
;; ;; Alias for the size function:
;; (defalias 'gnus-user-format-function-size 'rs-gnus-summary-line-message-size)
;; Usage for the summary tree functions:

;; (rs-gnus-summary-tree-arrows-rs)

;; Usage for the balloon face:

;; (setq gnus-balloon-face-0 'rs-gnus-balloon-0)
;; (setq gnus-balloon-face-1 'rs-gnus-balloon-1)

;;; Code:

(eval-when-compile
  (require 'nnheader))

;;;###autoload
(defun rs-gnus-summary-tree-arrows-ascii-default ()
  "Use default tree layout with ascii arrows."
  ;; See `gnus-sum.el'.  Useful for restoring defaults.
  (interactive)
  (setq
   ;; Defaults from `gnus-sum.el'
   gnus-sum-thread-tree-false-root      "> "
   gnus-sum-thread-tree-single-indent   ""
   gnus-sum-thread-tree-root            "> "
   gnus-sum-thread-tree-vertical        "| "
   gnus-sum-thread-tree-leaf-with-other "+-> "
   gnus-sum-thread-tree-single-leaf "  \\-> "
   gnus-sum-thread-tree-indent          "  ")
  (gnus-message 5 "Using default ascii tree layout."))

;;;###autoload
(defun rs-gnus-summary-tree-arrows-ascii ()
  "Use tree layout with ascii arrows."
  ;; Slighlty modified from default values.
  (interactive)
  (setq
   gnus-sum-thread-tree-false-root      "+ "
   gnus-sum-thread-tree-single-indent   ""
   gnus-sum-thread-tree-root            "> "
   gnus-sum-thread-tree-vertical        "| "
   gnus-sum-thread-tree-leaf-with-other "+-> "
   gnus-sum-thread-tree-single-leaf    "\\-> " ;; "\\" is _one_ char
   gnus-sum-thread-tree-indent          "  ")
  (gnus-message 5 "Using ascii tree layout."))

;;;###autoload
(defun rs-gnus-summary-tree-arrows-latin ()
  "Use default tree layout with ascii arrows (RS)."
  (interactive)
  (setq ;; ×
   gnus-sum-thread-tree-false-root      "÷» "
   gnus-sum-thread-tree-single-indent   "== "
   gnus-sum-thread-tree-root            "×» "
   gnus-sum-thread-tree-vertical        "|"
   gnus-sum-thread-tree-leaf-with-other "+-> "
   gnus-sum-thread-tree-single-leaf    "\\-> " ;; "\\" is _one_ char
   gnus-sum-thread-tree-indent          " ")
  (gnus-message 5 "Using tree layout with latin chars."))

;;;###autoload
(defalias 'rs-gnus-summary-tree-arrows 'rs-gnus-summary-tree-arrows-wide)

;;;###autoload
(defun rs-gnus-summary-tree-arrows-wide ()
  "Use tree layout with wide unicode arrows."
  (interactive)
  (setq
   gnus-sum-thread-tree-false-root      "┈┬──▷ "
   gnus-sum-thread-tree-single-indent   " ●  "
   gnus-sum-thread-tree-root            "┌─▶ "
   gnus-sum-thread-tree-vertical        "│"
   gnus-sum-thread-tree-leaf-with-other "├┬─► "
   gnus-sum-thread-tree-single-leaf     "╰┬─► "
   gnus-sum-thread-tree-indent          " ")
  (gnus-message 5 "Using tree layout with wide unicode arrows."))

;;;###autoload
(defun rs-gnus-summary-tree-arrows-test ()
  "Use tree layout with unicode arrows."
  (interactive)
  (setq
   gnus-sum-thread-tree-false-root      " ╤═▷ "
   gnus-sum-thread-tree-single-indent   "●  " ;; " ▷ "
   gnus-sum-thread-tree-root            "┌▶ "
   gnus-sum-thread-tree-vertical        "│"
   gnus-sum-thread-tree-leaf-with-other "├┬► "
   gnus-sum-thread-tree-single-leaf     "╰─► "
   gnus-sum-thread-tree-indent          " ")
  (gnus-message 5 "Using tree layout with unicode arrows."))

;;;###autoload
(defun rs-gnus-summary-tree-arrows-01 ()
  "Use tree layout with unicode arrows."
  ;; Suggested by Reiner Steib
  ;;  <v91xsxfbht.fsf@marauder.physik.uni-ulm.de>
  (interactive)
  (setq
   gnus-sum-thread-tree-false-root      "┌▷ "
   gnus-sum-thread-tree-single-indent   " ▷ "
   gnus-sum-thread-tree-root            "┌┬▶ "
   gnus-sum-thread-tree-vertical        "│"
   gnus-sum-thread-tree-leaf-with-other "├┬► "
   gnus-sum-thread-tree-single-leaf     "╰┬► "
   gnus-sum-thread-tree-indent          " ")
  (gnus-message 5 "Using tree layout with arrows."))

;;;###autoload
(defun rs-gnus-summary-tree-lines-rs ()
  "Use tree layout with unicode lines."
  ;; Suggested by Reiner Steib
  (interactive)
  (setq
   ;; gnus-summary-line-format "%«%U%R%z%u&ct; %4k: %B%»%(%-20,20f%) %s\n"
   ;; gnus-sum-thread-tree-false-root      "  "
   gnus-sum-thread-tree-single-indent   " "
   gnus-sum-thread-tree-root            "┌"
   gnus-sum-thread-tree-vertical        "│"
   gnus-sum-thread-tree-leaf-with-other "├╮ "
   gnus-sum-thread-tree-single-leaf     "╰─╮")
  (gnus-message 5 "Using tree layout with unicode arrows."))

;;;###autoload
(defun rs-gnus-summary-tree-arrows-mt ()
  "Use tree layout with unicode arrows."
  ;; Suggested by Mark Trettin in
  ;; <news:dcsg.m3isqr7ppc.fsf@beldin.mt743742.dialup.rwth-aachen.de>
   ;; gnus-summary-line-format "%U%R%z %B%-23,23n %s\n"
  (interactive)
  (setq
   gnus-sum-thread-tree-false-root      "  "
   gnus-sum-thread-tree-single-indent   " ▷"
   gnus-sum-thread-tree-root            "┌▶"
   gnus-sum-thread-tree-vertical        "│"
   gnus-sum-thread-tree-leaf-with-other "├┬►"
   gnus-sum-thread-tree-single-leaf     "╰─►"
   gnus-sum-thread-tree-indent          "  ")
  (gnus-message 5 "Using tree layout with unicode arrows."))

;;;###autoload
(defun rs-gnus-summary-tree-lines ()
  "Use tree layout with unicode lines."
  ;; Suggested by Jesper Harder in <news:m3ptvieklv.fsf@defun.localdomain>"
  (interactive)
  (setq
   ;; gnus-sum-thread-tree-false-root      "> "
   gnus-sum-thread-tree-single-indent   ""
   gnus-sum-thread-tree-root            ""
   gnus-sum-thread-tree-vertical        "│"
   gnus-sum-thread-tree-leaf-with-other "├╮ "
   gnus-sum-thread-tree-single-leaf     "╰─╮ ")
  (gnus-message 5 "Using tree layout with unicode lines."))

;;;###autoload
(defcustom rs-gnus-summary-line-content-type-alist
  '(("^text/plain"             " ")
    ("^text/html"              "h")
    ("^message/rfc822"         "f") ;; forwarded
    ("^multipart/mixed"        "m")
    ("^multipart/alternative"  "a")
    ("^multipart/related"      "r")
    ("^multipart/signed"       "s")
    ("^multipart/encrypted"    "e")
    ("^multipart/report"       "t")
    ("^application/"           "A")
    ("^image/"                 "I"))
  "Alist of regular expressions and summary line indicators."
  :group 'gnus-summary-format
  :type '(repeat (list (regexp :tag "Regexp")
		       (string :tag "Indicator"))))

;;;###autoload
(defun rs-gnus-summary-line-content-type (header)
  "Display content type of message in summary line.

This function is intended to be used in `gnus-summary-line-format-alist', with
\(defalias 'gnus-user-format-function-X 'rs-gnus-summary-line-content-type).
See (info \"(gnus)Group Line Specification\").

You need to add `Content-Type' to `nnmail-extra-headers' and
`gnus-extra-headers', see Info node `(gnus)To From Newsgroups'."
  (let ((case-fold-search t)
	(ctype (or (cdr (assq 'Content-Type (mail-header-extra header)))
		   "text/plain"))
	indicator)
    (mapc (lambda (el)
	    (when (string-match (car el) ctype)
	      (setq indicator (cadr el))))
	  rs-gnus-summary-line-content-type-alist)
    (if indicator
	indicator
      "o")))

;;;###autoload
(defun rs-gnus-summary-line-message-size (head)
  "Return pretty-printed version of message size.

Like `gnus-summary-line-message-size' but more verbose.  This function is
intended to be used in `gnus-summary-line-format-alist', with
\(defalias 'gnus-user-format-function-X 'rs-gnus-summary-line-message-size).

See (info \"(gnus)Group Line Specification\")."
  (let ((c (or (mail-header-chars head) -1)))
    (gnus-message 9 "c=%s chars in article %s" c (mail-header-number head))
    (cond ((< c 0) "n/a") ;; chars not available
	  ((< c (* 1000))       (format "%db"  c))
	  ((< c (* 1000 10))    (format "%1.1fk" (/ c 1024.0)))
	  ((< c (* 1000 1000))  (format "%dk" (/ c 1024.0)))
	  ((< c (* 1000 10000)) (format "%1.1fM" (/ c (* 1024.0 1024))))
	  (t (format "%dM" (/ c (* 1024.0 1024)))))))

;;;###autoload
(defun rs-gnus-summary-line-score (head)
  "Return pretty-printed version of article score.

See (info \"(gnus)Group Line Specification\")."
  (let ((c (gnus-summary-article-score (mail-header-number head))))
    ;; (gnus-message 9 "c=%s chars in article %s" c (mail-header-number head))
    (cond ((< c -1000)     "vv")
	  ((< c  -100)     " v")
	  ((< c   -10)     "--")
	  ((< c     0)     " -")
	  ((= c     0)     "  ")
	  ((< c    10)     " +")
	  ((< c   100)     "++")
	  ((< c  1000)     " ^")
	  (t               "^^"))))

(defcustom rs-gnus-summary-line-label-alist
  '(("Important" "Im")
    ("Work" "Wo")
    ("Personal" "Pe")
    ("To do" "TD")
    ("Later" "La")
    ("Need reply" "NR"))
  "Alist of regular expressions and summary line indicators."
  :group 'gnus-summary-format
  :type '(repeat (list (regexp :tag "Regexp")
		       (string :tag "Indicator"))))

;; http://www.fas.harvard.edu/computing/kb/kb1059.html
;; http://ilias.ca/blog/2005/09/gmail-labels-in-thunderbird.html
;; http://thread.gmane.org/m2n05mr2iv.fsf%40catbert.dok.org

;;;###autoload
(defun rs-gnus-summary-line-label (header)
  "Display label of message in summary line.

This function is intended to be used in `gnus-summary-line-format-alist', with
\(defalias 'gnus-user-format-function-X 'rs-gnus-summary-line-label).
See (info \"(gnus)Group Line Specification\").

You need to add `X-Gnus-Label' to `nnmail-extra-headers' and
`gnus-extra-headers', see Info node `(gnus)To From Newsgroups'."
  (let ((case-fold-search t)
	(label (or (cdr (assq 'X-Gnus-Label (mail-header-extra header)))
		   ""))
	indicator)
    (mapc (lambda (el)
	    (when (string-match (car el) label)
	      (setq indicator (cadr el))))
	  rs-gnus-summary-line-label-alist)
    (if indicator
	indicator
      label)))

;;;###autoload
(defun rs-gnus-summary-limit-to-label (regexp &optional not-matching)
  "Limit the summary buffer to articles that match a label."
  (interactive
   (list (read-string
	  (format "%s label (regexp): "
		  (if current-prefix-arg "Exclude" "Limit to")))
	 current-prefix-arg))
  (gnus-summary-limit-to-extra 'X-Gnus-Label regexp not-matching))

;;;###autoload
(defun rs-gnus-summary-line-list-subject (head)
  "Return modified subject for mailing lists.

This function is intended to be used in `gnus-summary-line-format-alist', with
\(defalias 'gnus-user-format-function-X 'rs-gnus-summary-line-list-subject).

See (info \"(gnus)Group Line Specification\")."
  (let ((subj (or (mail-header-subject head) ""))
	type title id)
    (when (string-match
	   (concat ".* SUSE Security \\(Announcement\\|Summary Report\\)"
		   "[ :]*"
		   "\\(.*\\) ?(\\(SUSE-[-:SASR0-9:]*\\))")
	   subj)
      (setq type (match-string 1 subj)
	    title (match-string 2 subj)
	    id (match-string 3 subj)))
    (if (and id type title)
	(format "[%s] %s" id (if (>= (length title) 1)
				 title
			       (format "*%s*" type)))
      subj)))


(defalias 'gnus-user-format-function-list-subject
  'rs-gnus-summary-line-list-subject)

;; Example...
(defun rs-gnus-summary-line-sender (header)
  "Display sender of message in summary line.

This function is intended to be used in `gnus-summary-line-format-alist', with
\(defalias 'gnus-user-format-function-X 'rs-gnus-summary-line-sender).
See (info \"(gnus)Group Line Specification\").

You need to add `Sender' to `nnmail-extra-headers' and
`gnus-extra-headers', see Info node `(gnus)To From Newsgroups'."
  (let ((case-fold-search t))
    (or (cdr (assq 'Sender (mail-header-extra header)))
	"no sender found")))

;; An example for noffle:
;; (defun gnus-user-format-function-noffle (header)
;;   "Display noffle status in summary line.
;; You need to add `X-NOFFLE-Status' to `nnmail-extra-headers' and
;; `gnus-extra-headers', see Info node `(gnus)To From Newsgroups'."
;;   (let ((case-fold-search t)
;; 	(val (or (cdr (assq 'X-NOFFLE-Status (mail-header-extra header)))
;; 		 "unknown")))
;;     (gnus-replace-in-string val "^\\(\\w\\).*$" "\\1")))

;;;###autoload
(defun rs-gnus-balloon-0 (window object position)
  "Show some informations about the current article.
Informations include size, score, content type and number.
Used as help echo for the summary buffer."
  ;; (gnus-message 10 "rs-gnus-balloon-0")
  (with-current-buffer object
    (let* ((article (get-text-property position 'gnus-number))
	   (head (gnus-data-header (gnus-data-find article)))
	   (chars (mail-header-chars head))
	   (size (if (fboundp 'rs-gnus-summary-line-message-size)
		     (rs-gnus-summary-line-message-size head)
		   (gnus-summary-line-message-size head)))
	   (score (gnus-summary-article-score article))
	   (ct (gnus-replace-in-string
		(or (cdr (assq 'Content-Type (mail-header-extra head)))
		    "n/a")
		"[; ].*$" ""))
	   (no (mail-header-number head)))
      (format "%-10s%s\n%-10s%s\n%-10s%s\n%-10s%s\n%-10s%s\n"
	      "Size:" size
	      "Chars:" chars
	      "Score:" score
	      "C-Type:" ct
	      "Number:" no))))

;;;###autoload
(defun rs-gnus-balloon-1 (window object position)
  "Show full \"From\", \"Subject\", \"To\", and \"Date\" of the current article.
Used as help echo for the summary buffer."
  ;; (gnus-message 10 "rs-gnus-balloon-1")
  (with-current-buffer object
    (let* ((article (get-text-property position 'gnus-number))
	   (head (gnus-data-header (gnus-data-find article)))
	   (from (mail-header-from head))
	   (subject (mail-header-subject head))
	   (to (cdr (or (assq 'To (mail-header-extra head)))))
	   (ng (cdr (or (assq 'Newsgroups (mail-header-extra head)))))
	   (date (mail-header-date head)))
      (format "%-11s%s\n%-11s%s\n%-11s%s\n%-11s%s\n"
	      "From:" from
	      "Subject:" subject
	      "Date:" date
	      (cond (to "To:")
		    (ng "Newsgroup:")
		    (t "To/Ngrp:"))
	      (or to ng "n/a")))))

;;;###autoload
(defun rs-gnus-summary-line-initialize ()
  "Setup my summary line."
  (interactive)
  ;; Alias for the content-type function:
  (defalias 'gnus-user-format-function-ct 'rs-gnus-summary-line-content-type)
  ;; Alias for the size function:
  (defalias 'gnus-user-format-function-size 'rs-gnus-summary-line-message-size)
  ;; Alias for the score function:
  (defalias 'gnus-user-format-function-score 'rs-gnus-summary-line-score)
  ;;
  (defalias 'gnus-user-format-function-label 'rs-gnus-summary-line-label)
  ;;
  ;; Use them:
  (setq gnus-balloon-face-0 'rs-gnus-balloon-0)
  (setq gnus-balloon-face-1 'rs-gnus-balloon-1)
  ;; Unbold face for UTF arrows: (FIXME: Doesn't work on marauder.)
  (copy-face 'default 'rs-gnus-face-1)
  (setq gnus-face-1 'rs-gnus-face-1)
  ;; (set-face-italic-p 'rs-gnus-face-1 nil)
  ;; (dolist (el '(gnus-summary-low-ancient-face
  ;; 		gnus-summary-low-read-face
  ;; 		gnus-summary-low-ticked-face
  ;; 		gnus-summary-low-undownloaded-face
  ;; 		gnus-summary-low-unread-face))
  ;;   (message "%s" el)
  ;;   (set-face-italic-p el nil)
  ;;   (set-face-bold-p el nil)
  ;;   (sit-for 1))
  (if (or (not window-system)
	  (string-match "marauder\\|siogo" system-name))
      (rs-gnus-summary-tree-arrows-latin)
    (rs-gnus-summary-tree-arrows))
  ;; Set line format:
  (setq gnus-summary-line-format
	"%«%U%R%u&score;%u&ct; %4u&size;%»%* %(%-20,20f%) %1«%1{%B %}%s%»\n"))

(defcustom rs-gnus-expirable-authors nil
  "List of authors that are used in `rs-gnus-summary-mark-lists-expirable'."
  :group 'gnus-summary
  :type '(repeat (string :tag "Author")))

(defcustom rs-gnus-expirable-subjects nil
  "List of subjects that are used in `rs-gnus-summary-mark-lists-expirable'."
  :group 'gnus-summary
  :type '(repeat (string :tag "Subject")))

;;;###autoload
(defun rs-gnus-summary-mark-lists-expirable ()
  "Mark some articles (lists, ...) as expirable."
  (interactive)
  (let ((gnus-summary-generate-hook nil)
	(subj (regexp-opt rs-gnus-expirable-subjects t))
	(from (regexp-opt rs-gnus-expirable-authors t)))
    (gnus-uu-mark-by-regexp subj)
    (autoload 'ignore-errors "cl")
    (when (ignore-errors
	    (progn
	      (gnus-summary-limit-to-author from)
	      t))
      (gnus-uu-mark-buffer)
      (gnus-summary-pop-limit t))
    (let ((articles (gnus-summary-work-articles nil))
	  article)
      (save-excursion
	(while articles
	  (gnus-summary-goto-subject (setq article (pop articles)))
	  (let (gnus-newsgroup-processable)
	    (gnus-summary-mark-as-expirable 1))
	  (gnus-summary-remove-process-mark article)))))
  (when (y-or-n-p "Expire articles now? ")
    (gnus-summary-expire-articles 'now)))

;;;###autoload
(defun rs-gnus-summary-more-headers ()
  "Force redisplaying of the current article with ..."
  (interactive)
  (let ((gnus-visible-headers
	 (concat gnus-visible-headers "\\|^X-\\|^NNTP")))
    (gnus-summary-show-article)))

;;;###autoload
(defun rs-gnus-summary-non-boring-headers ()
  "Force redisplaying of the current article with ..."
  (interactive)
  (let ((gnus-visible-headers nil))
    (gnus-summary-show-article)))

;;;###autoload
(defun rs-gnus-summary-mark-as-expirable-and-next-line(n)
  "Mark N articles forward as expirable and go to next line.
Useful in a summary buffer with read articles."
  (interactive "p")
  (gnus-summary-mark-as-expirable n)
  (next-line 1))

;;;###autoload
(defun rs-gnus-summary-mark-as-expirable-dont-move ()
  "Mark this article expirable.  Don't move point."
  (interactive)
  (gnus-summary-mark-article nil ?E nil))

;;;###autoload
(defun rs-gnus-summary-mark-as-expirable-next-article ()
  "Mark this article expirable.  Move to next article."
  (interactive)
  (gnus-summary-mark-article nil ?E nil)
  (gnus-summary-next-article))

;; Suggested by David Mazieres in <news:6czn0zqcc5.fsf@orchard.scs.cs.nyu.edu>
;; in analogy to `rmail-summary-by-recipients'.  Unlike
;; `rmail-summary-by-recipients', doesn't include From.

;;;###autoload
(defun rs-gnus-summary-limit-to-recipient (recipient &optional not-matching)
  "Limit the summary buffer to articles with the given RECIPIENT.

If NOT-MATCHING, exclude RECIPIENT.

To and Cc headers are checked.  You need to include them in
`nnmail-extra-headers'."
  ;; Unlike `rmail-summary-by-recipients', doesn't include From.
  (interactive
   (list (read-string (format "%s recipient (regexp): "
			      (if current-prefix-arg "Exclude" "Limit to")))
	 current-prefix-arg))
  (when (not (equal "" recipient))
    (prog1 (let* ((to
		   (if (memq 'To nnmail-extra-headers)
		       (gnus-summary-find-matching
			(cons 'extra 'To) recipient 'all nil nil
			not-matching)
		     (gnus-message
		      1 "`To' isn't present in `nnmail-extra-headers'")
		     (sit-for 1)
		     nil))
		  (cc
		   (if (memq 'Cc nnmail-extra-headers)
		       (gnus-summary-find-matching
			(cons 'extra 'Cc) recipient 'all nil nil
			not-matching)
		     (gnus-message
		      1 "`Cc' isn't present in `nnmail-extra-headers'")
		     (sit-for 1)
		     nil))
		  (articles
		   (if not-matching
		       ;; We need the numbers that are in both lists:
		       (mapcar (lambda (a)
				 (and (memq a to) a))
			       cc)
		     (nconc to cc))))
	     (unless articles
	       (error "Found no matches for \"%s\"" recipient))
	     (gnus-summary-limit articles))
      (gnus-summary-position-point))))

;;;###autoload
(defun rs-gnus-summary-sort-by-recipient (&optional reverse)
  "Sort the summary buffer by recipient name alphabetically.
If `case-fold-search' is non-nil, case of letters is ignored.
Argument REVERSE means reverse order."
  (interactive "P")
  (gnus-summary-sort 'recipient reverse))

(defsubst rs-gnus-article-sort-by-recipient (h1 h2)
  "Sort articles by recipient."
  (string-lessp
   (let ((extract (funcall
		   gnus-extract-address-components
		   (or (cdr (assq 'To (mail-header-extra h1))) ""))))
     (or (car extract) (cadr extract)))
   (let ((extract (funcall
		   gnus-extract-address-components
		   (or (cdr (assq 'To (mail-header-extra h2))) ""))))
     (or (car extract) (cadr extract)))))

(defun rs-gnus-thread-sort-by-recipient (h1 h2)
  "Sort threads by root recipient."
  (gnus-article-sort-by-recipient
   (gnus-thread-header h1)
   (gnus-thread-header h2)))

;; Not using my own namespace prefix because `gnus-summary-sort' wants
;; gnus-thread-sort-by-%s" and "gnus-article-sort-by-%s":
(require 'gnus-sum)
(unless (fboundp 'gnus-article-sort-by-recipient)
  (defalias 'gnus-article-sort-by-recipient
    'rs-gnus-article-sort-by-recipient))
(unless (fboundp 'gnus-thread-sort-by-recipient)
  (defalias 'gnus-thread-sort-by-recipient
    'rs-gnus-thread-sort-by-recipient))

;;;###autoload
(defun rs-gnus-summary-score-statistics (&optional ancient quiet)
  "Display score statistics for current summary buffer.

If ANCIENT, also count ancient articles.  Returns a list: (high
default low)."
  (interactive)
  (let ((high 0) (dflt 0) (low 0))
    (dolist (i gnus-newsgroup-scored)
      (cond
       ;; Ignore ancient articles
       ;; ((memq (car i) gnus-newsgroup-ancient) 'ancient)
       ;; ((not (memq (car i) gnus-newsgroup-unreads)) 'not-unread)
       ((and (not ancient)
	     (not (memq (car i) gnus-newsgroup-articles)))
	'not-art)
       ;;
       ((< (cdr i) gnus-summary-default-score) (setq low  (1+ low)))
       ((> (cdr i) gnus-summary-default-score) (setq high (1+ high)))))
    (setq dflt (- (+ (length gnus-newsgroup-articles)
		     (if ancient
			 (length gnus-newsgroup-ancient)
		       0))
		  low high))
    (unless quiet
      (gnus-message 1 "Score statistics: %s high, %s default, %s low."
		    high dflt low))
    (list high dflt low)))
;; (add-hook 'gnus-summary-prepared-hook 'rs-gnus-summary-score-statistics)

(defcustom rs-gnus-leafnode-filter-file "/usr/local/etc/leafnode/filters"
  "Filter file for leafnode."
  ;; May be a tramp file name ("/su:/etc/leafnode/filters") if file is not
  ;; writable for the user.
  :group 'gnus-summary
  :type '(choice (const "/usr/local/etc/leafnode/filters")
		 (const "/su:/usr/local/etc/leafnode/filters")
		 (const "/su:/etc/leafnode/filters")
		 (const "/root@localhost:/etc/leafnode/filters")
		 file))

;;;###autoload
(defun rs-gnus-leafnode-kill-thread ()
  "Kill thread from here using leafnode."
  (interactive)
  (let ((mid (gnus-with-article-buffer (gnus-fetch-field "Message-Id")))
	(file rs-gnus-leafnode-filter-file)
	rule)
    (gnus-message 9 "Writing kill rule for MID `%s' to file `%s'" mid file)
    (with-temp-buffer
      (insert "\nnewsgroups = "
	      (regexp-quote gnus-newsgroup-name)
	      "\npattern = ^References:.*"
	      (regexp-quote mid)
	      "\naction = kill\n")
       (append-to-file (point-min) (point-max) file))))
;; (define-key gnus-summary-mode-map (kbd "C-c k") 'rs-gnus-leafnode-kill-thread)

;; /var/spool/news$ find `ls -d|grep -v '\.'` -name '.overview' |xargs grep 'Postal Lottery:'|awk -F'   ' '{print $5}'|xargs -n 1 /usr/local/sbin/applyfilter -n -C

;; FIXME: Only half finished!
(defun rs-gnus-summary-applyfilter (subject &optional spoolbase overview)
  "Find articles with subject matching SUBJECT and delete them from the spool."
  (unless spoolbase
    (setq spoolbase "/var/spool/news/"))
  (unless overview
    (setq overview ".overview"))
  (dolist (ent gnus-newsrc-alist)
    (let ((full (car ent))
	  (level (nth 1 ent))
	  overfile)
      (unless (string-match "nn.*:" full)
	(setq overfile (concat spoolbase
			       (subst-char-in-string ?. ?/ full)
			       "/" overview))
	(message overfile)))))

;;; provide ourself

(provide 'rs-gnus-summary)

;;; rs-gnus-summary.el ends here

;; Local Variables:
;; coding: utf-8
;; End:
