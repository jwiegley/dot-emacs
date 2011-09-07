;;; bbdb-vcard-import.el -- import vCards into BBDB
;; 
;; Copyright (c) 2008 Marcus Crestani
;;
;; bbdb-vcard-import.el is free software you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.
;;
;; This software is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
;;
;; Author: Marcus Crestani <crestani@informatik.uni-tuebingen.de>
;; Created: 2008-01-03
;; Version: $Id: bbdb-vcard-import.el,v 1.6 2008/01/31 16:19:15 cvs Exp $
;; Keywords: vcard bbdb
;;
;; This requires vcard.el by NoahFriedman for the importer to work.
;;
;;    http://www.splode.com/~friedman/software/emacs-lisp/src/vcard.el
;;
;; The implementation is based on Christopher Smiths very simple
;; version of `bbdb-vcard-snarf-buffer':
;;
;;   http://www.emacswiki.org/cgi-bin/wiki/BbdbImporters#toc3
;;

;;; Commentary

;;
;; To import all vCards that are in the file ~/vCards.vcf do:
;;
;;	M-x bbdb-vcard-import RET ~/vCards.vcf RET
;;

;;; Todo

;;
;; STREET ADDRESSES and PHONE NUMBERS are not yet imported.  See
;; comment in `bbdb-vcard-merge'.
;;

;;; ChangeLog

;;
;; 2008-01-31  Marcus Crestani  <crestani@informatik.uni-tuebingen.de>
;;   - Do not enforce (type . "internet") for email addresses.
;; 
;; 2008-01-03  Marcus Crestani  <crestani@informatik.uni-tuebingen.de>
;;   - Initial version.
;;

;;; Code:

(require 'vcard)
(require 'bbdb)

(defvar bbdb-vcard-merged-records nil)

(defun bbdb-vcard-filter-empty-values (values)
  "Filter out empty values."
  (if (consp values)
      (if (string= "" (car values))
	  (bbdb-vcard-filter-empty-values (cdr values))
	(cons (car values) (bbdb-vcard-filter-empty-values (cdr values))))))

(defun bbdb-vcard-values (record field)
  "Return the values of an RECORD's FIELD; empty string entries are filtered out."
  (let ((values (vcard-values record (list field))))
    (if values
	(mapconcat 'identity 
		   (bbdb-vcard-filter-empty-values (car values))
		   ", ")
      "")))

(defun bbdb-vcard-get-emails (record)
  "Return a list of email addresses."
  (let ((pref (vcard-ref record '("email" ("type" . "pref"))))
	(rest (vcard-ref record '("email") '(("type" . "pref")))))
    (mapcar (lambda (entry) (car (cdr entry))) 
	    (if pref 
		(cons (car pref) rest)
	      rest))))

(defun bbdb-vcard-get-phones (record)
  "Return a list of phone number objects."
  (let ((pref (vcard-ref record '("tel" ("type" . "pref"))))
	(rest (vcard-ref record '("tel") '(("type" . "pref")))))
    (mapcar (lambda (entry)
	      (let ((proplist (car entry))
		    (phone (car (cdr entry))))
		(vector
		 (vcard-get-property proplist "type")
		 phone)))
	    (if pref
		(cons (car pref) rest)
	      rest))))

(defun bbdb-vcard-get-addresses (record)
  "Return a list of adress objects."
  (let ((pref (vcard-ref record '("adr" ("type" . "pref"))))
	(rest (vcard-ref record '("adr") '(("type" . "pref")))))
    (mapcar (lambda (entry)
	      (let ((proplist (car entry))
		    (phone (car (cdr entry))))
		(vector
		 (vcard-get-property proplist "type")
		 phone)))
	    (if pref
		(cons (car pref) rest)
	      rest))))

(defun bbdb-vcard-merge-interactively (name company nets addrs phones notes)
  "Interactively add a new record; see \\[bbdb-merge-interactively]."
  (let*
      ((f-l-name (bbdb-divide-name name))
       (firstname (car f-l-name))
       (lastname (nth 1 f-l-name))
       (aka nil)
       (new-record
        (vector firstname lastname aka company phones addrs
                (if (listp nets) nets (list nets)) notes
                (make-vector bbdb-cache-length nil)))
       (old-record (bbdb-search-simple name nets)))
    (if old-record
	(progn
	  (setq new-record (bbdb-merge-internally old-record new-record))
	  (bbdb-delete-record-internal old-record)))
    ;; create  new record
    (bbdb-invoke-hook 'bbdb-create-hook new-record)
    (bbdb-change-record new-record t)
    (bbdb-hash-record new-record)
    new-record))

(defun bbdb-vcard-merge (record)
  "Merge data from vcard interactively into bbdb."
  (let* ((name (bbdb-vcard-values record "fn"))
	 (company (bbdb-vcard-values record "org"))
	 (net (bbdb-vcard-get-emails record))
	 (addrs (bbdb-vcard-get-addresses record))
	 (phones (bbdb-vcard-get-phones record))
	 (categories (bbdb-vcard-values record "categories"))
	 (notes (and (not (string= "" categories))
		     (list (cons 'categories categories))))
	 ;; TODO: addrs and phones are not yet imported.  To do this
	 ;; right, figure out a way to map the several labels to
	 ;; `bbdb-default-label-list'.  Also, some phone number
	 ;; conversion may break the format of numbers.
	 (new-record (bbdb-vcard-merge-interactively name company net nil nil notes)))
    (setq bbdb-vcard-merged-records (append bbdb-vcard-merged-records 
					    (list new-record)))))

(defun bbdb-vcard-snarf-region (begin end)
  "Bbdb-snarf each match."
  (let ((record (vcard-parse-region begin end)))
    (bbdb-vcard-merge record)))

(defun bbdb-vcard-snarf-buffer (buf)
  "Traverse BUF via regex.  Bbdb-snarf against each match."
  (setq bbdb-vcard-merged-records nil)
  (let ((bbdb-current-buffer (current-buffer))
	(bbdb-current-point (point-min))
	(bbdb-next-point (point-min)))
    (switch-to-buffer buf)
    (goto-char bbdb-current-point)
    (while (re-search-forward "END:VCARD" nil (message "%s done" buf))
      (setq bbdb-next-point (point))
      (bbdb-vcard-snarf-region bbdb-current-point (point))
      (switch-to-buffer buf)
      (goto-char bbdb-next-point)
      (setq bbdb-current-point (point)))
    (switch-to-buffer bbdb-current-buffer)
    (bbdb-display-records bbdb-vcard-merged-records)))

(defun bbdb-vcard-snarf-current-buffer ()
  "Snarf the vcards in the current buffer."
  (interactive)
  (bbdb-vcard-snarf-buffer (current-buffer)))

(defun bbdb-vcard-import-current-buffer ()
  "Import the vcards in the current buffer into your bbdb."
  (interactive)
  (bbdb-vcard-snarf-current-buffer))

(defun bbdb-vcard-import (file)
  "Import the vcards in FILE into your bbdb."
  (interactive "FvCard file to read from: ")
  (let ((buffer (find-file file)))
    (bbdb-vcard-snarf-buffer buffer)
    (revert-buffer buffer)
    (kill-buffer buffer)))

(provide 'bbdb-vcard-import)
