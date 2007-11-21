;;; visit-url.el --- Front-end function to the `browse-url' package

;; Copyright (C) 2001 John Wiegley <johnw@gnu.org>

;; Emacs Lisp Archive Entry
;; Filename: visit-url.el
;; Version: 1.1
;; Keywords: hypertext, hypermedia, www
;; Author: John Wiegley <johnw@gnu.org>
;; Maintainer: John Wiegley <johnw@gnu.org>
;; Description: Front-end function to the `browse-url' package
;; URL: http://www.gci-net.com/~johnw/Emacs/visit-url.el
;; Compatibility: Emacs20, Emacs21

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;; MA 02111-1307, USA.

;;; Commentary:

(defgroup visit-url nil
  "Front-end functionality to the `browse-url' package."
  :group 'hypermedia)

(defcustom visit-url-archive-names
  "\\.\\(tar\\|tgz\\|gz\\|bz2\\|Z\\|el\\|deb\\|rpm\\)\\'"
  "A regexp that matches URLs which should be downloaded, not visited."
  :type 'regexp
  :group 'visit-url)

(defcustom visit-url-download-function 'w3m-download
  "The function to call for downloading URLs."
  :type 'function
  :group 'visit-url)

(defun visit-url-expand-hostname (host)
  (let ((possibles (list (concat "www." host ".com")
			 (concat "www." host ".org")
			 (concat "www." host ".net")
			 (concat "www." host ".edu")
			 (concat host ".com")
			 (concat host ".org")
			 (concat host ".net")
			 (concat host ".edu")))
	found)
    (while possibles
      (if (= 0 (call-process "host" nil nil nil (car possibles)))
	  (setq found (car possibles) possibles nil)
	(setq possibles (cdr possibles))))
    found))

;;;###autoload
(defun visit-url (&optional url)
  (interactive)
  (require 'thingatpt)
  (if (and (null url)
	   (thing-at-point-looking-at thing-at-point-url-regexp))
      (if (and (interactive-p) current-prefix-arg)
	  (browse-url-netscape (thing-at-point-url-at-point))
	(browse-url (thing-at-point-url-at-point)))
    (or url (setq url (completing-read "Visit URL: "
				       'read-file-name-internal)))
    (if (file-readable-p url)
	(setq url (concat "file:" (expand-file-name url)))
      (if (string-match "\\`\\(\\([^:]+\\)://\\)?\\([^/]+\\)\\(.*\\)" url)
	  (let ((protocol (or (match-string 2 url) "http"))
		(host (match-string 3 url))
		(path (match-string 4 url)))
	    (unless (string-match "\\." host)
	      (setq host (visit-url-expand-hostname host)))
	    (setq url (concat protocol "://" host path)))))
    (message url)
    (cond
     ((string-match visit-url-archive-names url)
      (funcall visit-url-download-function url))
     (t
      (browse-url url)))))

(provide 'visit-url)

;;; visit-url.el ends here
