;;; w3m-save.el --- Save the page to the local files

;; Copyright (C) 2015-2017 TSUCHIYA Masatoshi <tsuchiya@namazu.org>

;; Author: Katsumi Yamaoka <yamaoka@jpl.org>
;; Keywords: w3m, WWW, hypermedia

;; This file is a part of emacs-w3m.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Save the current page and its image data, if any, to a local file
;; PAGE.html and sub-directory PAGE-files/.  PAGE.html and PAGE-files/
;; are portable; you can move them to any place including a web site.

;;; Code:

(eval-when-compile (require 'cl))
(require 'w3m)

(defcustom w3m-save-buffer-directory (expand-file-name
				      "saved/"
				      w3m-default-save-directory)
  "Default directory for saved pages and their image files."
  :group 'w3m
  :type 'directory)

(defcustom w3m-save-buffer-use-cache t
  "If non-nil, use cached data if available."
  :group 'w3m
  :type 'boolean)

(defcustom w3m-save-buffer-html-only nil
  "Save images along with a web-page, or just html.
If nil, `w3m-save-buffer' will save the images of a buffer in
addition to the buffer's html. If the buffer was originally
loaded without images, the images will now be retrieved. The
value of this variable may be over-ridden at run-time by passing
a prefix argument to function `w3m-save-buffer'."
  :group 'w3m
  :type 'boolean)

(defun w3m-save-buffer (name &optional no-images)
  "Save the current w3m buffer.
Save the current buffer as `w3m-save-buffer-directory'/NAME.html,
and optionally save the buffer's associated image files in
folder `w3m-save-buffer-directory'/NAME-files/. Use of
`w3m-save-buffer-directory' may be over-ridden by including a
folder path in NAME. Variable `w3m-save-buffer-html-only'
determines whether images will be saved by default, but that
setting may be toggled using the prefix argument (the
optional NO-IMAGES). The saved page will be added to the
history list, and be viewable using `w3m-next-page'."
  (interactive
   (if (and w3m-current-url
	    (or (not (string-match "\\`[\C-@- ]*\\'\\|\\`about:\\|\\`file:"
				   w3m-current-url))
		(string-match "\\`about://\\(?:header\\|source\\)/"
			      w3m-current-url)))
       (let ((name (or (and (stringp w3m-current-title)
			    (not (string-match "\\`[\C-@- ]*\\'"
					       w3m-current-title))
			    w3m-current-title)
		       (and (not (string-match "\\`[\C-@- ]*\\'"
					       w3m-current-url))
			    (file-name-nondirectory w3m-current-url))
		       (make-temp-name "w3m-")))
	     (case-fold-search t))
	 (setq name (w3m-replace-in-string name "[\C-@- \"*/:<>?\|]+" "_"))
	 (list
	  (read-file-name
	   (if (not w3m-save-buffer-html-only)
	       "Save this page (with images) to: "
	     "Save this page (html only) to: ")
	   (file-name-as-directory w3m-save-buffer-directory)
	   name nil (concat name ".html"))
	  current-prefix-arg))
     (error "No valid url for this page")))
  (when w3m-save-buffer-html-only
    (setq no-images (not no-images)))
  (let ((url w3m-current-url)
	(w3m-prefer-cache w3m-save-buffer-use-cache)
	(case-fold-search t)
	subdir type st base regexp sdir charset ibuf imgs nd img bads bname
	ext num bn)
    (unless (and url
		 (or (not (string-match
			   "\\`[\C-@- ]*\\'\\|\\`about:\\|\\`file:"
			   url))
		     (and (string-match "\\`about://\\(?:header\\|source\\)/"
					url)
			  (setq url (substring url (match-end 0)))
			  (not (string-match "\\`[\C-@- ]*\\'" url)))))
      (error "No valid url for this page"))
    (cond ((or (not (stringp name))
	       (string-match "\\`[\C-@- ]*\\'" name))
	   (error "No valid file name"))
	  ((not (string-match "\\.html?\\'" name))
	   (setq name (concat name ".html"))))
    (unless (file-name-directory name)
      (setq name (expand-file-name name w3m-save-buffer-directory)))
    (setq subdir (concat (file-name-sans-extension name) "-files"))
    (cond ((and (not no-images) (file-exists-p name) (file-exists-p subdir))
	   (if (yes-or-no-p
		(format "#1=%s and #1#-files/ already exist in %s, overwrite? "
			(file-name-nondirectory name)
			(file-name-directory name)))
	       (progn
		 (delete-file name)
		 (delete-directory subdir t))
	     (keyboard-quit)))
	  ((file-exists-p name)
	   (if (yes-or-no-p (format "%s already exists, overwrite? " name))
	       (delete-file name)
	     (keyboard-quit)))
	  ((and (not no-images) (file-exists-p subdir))
	   (if (yes-or-no-p (format "%s already exists, overwrite? " subdir))
	       (delete-directory subdir t)
	     (keyboard-quit))))
    (with-temp-buffer
      (unless (setq type (w3m-retrieve url))
	(error "Retrieving failed: %s" url))
      (goto-char (point-min))
      ;; Look for <base> url.
      (setq base (if (and (re-search-forward "<head[\t\n >]" nil t)
			  (progn
			    (setq st (match-end 0))
			    (re-search-forward "</head[\t\n >]" nil t))
			  (re-search-backward "<\\(base\
\\(?:[\t\n ]+[^\t\n >]+\\)*[\t\n ]+href=\"\\([^\"]+\\)\"[^>]*\\)>" st t))
		     (prog1
			 (match-string 2)
		       (replace-match "<!--\\1-->"))
		   url))
      (setq st (point))
      ;; Make link urls absolute.
      (dolist (tag '(("a" . "href") ("form" . "action")))
	(setq regexp (concat "<" (car tag)
			     "\\(?:[\t\n ]+[^\t\n >]+\\)*[\t\n ]+"
			     (cdr tag) "=\"\\([^\"]+\\)"))
	(while (re-search-forward regexp nil t)
	  (insert (prog1
		      (condition-case nil
			  (w3m-expand-url (match-string 1) base)
			(error (match-string 1)))
		    (delete-region (match-beginning 1) (match-end 1)))))
	(goto-char st))
      ;; Save images into `subdir'.
      (unless no-images
	(make-directory subdir t)
	(setq sdir (file-name-nondirectory (directory-file-name subdir)))
	(when (and (setq charset (or (w3m-arrived-content-charset url)
				     (w3m-content-charset url)
				     (and (equal "text/html" type)
					  (w3m-detect-meta-charset))
				     (w3m-detect-xml-charset)))
		   (setq charset (w3m-charset-to-coding-system charset)))
	  (setq sdir (encode-coding-string sdir charset)))
	(unwind-protect
	    (while (re-search-forward "<img\
\\(?:[\t\n ]+[^\t\n >]+\\)*[\t\n ]+src=\"\\([^\"?]+\\)" nil t)
	      (setq st (match-beginning 1)
		    nd (match-end 1)
		    img (w3m-expand-url (match-string 1) base))
	      (when
		  (cond
		   ((member img bads) nil)
		   ((assoc img imgs)
		    (setq bname (cadr (assoc img imgs))
			  ext (caddr (assoc img imgs)))
		    t)
		   (t
		    (with-current-buffer
			(or ibuf
			    (setq ibuf (generate-new-buffer " *temp*")))
		      (erase-buffer)
		      (if (setq type (w3m-retrieve img))
			  (progn
			    (push (list img) imgs)
			    (setq img (file-name-nondirectory img)
				  bname (file-name-sans-extension img)
				  ext (file-name-extension img)
				  num 1)
			    (if (zerop (length ext))
				(when (setq ext (assoc type
						       w3m-image-type-alist))
				  (setq ext (concat "."
						    (symbol-name (cdr ext)))))
			      (setq ext (concat "." ext)))
			    (setq bname (w3m-replace-in-string
					 bname "[\C-@- \"*/:<>?\|]+" "_"))
			    (when (file-exists-p (expand-file-name
						  (concat bname ext) subdir))
			      (while (progn
				       (setq bn (concat
						 bname "-"
						 (number-to-string num)))
				       (file-exists-p
					(expand-file-name
					 (concat bn ext) subdir)))
				(setq num (1+ num)))
			      (setq bname bn))
			    (setcdr (car imgs) (list bname ext))
			    (write-region (point-min) (point-max)
					  (expand-file-name
					   (concat bname ext) subdir))
			    t)
			(push img bads)
			nil))))
		(delete-region (goto-char st) nd)
		(insert sdir "/" bname (or ext ""))))
	  (when ibuf (kill-buffer ibuf))
	  (unless imgs (delete-directory subdir))))
      (unless (file-exists-p (file-name-directory name))
	(make-directory (file-name-directory name) t))
      (write-region (point-min) (point-max) name))
    (w3m-history-set-current
     (prog1
	 (cadar w3m-history)
       (w3m-history-push (w3m-expand-file-name-as-url name)
			 (list :title (or w3m-current-title "<no-title>")))))
    name))

(provide 'w3m-save)

;; w3m-save.el ends here
