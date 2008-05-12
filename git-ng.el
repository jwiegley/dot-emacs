;;; git-ng.el --- next generation Git interface for Emacs

;; Copyright (C) 2008  John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Keywords: completion convenience tools vc
;; Version: 0.01
;; location: http://www.newartisans.com/software/emacs.html

;; This file is not yet part of GNU Emacs.

;; This module is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.

;; This module is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Code:

(eval-when-compile
  (require 'cl)
  (require 'add-log))

;; Attempt to handle older/other emacs in XEmacs way.
;; If `line-beginning-position' isn't available, use point-at-bol.
(unless (fboundp 'line-beginning-position)
  (defalias 'line-beginning-position 'point-at-bol))

(defgroup gitsum nil
  "Special support for the Git content tracker."
;;  :version "21.4"
  :group 'tools
  :prefix "gitsum-")

(defvar gitsum-data nil)
(defvar gitsum-look-for-adds nil)

(defface gitsum-header-face
  '((((class color) (background dark))
     (:foreground "lightyellow" :bold t))
    (((class color) (background light))
     (:foreground "blue4" :bold t))
    (t (:bold t)))
  "Face used to highlight directory changes."
  :group 'gitsum)

(defface gitsum-marked-face
  '((t (:bold t)))
  "Face used to highlight marked changes."
  :group 'gitsum)

(defface gitsum-need-action-face
  '((((class color) (background dark))
     (:foreground "orange"))
    (((class color) (background light))
     (:foreground "orange"))
    (t (:italic t)))
  ""
  :group 'gitsum)

(defface gitsum-need-action-marked-face
  '((((class color) (background dark))
     (:foreground "orange" :bold t))
    (((class color) (background light))
     (:foreground "orange" :bold t))
    (t (:italic t :bold t)))
  ""
  :group 'gitsum)

(defface gitsum-filename-face
  '((((class color) (background dark))
     (:foreground "lightblue"))
    (((class color) (background light))
     (:foreground "blue4"))
    (t ()))
  "Face used to highlight file names."
  :group 'gitsum)

(defface gitsum-change-line-face
  '((((class color) (background dark))
     (:foreground "grey75" :background "grey25"))
    (((class color) (background light))
     (:foreground "grey25" :background "grey75"))
    (t (:bold t)))
  "Face used to highlight file names."
  :group 'gitsum)

(defun gitsum-add-props (str &rest props)
  (add-text-properties 0 (1- (length str)) (list* props) str)
  str)

(defun gitsum-add-face (str face &optional keymap &rest props)
  (when keymap
    (when (keymapp keymap)
      (setq props (list* 'keymap keymap props)))
    (setq props (list* 'mouse-face 'highlight props)))
  (add-text-properties 0 (length str) (list* 'face face props) str)
  str)

;;; Code to work with changesets

;; A changeset is an alist of the following form:
;;
;;   ((DIR (FILE (LINE CHANGE...))))
;;
;; Where DIR and FILE are plain strings, but LINE is of the following
;; possible formats:
;;
;;   LINE     An integer giving the first line of the hunk
;;   -LINE    Integer line of hunk, but hunk is not "visible"
;;   (LINE)   Integer line of hunk, but hunk is "marked"
;;   SYMBOL   Non-hunk change: 'addfile 'newfile 'rmfile 'binary or 'replace
;;   -SYMBOL  Non-hunk change, but change is not "visible"
;;   (SYMBOL) Non-hunk change, but change is "marked"
;;
;; Each CHANGE is a string which represents a modification to make to
;; the file after the starting LINE.  It begins with either a "+" or
;; "-" to indicate if the line should be removed or added to the file.
;;
;; So, for example, in a buffer with no changes visible or marked yet:
;;
;; (("."
;;  ("TODO" (addfile))
;;  ("report.cc" (-replace "[A-Za-z_0-9] indented intended"))
;;  ("report.cc"
;;   (-606 "-    blah" "+    blah" "+    blah")
;;   (-620 "-    blah" "+    blah" "+    blah")
;;   (-629 "-    blah" "+    blah" "+    blah")
;;   (-634 "-    blah" "+    blah" "+    blah")
;;   (-641 "-    blah" "+    blah" "+    blah")
;;   (-652 "-    blah" "+    blah" "+    blah")
;;   (-664 "-    blah" "+    blah" "+    blah"))
;;  ("report.h"
;;   (-115 "-    blah" "+    blah" "+    blah")
;;   (-126 "+"))))

(defconst gitsum-invisible-item-alist
  '((-replace . replace)
    (-addfile . addfile)
    (-newfile . newfile)
    (-rmfile  . rmfile)
    (-binary  . binary)))

(defun gitsum-item-visible-p (item)
  "Is ITEM visible?
Everything but negative numbers and invisible symbols are visible."
  (if (numberp item) (<= 0 item)
    (not (assq item gitsum-invisible-item-alist))))

(defun gitsum-visible-item (item)
  "Convert ITEM to visible."
  (let (a)
    (cond
     ((numberp item) (abs item))
     ((setq a (assq item gitsum-invisible-item-alist)) (cdr a))
     (t item))))

(defun gitsum-invisible-item (item)
  "Convert ITEM to invisible."
  (let (a)
    (cond
     ((numberp item) (- (abs item)))
     ((setq a (rassq item gitsum-invisible-item-alist)) (car a))
     (t item))))

(defun gitsum-toggle-item (item)
  "Mark visible change ITEM as invisible and vice versa."
  (let (a)
    (cond
     ((numberp item) (- item))
     ((setq a (assq item gitsum-invisible-item-alist)) (cdr a))
     ((setq a (rassq item gitsum-invisible-item-alist)) (car a))
     (t item))))

(defconst gitsum-item-status-alist
  '((replace . "Modified")
    (addfile . "Added")
    (newfile . "Unknown")
    (rmfile  . "Deleted")
    (binary  . "Modified (binary)")))

(defun gitsum-item-status (item)
  "Return file-status displayed with ITEM."
  (cdr (assq (gitsum-visible-item item) gitsum-item-status-alist)))

(eval-and-compile
  (if (fboundp 'make-temp-file)
      (defalias 'gitsum-make-temp-file 'make-temp-file)
    ;; make-temp-name generates a unique name when it is called, but
    ;; takes no provisions to ensure that it will remain unique. Thus,
    ;; there is a race condition before we use the name. This is
    ;; probably a bad thing.
    (defalias 'gitsum-make-temp-file 'make-temp-name)))

(defsubst gitsum-change-item (change)
  (if (listp (car change))
      (caar change)
    (car change)))

(defsubst gitsum-change-line (change)
  (let ((ch (gitsum-change-item change)))
    (if (symbolp ch)
	1
      ch)))

(defun gitsum-applicable-p (data predicate)
  (catch 'exit
    (ignore
     (let (dir file change)
       (dolist (dir data)
	 (dolist (file (cdr dir))
	   (dolist (change (cdr file))
	     (if (funcall predicate (car dir) (car file) change)
		 (throw 'exit t)))))))))

(defsubst gitsum-marked-p (data)
  (gitsum-applicable-p data (function
			      (lambda (dir file change)
				(listp (car change))))))

(defsubst gitsum-changeset-has-change-p (data odir ofile start-line replace)
  (gitsum-applicable-p
   data (function
	 (lambda (d f change)
	   (and (equal odir d)
		(equal ofile f)
		(eq start-line (gitsum-change-item change))
		(gitsum-item-visible-p (gitsum-change-item change))
		(or (not (eq start-line 'replace))
		    (equal (cadr change) replace)))))))

(defun gitsum-changeset-has-directory-p (changeset name)
  (catch 'exit
    (ignore
     (let (dir)
       (dolist (dir changeset)
	 (if (string= name (car dir))
	     (throw 'exit t)))))))

(defun gitsum-find-changeset (data predicate)
  (let (dir file change changeset)
    (dolist (dir data)
      (dolist (file (cdr dir))
	(dolist (change (cdr file))
	  (if (funcall predicate (car dir) (car file) change)
	      (setq changeset
		    (gitsum-add-changeset
		     changeset
		     (list (list (car dir) (list (car file) change)))))))))
    changeset))

(defun gitsum-apply-to-changeset (data func)
  (let (dir file change)
    (dolist (dir data)
      (dolist (file (cdr dir))
	(dolist (change (cdr file))
	  (funcall func (car dir) (car file) change))))))

(defun gitsum-remove-changeset (data changeset)
  "Remove DATA from the current CHANGESET."
  (let (dir file change)
    (dolist (dir changeset)
      (dolist (file (cdr dir))
	(dolist (change (cdr file))
	  (let* ((dentry (assoc (car dir) data))
		 (fentry (assoc (car file) (cdr dentry))))
	    (setcdr fentry (delete (assoc (car change) (cdr fentry))
				   (cdr fentry)))
	    (unless (cdr fentry)
	      (setcdr dentry (delete fentry (cdr dentry))))
	    (unless (cdr dentry)
	      (setq data (delete dentry data))))))))
  data)

(defconst gitsum-item-numeric-alist
  '((addfile . 0)
    (newfile . 0)
    (rmfile . 0)
    (binary . 0)
    (replace . 999999)))

(defun gitsum-change-< (l r)
  (setq l (car l)
	l (if (listp l) (car l) l)	; it might be marked
	l (gitsum-visible-item l)
	l (or (cdr (assq l gitsum-item-numeric-alist)) l))
  (setq r (car r)
	r (if (listp r) (car r) r)
	r (gitsum-visible-item r)
	r (or (cdr (assq r gitsum-item-numeric-alist)) r))
  (< l r))

(defun gitsum-add-changeset (data changeset)
  "Add DATA to the current CHANGESET."
  (let (dir file change)
    (dolist (dir changeset)
      (dolist (file (cdr dir))
	(dolist (change (cdr file))
	  (let ((dentry (assoc (car dir) data)))
	    (if dentry
		(let ((fentry (assoc (car file) dentry)))
		  (if fentry
		      (unless (member change (cdr fentry))
			(nconc fentry (list change))
			(setcdr fentry
				(sort (cdr fentry)
				      (function gitsum-change-<))))
		    (nconc dentry (list (list (car file) change)))))
	      (setq data (cons (list (car dir)
				     (list (car file) change))
			       data))))))))
  data)

(defun gitsum-merge-changeset (data changeset)
  "Merge DATA into the current CHANGESET."
  (let (dir file change final-data)
    (dolist (dir changeset)
      (dolist (file (cdr dir))
	(dolist (change (cdr file))
	  (let ((dentry (assoc (car dir) data)))
	    (if dentry
		(let ((fentry (assoc (car file) dentry))
		      (item (gitsum-change-item change)))
		  (if fentry
		      (unless
			  (or (assoc item (cdr fentry))
			      (assoc (gitsum-toggle-item item) (cdr fentry))
			      (assoc (list item) (cdr fentry)))
			(nconc fentry (list change))
			(setcdr fentry
				(sort (cdr fentry)
				      (function gitsum-change-<))))
		    (nconc dentry (list (list (car file) change)))))
	      (setq data (cons (list (car dir)
				     (list (car file) change))
			       data)))))))
    (dolist (dir data)
      (dolist (file (cdr dir))
	(dolist (change (cdr file))
	  (let* ((dentry (assoc (car dir) changeset))
		 (fentry (assoc (car file) dentry))
		 (item (gitsum-change-item change))
		 final-dentry final-fentry)
	    (when (and dentry fentry
		       (or (assoc item (cdr fentry))
			   (assoc (gitsum-toggle-item item) (cdr fentry))
			   (assoc (list item) (cdr fentry))))
	      (unless (setq final-dentry (assoc (car dir) final-data))
		(setq final-data (cons (list (car dir)) final-data)
		      final-dentry (assoc (car dir) final-data)))
	      (unless (setq final-fentry (assoc (car file) final-dentry))
		(nconc final-dentry (list (list (car file))))
		(setq final-fentry (assoc (car file) final-dentry)))
	      (nconc final-fentry (list change)))))))
    (nreverse final-data)))

(defun gitsum-create-changeset (data kind desc path visible marked
				     &optional contents)
  (let* ((dir (directory-file-name (or (file-name-directory path) ".")))
	 (base (file-name-nondirectory path))
	 (entries
	  (if (numberp kind)
	      (cons (if marked (list kind)
		      (if visible kind (gitsum-toggle-item kind)))
		    (cons desc contents))
	    (list (if marked (list kind)
		    (if visible kind (gitsum-toggle-item kind)))
		  contents)))
	 (entry (assoc dir data)))
    (if (null entry)
	(cons (cons dir
		    (list (cons base
				(list entries))))
	      data)
      (if entry
	  (let ((item (assoc base entry)))
	    (if item
		(nconc item (list entries))
	      (nconc entry
		     (list (cons base (list entries)))))))
      data)))

(defun gitsum-parse-changeset (&optional visible marked)
  "Return the changeset represented in the current buffer as a
Lisp changeset."
  (let ((limit (* 10 (count-lines (point-min) (point-max))))
	kind name moniker monikers-to-names data)
    (while (and (not (eobp)) (> limit 0))
      (setq limit (1- limit))
      (cond
       ((looking-at "\\? \\(.+?\\)\0")
	(goto-char (match-end 0))
	(setq kind 'newfile name (match-string 1)))
       ((looking-at ":\\([0-9]\\{6\\} \\)\\{2\\}\\(\\([0-9a-f]\\{7\\}\\.\\.\\. \\)\\{2\\}\\)\\([AM]\\)\0\\(.+?\\)\0")
	(goto-char (match-end 0))
	(setq kind (cond ((string= (match-string 4) "A") 'addfile)
			 ((string= (match-string 4) "M") 'replace))
	      name (match-string 5)
	      moniker (match-string 2))
	(if (eq kind 'addfile)
	    (setq data (gitsum-create-changeset data kind nil name
						visible marked))
	  (setq monikers-to-names (cons (cons moniker name)
					monikers-to-names))))
       ((looking-at "\0")
	(forward-char))
       ((looking-at "diff ")
	(forward-line)
	(when (looking-at "index \\([0-9a-f]+\\)\\.\\.\\([0-9a-f]+\\) [0-9]\\{6\\}")
	  (let ((name (cdr (or (assoc (concat (match-string 1) "... "
					      (match-string 2) "... ")
				      monikers-to-names)
			       (assoc (concat (match-string 1) "... "
					      "0000000... ")
				      monikers-to-names)))))
	    (assert name)
	    (while (and (not (eobp)) (> limit 0))
	      (setq limit (1- limit))
	      (forward-line)
	      (when (looking-at "@@ \\([0-9,+ -]+?,\\([0-9]+\\)\\) @@")
		(let ((start-line (string-to-number (match-string 2)))
		      (desc (match-string 1))
		      lines)
		  (forward-line)
		  (while (looking-at "^\\([+ -].*\\)")
		    (setq lines (cons (match-string 1) lines))
		    (forward-line))
		  (setq data (gitsum-create-changeset
			      data start-line desc name visible marked
			      (nreverse lines)))))))))
       (t
	(forward-line))))
    (assert (>= limit 0))
    (nreverse data)))

(defun gitsum-read-changeset (&optional visible)
  (let (changeset)
    ;; First, locate all the unknown files in the current working set
    (with-temp-buffer
      (call-process "git-ls-files" nil t nil
		    "--others" "--directory" "--no-empty-directory")
      (goto-char (point-min))
      (setq changeset (gitsum-parse-changeset visible)))

    ;; Then produce a patch of what we've done relative to the index cache
    ;; (These changes will appear non-bold).
    (with-temp-buffer
      (call-process "git-diff" nil t nil "--patch-with-raw" "-z")
      (goto-char (point-min))
      (setq changeset
	    (gitsum-add-changeset changeset
				  (gitsum-parse-changeset visible))))

    ;; Then produce a patch of what we've been staged in the index cache
    ;; (These changes will appear bold).
    (with-temp-buffer
      (call-process "git-diff" nil t nil "--patch-with-raw" "-z" "--cached")
      (goto-char (point-min))
      (setq changeset
	    (gitsum-add-changeset changeset
				  (gitsum-parse-changeset visible t))))
    changeset))

(defun gitsum-empty-db-p ()
  "Check if the git db is empty (no commit done yet)."
  (not (eq 0 (call-process "git" nil nil nil
			   "rev-parse" "--verify" "HEAD"))))

(defun gitsum-symbolic-ref (ref)
  "Wrapper for the gitsum-symbolic-ref command."
  (let ((str (with-temp-buffer
	       (call-process "git" nil t nil "symbolic-ref" ref)
	       (buffer-string))))
    (and str (car (split-string str "\n")))))

(defun gitsum-config (key)
  "Retrieve the value associated to KEY in the git repository config file."
  (let ((str (with-temp-buffer
	       (call-process "git" nil t nil "config" key)
	       (buffer-string))))
    (and str (car (split-string str "\n")))))

(defcustom gitsum-commits-coding-system nil
  "Default coding system for the log message of git commits."
  :group 'gitsum
  :type '(choice (const :tag "From repository config" nil)
                 (coding-system)))

(defun gitsum-get-logoutput-coding-system ()
  "Return the coding system used for gitsum-log output."
  (let ((repo-config (or (gitsum-config "i18n.logoutputencoding")
                         (gitsum-config "i18n.commitencoding"))))
    (or gitsum-commits-coding-system
        (and repo-config
             (fboundp 'locale-charset-to-coding-system)
             (locale-charset-to-coding-system repo-config))
	'utf-8)))

(defun gitsum-get-commit-description (commit &optional symbolic-ref)
  "Get a one-line description of COMMIT."
  (let ((coding-system-for-read (gitsum-get-logoutput-coding-system)))
    (let ((descr (with-temp-buffer
		   (call-process "git" nil t nil "log" "--max-count=1"
				 "--pretty=oneline" commit)
		   (buffer-string))))
      (if (and descr (string-match "\\`\\([0-9a-f]\\{40\\}\\) *\\(.*\\)$" descr))
          (concat (if symbolic-ref
		      (save-match-data
			(if (string-match "^refs/heads/" symbolic-ref)
			    (substring symbolic-ref (match-end 0))
			  symbolic-ref))
		    (substring (match-string 1 descr) 0 10))
		  " - " (match-string 2 descr))
        descr))))

(defun gitsum-get-merge-heads ()
  "Retrieve the merge heads from the MERGE_HEAD file if present."
  (let (heads)
    (when (file-readable-p ".git/MERGE_HEAD")
      (with-temp-buffer
        (insert-file-contents ".git/MERGE_HEAD" nil nil nil t)
        (goto-char (point-min))
        (while (re-search-forward "[0-9a-f]\\{40\\}" nil t)
          (push (match-string 0) heads))))
    (nreverse heads)))

(defun gitsum-display-changeset (data)
  "Display the changeset DATA using a pcl-cvs-like buffer."
  (erase-buffer)
  (let ((head (if (gitsum-empty-db-p) "Nothing committed yet"
		(gitsum-get-commit-description
		 "HEAD" (gitsum-symbolic-ref "HEAD"))))
	(merge-heads (gitsum-get-merge-heads)))
    (insert
     (format "Directory:  %s\nHead:       %s%s\n"
	     default-directory head
	     (if merge-heads
		 (concat "\nMerging:    "
			 (mapconcat #'gitsum-get-commit-description
				    merge-heads "\n\n            "))
	       "\n"))))
  (unless data
    (insert "There are no changes to review.\n"))
  (let (dir file change line beg)
    (dolist (dir data)
      (insert
       (gitsum-add-props
	(concat "    In directory "
		(gitsum-add-face (concat (car dir))
				 'gitsum-header-face t)
		":\n")
	'gitsum-line-type 'dir
	'gitsum-dir (car dir)))
      (dolist (file (cdr dir))
	(let* ((all-marked (listp (car (cadr file))))
	       (action (gitsum-change-item (cadr file)))
	       (status (gitsum-item-status action)))
	  (when (not status)
	    (setq all-marked t)
	    (dolist (change (cdr file))
	      (if (and all-marked
		       (not (listp (car change))))
		  (setq all-marked nil))))
	  (insert
	   (gitsum-add-props
	    (concat "          "
		    (if (and status (gitsum-item-visible-p action))
			(gitsum-add-face " * " 'gitsum-change-line-face t)
		      "   ")
		    " "
		    (gitsum-add-face (format "%-24s"
					     (if status status "Modified"))
				     (if all-marked
					 'gitsum-need-action-marked-face
				       'gitsum-need-action-face) t)
		    (gitsum-add-face (concat (car file))
				     'gitsum-filename-face t) "\n")
	    'gitsum-line-type 'file
	    'gitsum-dir (car dir)
	    'gitsum-file (car file)))
	  (dolist (change (if status nil (cdr file)))
	    (let ((item (gitsum-change-item change)))
	      (setq beg (point))
	      (cond
	       ((eq 'replace item)
		(insert (gitsum-add-face
			 "replace   "
			 'gitsum-change-line-face t)
			(format " %s" (cadr change))
			?\n)
		(add-text-properties beg (point)
				     (list 'gitsum-line-type 'change
					   'gitsum-dir (car dir)
					   'gitsum-file (car file)
					   'gitsum-change change)))
	       ((symbolp item)
		;; 'addfile 'newfile 'rmfile 'binary or '-replace
		;; xyzzy
		)
	       ((> item 0)
		(insert
		 (gitsum-add-face
		  (format "@@ %s @@" (cadr change))
		  'gitsum-change-line-face t))
		;; Avoid trailing whitespace here, so that we could use
		;; `show-trailing-whitespace' in Emacs, but make it
		;; display as space.  \000 is unlikely to be searched
		;; for.  NB "" as display property loses.
		(if (boundp 'show-trailing-whitespace)
		    (if (fboundp 'propertize)
			(insert (propertize "\000" 'display " "))))
		(insert ?\n)
		(dolist (line (cddr change))
		  (insert (if (not (listp (car change)))
			      line
			    (gitsum-add-face (concat line)
					     'gitsum-marked-face t))
			  ?\n))
		(add-text-properties beg (point)
				     (list 'gitsum-line-type 'change
					   'gitsum-dir (car dir)
					   'gitsum-file (car file)
					   'gitsum-change change))))))))))
  (insert "
--------------------- End ---------------------\n"))

;;; Code to determine the current changeset in gitsum-mode

(defun gitsum-changeset-at-point (&optional invisible-too)
  (let* ((type (get-text-property (point) 'gitsum-line-type))
	 (dir (get-text-property (point) 'gitsum-dir))
	 (dentry (and dir (assoc dir gitsum-data)))
	 data)
    (cond
     ((eq type 'dir)
      (setq data (list dentry)))
     ((eq type 'file)
      (let* ((file (get-text-property (point) 'gitsum-file))
	     (fentry (assoc file dentry)))
	(setq data (list (list (car dentry) fentry)))))
     ((eq type 'change)
      (let* ((file (get-text-property (point) 'gitsum-file))
	     (fentry (assoc file dentry)))
	(setq data (list
		    (list (car dentry)
			  (list (car fentry)
				(get-text-property (point)
						   'gitsum-change))))))))
    (if invisible-too
	data
      (gitsum-find-changeset data
			      (function
			       (lambda (dir file change)
				 (setq change (gitsum-change-item change))
				 (or (symbolp change) (>= change 0))))))))

(defun gitsum-mark-object-at-point (&optional invisible-too)
  (let* ((type (get-text-property (point) 'gitsum-line-type))
	 (dir (get-text-property (point) 'gitsum-dir))
	 (dentry (and dir (assoc dir gitsum-data)))
	 data)
    (cond
     ((eq type 'dir)
      (setq data (list dentry)))
     ((eq type 'file)
      (let* ((file (get-text-property (point) 'gitsum-file))
	     (fentry (assoc file dentry)))
	(setq data (list (list (car dentry) fentry)))))
     ((eq type 'change)
      (let* ((file (get-text-property (point) 'gitsum-file))
	     (fentry (assoc file dentry)))
	(setq data (list
		    (list (car dentry)
			  (list (car fentry)
				(get-text-property (point)
						   'gitsum-change))))))))))

(defun gitsum-selected-changeset (&optional all-visible)
  "Return the currently selected changeset.

If marks are active, always returned the marked changes.
Otherwise, return the changes related to point, unless ALL-VISIBLE is
non-nil, in which case return all visible changes."
  (cond
   ((gitsum-marked-p gitsum-data)
    (gitsum-find-changeset gitsum-data
			    (function
			     (lambda (dir file change)
			       (listp (car change))))))
   (all-visible
    (gitsum-find-changeset gitsum-data
			    (function
			     (lambda (dir file change)
			       (equal (gitsum-visible-item (car change))
				      (car change))))))
   (t
    (gitsum-changeset-at-point))))

;;; Code to record the current changeset

;; If there are any marked changes, these are what get recorded.
;; Otherwise, all *visible* changes are recorded.

(defcustom gitsum-program "git"
  "*The program name which gitsum will use to produce patch sets."
  :type 'string
  :group 'gitsum)

(defcustom gitsum-stg-program "stg"
  "*The program name which gitsum will use to talk to Stacked Git."
  :type 'string
  :group 'gitsum)

(defcustom gitsum-default-expanded nil
  "*Non-nil means the *gitsum* buffer will be expanded by default."
  :type 'boolean
  :group 'gitsum)

(defvar gitsum-process-arg nil)
(defvar gitsum-parent-buffer nil)
(defvar gitsum-changeset-to-record nil)
(defvar gitsum-logfile)

(defvar gitsum-window-configuration-temp nil)

(defsubst gitsum-remember-window-configuration ()
  (setq gitsum-window-configuration-temp (list (current-window-configuration)
					   (point-marker))))
(defsubst gitsum-recall-window-configuration ()
  (if gitsum-window-configuration-temp
      (progn
	 (set-window-configuration (car gitsum-window-configuration-temp))
	 (goto-char (cadr gitsum-window-configuration-temp)))
    (error "No window configuration to restore.")))

(defsubst gitsum-changes-handled ()
  (if (buffer-live-p gitsum-parent-buffer)
      (let ((changeset gitsum-changeset-to-record))
	(with-current-buffer gitsum-parent-buffer
	  (setq gitsum-data
		(gitsum-remove-changeset gitsum-data changeset))
	  (gitsum-refresh)))))

(defun gitsum-start-process (subcommand args
					 &optional name value &rest localize)
  "Start Git process."
    (let*
	((buf (generate-new-buffer (format " *git-%s*" subcommand)))
	 (process-environment
	    ;; Use the environment variables to turn off highlighting.  (You
	    ;; could use `show-trailing-whitespace' in the buffer to highlight
	    ;; trailing space in the diffs.)
	    (append (list "DARCS_DONT_ESCAPE_TRAILING_SPACES=1"
			  "DARCS_DONT_COLOR=1"
			  "DARCS_DONT_ESCAPE_TRAILING_CR=1")
		    process-environment))
	 (process-connection-type nil)
	 (proc (apply 'start-process "git"
		      buf gitsum-program subcommand args)))
      (set-process-sentinel proc 'gitsum-process-sentinel)
      (set-process-filter proc 'gitsum-process-filter)
      (with-current-buffer buf
	(while name
	  (set (make-local-variable name) value)
	  (setq name (car localize)
		value (cadr localize)
		localize (cddr localize))))
      proc))

(defun gitsum-process-sentinel (proc string)
  (cond
   ((and (string-match "^exited abnormally" string) (process-buffer proc))
    (message string))))

(defun gitsum-process-filter (proc string)
  (with-current-buffer (process-buffer proc)
    (let ((moving (= (point) (process-mark proc))))
      (save-excursion
	;; Insert the text, advancing the process marker.
	(goto-char (process-mark proc))
	(insert string)
	(set-marker (process-mark proc) (point)))
      (if moving (goto-char (process-mark proc))))
    (save-excursion
      (goto-char (point-min))
      (cond
       ((looking-at "\n*Finished \\(recording\\|amending\\) patch")
	(message "Changes recorded.")
	(gitsum-changes-handled)
        (when gitsum-logfile (delete-file gitsum-logfile))
	(kill-buffer (current-buffer)))
       ((looking-at "\n*Ok, if you don't want to \\(record\\|amend\\) anything")
	(message "No changes recorded.")
        (when gitsum-logfile (delete-file gitsum-logfile))
	(kill-buffer (current-buffer)))

       ((looking-at "\n*What is the target email address")
	(process-send-string proc gitsum-process-arg)
	(delete-region (point-min) (point-max)))
       ((looking-at "\n*Successfully sent patch bundle")
	(message "Changes sent to `%s'." gitsum-process-arg)
	(kill-buffer (current-buffer)))
       ((looking-at "\n*You don't want to send any patches")
	(message "No changes sent.")
	(kill-buffer (current-buffer)))

       ((looking-at "\n*Do you really want to .+\\? ") ;; Should the last whitespace be there?
	(process-send-string proc "y\n")
	(delete-region (point-min) (point-max)))
       ((looking-at "\n*Finished reverting.")
	(message "Changes reverted.")
	(gitsum-changes-handled)
	(kill-buffer (current-buffer)))
       ((looking-at "\n*If you don't want to revert")
	(message "No changes reverted.")
	(kill-buffer (current-buffer)))

       ((looking-at "\n*\\(Waiting for lock.*\\)\n+")
	(let ((waiting (match-string 1)))
	  (message waiting)
	  (delete-region (point-min) (match-end 0))))

       ((looking-at "\n*\\(Couldn't get lock.*\\)\n*")
	(let ((waiting (match-string 1)))
	  (message waiting)
	  (kill-buffer (current-buffer))))

       ((looking-at "\\(.*\n\\)*Shall I amend this patch\\?.*")
        (process-send-string proc "y")
        (delete-region (point-min) (match-end 0)))

       ((looking-at "\n*Git needs to know what name")
	(let* ((default-mail (concat user-full-name
				     " <" user-mail-address ">"))
	       (enable-recursive-minibuffers t)
	       (mail-address (read-string
			      (format
			       "What is your email address? (default %s) "
			       default-mail)
			      nil nil default-mail)))
	  (process-send-string proc mail-address)
	  (process-send-string proc "\n"))
	(re-search-forward "What is your email address\\?.*")
	(delete-region (point-min) (point)))

       ((looking-at "diff --git a/\\(.+?\\) b/.+$")
	(let* ((kind (intern (match-string 1)))
	       (file (match-string 2))
	       (dir (directory-file-name
		     (file-name-directory file)))
	       (base (file-name-nondirectory file))
	       (start-line (match-string 4))
	       (replace (match-string 6)))
	  (goto-char (match-end 0))
	  (forward-line)
	  (while (looking-at "^\\([+ -].*\\)")
	    (forward-line))
	  ;; jww (2008-04-16): Ugh, this needs to be made to work.  I've just
	  ;; lost my gumption for it today, though.
	  (when (looking-at "^Stage this hunk \\[y/n/a/d\\?\\]\\? ")
	    (if (eq kind 'hunk) (setq kind (string-to-number start-line)))
	    (let ((end (match-end 0))
		  (record (gitsum-changeset-has-change-p
			   gitsum-changeset-to-record
			   dir base kind replace)))
	      (process-send-string proc (if record "y" "n"))
	      (delete-region (point-min) end)))))

       ((looking-at "\n*\\(move\\).+")
	(goto-char (match-end 0))
	(forward-line)
	(when (looking-at
	       "^Shall I \\(record\\|send\\|revert\\|add\\) this \\(patch\\|change\\)\\?.+[]:] ")
	  (let ((end (match-end 0)))
	    (process-send-string proc "n")
	    (delete-region (point-min) end))))))))

(defun gitsum-really-record ()
  (interactive)
  (let ((tempfile (gitsum-make-temp-file "gitsum"))
	(parent-buf gitsum-parent-buffer)
	(changeset gitsum-changeset-to-record))
    (save-excursion
      (goto-char (point-max))
      (unless (bolp)
	(insert ?\n))
      (goto-char (point-min))
      (when (looking-at "^\\s-*$")
	(error "No record description entered")))
    (write-region (point-min) (point-max) tempfile)
    (kill-buffer (current-buffer))
    (gitsum-recall-window-configuration)
    (message "Recording changes...")
    (call-process "git" nil nil nil
		  "commit" (list "-F" tempfile))
    (gitsum-redo)))

(defun gitsum-record ()
  "Record selected changeset.
Note that only changes selected for recording are actually recorded.
If some changes are marked \(with \
\\<gitsum-mode-map>\\[gitsum-toggle-mark]\), \
then only those changes are recorded.
Otherwise, only changes which are selected to be displayed in the buffer
\(with \\<gitsum-mode-map>\\[gitsum-toggle]\) are recorded."
  (interactive)
  (gitsum-remember-window-configuration)
  (let ((parent-buf (current-buffer))
	(changeset (gitsum-selected-changeset t))
        (buf (get-buffer-create "*git comment*")))
    (switch-to-buffer-other-window buf)
    (gitsum-comment-mode)
    (set (make-local-variable 'gitsum-changeset-to-record) changeset)
    (set (make-local-variable 'gitsum-parent-buffer) parent-buf)
    (message
     "Title of change on first line, long comment after.  \
C-c C-c to commit.")
    (run-hooks 'gitsum-comment-hook)))

(defun gitsum-send (recipient)
  "Send selected changeset via email."
  (interactive "sSend changes to: ")
  (message "Sending changes...")
  (gitsum-start-process
   "send" (list)
   'gitsum-changeset-to-record (gitsum-selected-changeset t)
   'gitsum-parent-buffer (current-buffer)
   'gitsum-process-arg recipient))

(defun gitsum-changes (&optional how-many)
  "Show the changes in another buffer"
  (interactive "P")
  (let ((proc (gitsum-start-process
	       "changes" (if how-many
                             (list "--last" (number-to-string how-many))
                             (list))
	       'gitsum-parent-buffer (current-buffer))))
    (set-process-filter proc nil)
    (set-process-sentinel proc 'gitsum-changes-sentinel)
    (switch-to-buffer-other-window (process-buffer proc))
    (process-buffer proc)))

(defun gitsum-changes-sentinel (process event)
  (with-current-buffer (process-buffer process)
    (goto-char (point-min))))

(defun gitsum-query-manifest ()
  "List the version-controlled files in the working copy."
  (interactive)
  (let ((proc (gitsum-start-process
	       "query" '("manifest")
	       'gitsum-parent-buffer (current-buffer))))
    (set-process-filter proc nil)
    (set-process-sentinel proc 'gitsum-query-manifest-sentinel)
    (switch-to-buffer-other-window (process-buffer proc))
    (process-buffer proc)))

(defun gitsum-query-manifest-sentinel (process event)
  (with-current-buffer (process-buffer process)
    (setq buffer-read-only t)
    (gitsum-query-mode)
    (goto-char (point-min))))

(defun gitsum-amend ()
  "Amend last patch with selected changeset."
  (interactive)
  (let ((changeset (gitsum-selected-changeset t))
        (parent-buffer (current-buffer)))
    (if (> (length changeset) 0)
	(let ((history-buffer (gitsum-changes 1)))
          (with-current-buffer history-buffer
            (save-excursion 
	      (goto-char (point-max))
	      (insert "
WARNINGS: You should ONLY use git-commit --amend on patches which only exist in a single repository!
Also, running amend while another user is pulling from the same repository may cause repository corruption."))
            (sleep-for 2)
            (goto-char (point-min)))
	  (kill-buffer history-buffer)
	  (let ((amend (yes-or-no-p "Amend this latest changeset? (see WARNINGS) ")))
	    (when amend
	      (call-process "git" nil nil nil "reset" "--soft" "HEAD^")
	      (call-process "git" nil nil nil "commit" "-c" "ORIG_HEAD"))))
      (message "You need to select something first"))))

(defun gitsum-revert ()
  "Revert selected changeset."
  (interactive)
  (when (yes-or-no-p "Really revert these changes? ")
    (message "Reverting changes...")
    (gitsum-start-process
     "revert" (list)
     'gitsum-changeset-to-record (gitsum-selected-changeset t)
     'gitsum-parent-buffer (current-buffer))))

;;;;;;;; TODO: history of previous record comments, like in vc-mode
(defvar gitsum-comment-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-x\C-s" 'gitsum-really-record)
    (define-key map "\C-c\C-c" 'gitsum-really-record)
    map))

(defun gitsum-query-kill-buffer ()
  (interactive)
  (kill-this-buffer)
  (delete-window))

(defvar gitsum-query-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "q" 'gitsum-query-kill-buffer)
    map))

(define-derived-mode gitsum-comment-mode indented-text-mode "Git Summary"
  "Major mode for output from \\<gitsum-mode-map>\\[gitsum-comment].

\\{gitsum-comment-mode-map}"
  :group 'gitsum
  (setq truncate-lines t))

(define-derived-mode gitsum-query-mode indented-text-mode "Git Query"
  "Major mode for output from \\<gitsum-mode-map>\\[gitsum-query].

\\{gitsum-query-mode-map}"
  :group 'gitsum
  (setq truncate-lines t))

;;; Major Mode

(defun gitsum-check-gitsum-mode ()
  (unless (eq major-mode 'gitsum-mode)
    (error "Not in a gitsum-mode")))

(defun gitsum-reposition ()
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir)
      (goto-char (+ (line-beginning-position) 13)))
     ((eq type 'file)
      (goto-char (+ (line-beginning-position) 38)))
     ((eq type 'change)
      (goto-char (line-beginning-position))))))

(defsubst gitsum-other-buffer (other-buffer)
  (let ((buf (or other-buffer (generate-new-buffer "*git*"))))
    (with-current-buffer buf
      (unless (eq major-mode 'gitsum-mode)
	(gitsum-mode))
      (current-buffer))))

(defun gitsum-move (other-buffer)
  "Move the selected changeset to another gitsum buffer OTHER-BUFFER.

In interactive mode, prompts for the name of a buffer to move the changeset to.

Changesets may be moved around in different buffers, to ease
the collection of changes to record in a single Git patch."
  (interactive "BMove change to (RET creates new patch): ")
  (let ((buf (gitsum-other-buffer other-buffer))
	(changeset (gitsum-selected-changeset))
	(inhibit-redisplay t))
    (setq gitsum-data
	  (gitsum-remove-changeset gitsum-data changeset))
    (with-current-buffer buf
      (gitsum-apply-to-changeset
       changeset
       (function
	(lambda (dir file change)
	  (cond
	   ((listp (car change))
	    (setcar change (caar change)))
	   ((not (equal (car change) (gitsum-visible-item (car change))))
	    (setcar change (gitsum-visible-item (car change))))))))
      (setq gitsum-data
	    (gitsum-add-changeset gitsum-data changeset))
      (gitsum-refresh)))
  (gitsum-refresh))

(defun gitsum-find-file (e &optional other view)
  "Open the selected entry.
With a prefix OTHER, open the buffer in another window.
VIEW non-nil means open in View mode."
  (interactive (list last-input-event current-prefix-arg))
  (let* ((type (get-text-property (point) 'gitsum-line-type))
	 (file (if (eq 'type 'dir)
		   (get-text-property (point) 'gitsum-dir)
		 (gitsum-path (point)))))
    (cond
     ((eq type 'dir)
      (find-file (get-text-property (point) 'gitsum-dir)))
     ((eq type 'file)
      (cond ((eq other 'dont-select)
	     (display-buffer (find-file-noselect file)))
	    ((and other view)
	     (view-file-other-window file))
	    (view (view-file file))
	    (other (find-file-other-window file))
	    (t (find-file file))))
     ((eq type 'change)
      (let ((change-line (car (get-text-property (point) 'gitsum-change))))
	(with-current-buffer (cond ((eq other 'dont-select)
				    (display-buffer (find-file-noselect file)))
				   ((and other view)
				    (view-file-other-window file))
				   (view (view-file file))
				   (other (find-file-other-window file))
				   (t (find-file file)))
	  (if (listp change-line)
	      (setq change-line (car change-line)))
	  (goto-line (abs change-line))))))))

(defun gitsum-find-file-other-window (e)
  "Select a buffer containing the file in another window."
  (interactive (list last-input-event))
  (gitsum-find-file e t))

(defun gitsum-goto ()
  "Open the selected entry, possibly moving point to the change's location."
  (interactive)
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir)
      (find-file-other-window
       (get-text-property (point) 'gitsum-dir)))
     ((eq type 'file)
      (find-file-other-window (gitsum-path (point))))
     ((eq type 'change)
      (let ((change-line (car (get-text-property (point) 'gitsum-change))))
	(find-file-other-window (gitsum-path (point)))
	(if (listp change-line)
	    (setq change-line (car change-line)))
	(goto-line (abs change-line)))))))

(defun gitsum-toggle-context ()
  (interactive)
  (gitsum-check-gitsum-mode)
  (setq gitsum-show-context (not gitsum-show-context))
  (let ((dir default-directory)
	(gitsum-default-expanded t))
    (message "Re-running gitsum")
    (let ((changes (gitsum dir nil t gitsum-show-context)))
      (setq gitsum-data changes))
    (gitsum-refresh)))

(defun gitsum-toggle-mark ()
  "Toggle mark on current changeset.

Marked changesets have priority over simply activated ones regarding
the selection of changesets to commit."
  (interactive)
  (gitsum-check-gitsum-mode)
  (let ((changeset (gitsum-changeset-at-point t)))
    (gitsum-apply-to-changeset changeset
				(function
				 (lambda (dir file change)
				   (if (listp (car change))
				       (setcar change (caar change))
				     (setcar change (list (car change))))))))
  (gitsum-refresh))

(defun gitsum-toggle ()
  "Toggle the activation of the current changeset.

The activation of a changeset exposes the associated change, and selects
it for later commit."
  (interactive)
  (gitsum-check-gitsum-mode)
  ;;;;;;;; TODO: easier to expose a hunk which was made invisible by mistake
  (let ((changeset (gitsum-changeset-at-point t)))
    (let ((any-visible
	   (gitsum-applicable-p
	    changeset
	    (function
	     (lambda (d f change)
	       (gitsum-item-visible-p (gitsum-change-item change)))))))
	(gitsum-apply-to-changeset
	 changeset
	 (function
	  (lambda (dir file change)
	    (let ((item (gitsum-change-item change)))
	      (if any-visible
		  (setcar change (gitsum-invisible-item item))
		(if (listp (car change))
		    (setcar change (list (gitsum-visible-item item)))
		  (setcar change (gitsum-visible-item item))))))))))
  (gitsum-refresh))

(defun gitsum-refresh ()
  "Refresh the visualization of the changesets."
  (interactive)
  (gitsum-check-gitsum-mode)
  (let ((line (count-lines (point-min) (point)))
	(inhibit-redisplay t))
    (if (/= (point) (line-beginning-position))
	(setq line (1- line)))
    (gitsum-display-changeset gitsum-data)
    (goto-char (point-min))
    (forward-line line)
    (gitsum-reposition)))

(defun gitsum-line-is (sort)
  (save-excursion
    (beginning-of-line)
    (let ((type (get-text-property (point) 'gitsum-line-type)))
      (case sort
	('new (and (eq 'file type) (looking-at "  +New")))
	('modified (or (and (eq 'file type) (looking-at "\\s-+Modified"))
		       (eq 'change type)))
	('file (eq 'file type))
	('change (eq 'change type))
	('marked
	 (memq (get-text-property (point) 'face)
	       '(gitsum-marked-face gitsum-need-action-marked-face)))))))

(defun gitsum-next-entity (&optional arg backward)
  "Move to the next file or change.
With ARG, move that many times.
BACKWARD non-nil means to go backwards."
  (interactive "p")
  (dotimes (i (or arg 1))
    (forward-line (if backward -1))
    (beginning-of-line)
    (while (and (not (if backward (bobp) (eobp)))
		(not (looking-at "[0-9]")) ; stop at line headers
		(gitsum-line-is 'change))
      (forward-line (if backward -1 1)))
    (unless (get-text-property (point) 'gitsum-line-type)
      (goto-char (if backward (point-max) (point-min)))
      (forward-line (if backward -3 3)))
    (gitsum-reposition)))

(defun gitsum-next-line (&optional arg)
  "Move to the next file or change.
With ARG, move that many times."
  (interactive "p")
  (gitsum-next-entity arg))

(defun gitsum-previous-line (&optional arg)
  "Move to the previous file or change.
With ARG, move that many times."
  (interactive "p")
  (gitsum-next-entity arg t))

(defun gitsum-original-path (pos)
  (let ((file (get-text-property pos 'gitsum-file))
	(dir (get-text-property pos 'gitsum-dir)))
    (let ((path (expand-file-name	; new-style
		 file (file-name-as-directory
		       (expand-file-name dir "_darcs/pristine")))))
      (if (file-readable-p path)
	  path
	(let ((path (expand-file-name	; old-style
		     file (file-name-as-directory
			   (expand-file-name dir "_darcs/current")))))
	  (if (file-readable-p path)
	      path))))))

(defun gitsum-path (pos)
  (expand-file-name (get-text-property pos 'gitsum-file)
		    (file-name-as-directory
		     (get-text-property pos 'gitsum-dir))))

(defcustom gitsum-diff-switches nil
  "*diff(1) switches used by `gitsum-diff'."
  :type 'string
  :group 'gitsum)

(defun gitsum-diff ()
  "Show the changes made to current selection."
  (interactive)
  (if (not (gitsum-original-path (point)))
      (error "No record of this file in Git"))
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir))
     ((or (eq type 'file)
	  (eq type 'change))
      (require 'diff)			; for `diff-switches'
      (diff (gitsum-original-path (point))
	    (gitsum-path (point))
	    (or gitsum-diff-switches diff-switches))))))

(defun gitsum-delete ()
  "Remove selected changeset from the view."
  (interactive)
  (setq gitsum-data
	(gitsum-remove-changeset gitsum-data
				  (gitsum-selected-changeset)))
  (gitsum-refresh))

(defun gitsum-remove ()
  "Remove a file from the repository."
  (interactive)
  (gitsum-check-gitsum-mode)
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir)
      (error "Cannot remove whole directories yet; try file by file for now"))
     ((memq type '(file change))
      (let* ((dir (get-text-property (point) 'gitsum-dir))
	     (dentry (and dir (assoc dir gitsum-data)))
	     (file (get-text-property (point) 'gitsum-file))
	     (fentry (assoc file dentry))
	     (sym (gitsum-change-item (cadr fentry)))
	     file-to-remove)
	(cond
	 ((not (symbolp sym))
	  (when (yes-or-no-p
		 (format "Really delete file with changes `%s'? " file))
	    (delete-file (expand-file-name file dir))
	    (setq file-to-remove file)))
	 ((eq sym 'newfile)
	  (delete-file (expand-file-name file dir)))
	 ((eq sym 'addfile)
	  (setq file-to-remove file)
	  (delete-file (expand-file-name file dir)))
	 (t
	  (error "Removing makes no sense for that entry")))
	(if file-to-remove
	    (with-temp-buffer
	      (cd (expand-file-name dir))
	      (if (/= 0 (call-process gitsum-program nil t nil
				      "remove" file-to-remove))
		  (error "Error running `gitsum remove'"))))))))
  (gitsum-redo))

(defun gitsum-add ()
  "Put new file or directory under Git control."
  (interactive)
  (gitsum-check-gitsum-mode)
  (dolist (dir (gitsum-selected-changeset))
    (dolist (file (cdr dir))
      (let ((item (gitsum-change-item (cadr file))))
	(if (and (symbolp item) (eq item 'newfile))
	    (progn
	      (setcar (cadr file) 'addfile)
	      (with-temp-buffer
		(cd (expand-file-name (car dir)))
		(if (/= 0 (call-process gitsum-program nil t nil
					"add" (car file)))
		    (error "Error running `gitsum add' for `%s' in dir `%s'"
			   (car file) (car dir)))))
	  (error "Can only add New entries for `%s' in dir `%s'"
		 (car file) (car dir))))))
  (gitsum-refresh))

(defun gitsum-add-to-boring (path)
  "Add current file or directory to the boring file.

Propose the insertion of a regexp suitable to permanently ignore
the file or the directory at point into the boring file."
  (interactive
   (let ((type (get-text-property (point) 'gitsum-line-type)))
     (cond
      ((eq type 'dir)
       (setq path (get-text-property (point) 'gitsum-dir))
       (if (string-match "^\\./" path)
	   (setq path (substring path 2)))
       (setq path (concat "(^|/)" (regexp-quote path) "($|/)")))
      ((memq type '(file change))
       (setq path (get-text-property (point) 'gitsum-file))
       (setq path (concat "(^|/)" path "$"))))
     (list (read-string "Add to boring list: " path))))
  (save-excursion
    (set-buffer (find-file-noselect "_darcs/prefs/boring"))
    (goto-char (point-max))
    (insert path ?\n)
    (save-buffer)
    (kill-buffer (current-buffer)))
  (gitsum-redo))

(defun gitsum-add-change-log-entry ()
  "Execute `add-change-log-entry' on the current file."
  (interactive)
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir))
     ((or (eq type 'file)
	  (eq type 'change))
      (gitsum-goto)
      (add-change-log-entry)))))

(defun gitsum-ediff ()
  "Like `gitsum-diff' but in an Ediff session."
  (interactive)
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir))
     ((or (eq type 'file)
	  (eq type 'change))
      (let ( (pristine-filename (gitsum-original-path (point)))
	     (working-filename (gitsum-path (point)))
	     (old-window-configuration (current-window-configuration)) ;;Save the current window configuration, before opening ediff
	     )
      (progn
	(save-excursion
	  (find-file-read-only pristine-filename) ;;Pristine copy should not be modified
	  (rename-buffer (concat "*gitsum-pristine:" pristine-filename "*")) ;;It should be clear this is not a buffer you want to touch.
	  )
	(ediff pristine-filename working-filename
	       ;;Add this anonymous function as a startup hook in ediff-mode
	       (lambda () (progn
			    (make-variable-buffer-local 'pre-gitsum-ediff-window-configuration) ;;make buffer-local variable storing old window configuration, since "let" bindings die before ediff buffers are killed
			    (setq pre-gitsum-ediff-window-configuration old-window-configuration)
			    (make-local-hook 'ediff-quit-hook) ;;After we quit THIS PARTICULAR ediff buffer, restore the old window configuration
			    (add-hook 'ediff-quit-hook (lambda () (set-window-configuration pre-gitsum-ediff-window-configuration)))
			    )))
	))))))

(defun gitsum-ediff-merge ()
  "Start an `ediff-merge' session on the current selection."
  (interactive)
  (let ((type (get-text-property (point) 'gitsum-line-type)))
    (cond
     ((eq type 'dir))
     ((or (eq type 'file)
	  (eq type 'change))
      (ediff-merge (gitsum-original-path (point))
		   (gitsum-path (point)))))))

(defun gitsum-redo (&optional arg)
  "Refresh the status, redoing `git-status'."
  (interactive "P")
  (gitsum-check-gitsum-mode)
  (let ((dir default-directory)
	(look-for-adds (or arg gitsum-look-for-adds))
	(gitsum-default-expanded t))
    (message "Re-running gitsum")
    (let ((changes (gitsum
		    dir look-for-adds t gitsum-show-context)))
      (setq gitsum-data
	    (gitsum-merge-changeset gitsum-data changes)))
    (gitsum-refresh)))

(defun gitsum-quit ()
  "Close the gitsum buffer and quit."
  (interactive)
  (gitsum-check-gitsum-mode)
  (kill-buffer (current-buffer)))


(defun gitsum-add-comment ()
  "Similar to `add-change-log-entry'.

Inserts the entry in the Git comment file instead of the ChangeLog."
  ;; This is mostly copied from add-log.el and Xtla.  Perhaps it would
  ;; be better to split add-change-log-entry into several functions
  ;; and then use them, but that wouldn't work with older versions of
  ;; Emacs.
  (interactive)
  (require 'add-log)
  (let* ((defun (add-log-current-defun))
         (buf-file-name (if (and (boundp 'add-log-buffer-file-name-function)
                                 add-log-buffer-file-name-function)
                            (funcall add-log-buffer-file-name-function)
                          buffer-file-name))
         (buffer-file (if buf-file-name (expand-file-name buf-file-name)))
;         (file-name (tla-make-log))
         ;; Set ENTRY to the file name to use in the new entry.
         (entry (add-log-file-name buffer-file default-directory))
         beg
         bound
         narrowing)
    (switch-to-buffer-other-window (get-buffer-create "*git comment*"))

    (goto-char (point-min))
    (forward-line 1)			; skip header
    ;; Now insert the new line for this entry.
    (cond ((re-search-forward "^\\s *\\*\\s *$" bound t)
           ;; Put this file name into the existing empty entry.
           (if entry
               (insert entry)))
          ((let (case-fold-search)
             (re-search-forward
              (concat (regexp-quote (concat "* " entry))
                      ;; Don't accept `foo.bar' when
                      ;; looking for `foo':
                      "\\(\\s \\|[(),:]\\)")
              bound t))
           ;; Add to the existing entry for the same file.
           (re-search-forward "^\\s *$\\|^\\s \\*\\|\\'")
           (goto-char (match-beginning 0))
           ;; Delete excess empty lines; make just 2.
           (while (and (not (eobp)) (looking-at "^\\s *$"))
             (delete-region (point) (line-beginning-position 2)))
           (insert-char ?\n 2)
           (forward-line -2)
           (indent-relative-maybe))
          (t
           ;; Make a new entry.
	   (goto-char (point-max))
	   (re-search-backward "^." nil t)
	   (end-of-line)
	   (insert "\n* ")
	   (if entry (insert entry))))
    ;; Now insert the function name, if we have one.
    ;; Point is at the entry for this file,
    ;; either at the end of the line or at the first blank line.
    (if defun
        (progn
          ;; Make it easy to get rid of the function name.
          (undo-boundary)
          (unless (save-excursion
                    (beginning-of-line 1)
                    (looking-at "\\s *$"))
            (insert ?\ ))
          ;; See if the prev function name has a message yet or not
          ;; If not, merge the two entries.
          (let ((pos (point-marker)))
            (if (and (skip-syntax-backward " ")
                     (skip-chars-backward "):")
                     (looking-at "):")
                     (progn (delete-region (+ 1 (point)) (+ 2 (point))) t)
                     (> fill-column (+ (current-column) (length defun) 3)))
                (progn (delete-region (point) pos)
                       (insert ", "))
              (goto-char pos)
              (insert "("))
            (set-marker pos nil))
          (insert defun "): "))
      ;; No function name, so put in a colon unless we have just a star.
      (unless (save-excursion
                (beginning-of-line 1)
                (looking-at "\\s *\\(\\*\\s *\\)?$"))
        (insert ": ")))))

(defvar gitsum-mode-abbrev-table nil
  "Abbrev table used while in gitsum-mode mode.")
(define-abbrev-table 'gitsum-mode-abbrev-table ())

(global-set-key "\C-xD" 'gitsum-add-comment)

(defvar gitsum-mode-map
  (let ((map (make-sparse-keymap)))
    (suppress-keymap map)
    (define-key map [return] 'gitsum-toggle) ; ??
    (define-key map "\C-m" 'gitsum-toggle)
    (define-key map "\C-c\C-c" 'gitsum-goto)
    (define-key map [tab] 'gitsum-next-entity)
    (define-key map "?" 'describe-mode)
    (define-key map "f" 'gitsum-find-file)
    (define-key map "=" 'gitsum-diff)
    (define-key map "e" 'gitsum-ediff)
    (define-key map "E" 'gitsum-ediff-merge)
    (define-key map "g" 'gitsum-redo)
    (define-key map "n" 'gitsum-next-line)
    (define-key map "p" 'gitsum-previous-line)
    (define-key map "a" 'gitsum-add)
    (define-key map "l" 'gitsum-add-change-log-entry)
    (define-key map "c" 'gitsum-record)
    (define-key map "R" 'gitsum-record)
    (define-key map "U" 'gitsum-revert)
    (define-key map "u" 'gitsum-toggle-context)
    (define-key map "d" 'gitsum-delete)
    ;; (define-key map "r" 'gitsum-remove)
    (define-key map "M" 'gitsum-move)
    (define-key map "m" 'gitsum-toggle-mark)
    (define-key map "i" 'gitsum-add-to-boring)
    (define-key map "B" 'gitsum-add-to-boring)
    (define-key map "q" 'gitsum-quit)
    map))

(easy-menu-define gitsum-menu gitsum-mode-map "Menu used in `gitsum-mode'."
  '("Git summary"
    ["Open file.."		gitsum-find-file
				(or (gitsum-line-is 'file)
				    (gitsum-line-is 'change))]
    [" ..other window"		gitsum-find-file-other-window
				(or (gitsum-line-is 'file)
				    (gitsum-line-is 'change))]
    ["Display in other window"  gitsum-display-file	t]
    ("Differences"
     ["Interactive diff"	gitsum-ediff		t]
     ["Current diff"		gitsum-diff		t]
     ["Interactive merge"	gitsum-ediff-merge	t])
;;     ["View log"			gitsum-log		t]
    "--"
    ["Re-examine"		gitsum-redo		t]
    ["Record changes"		gitsum-record		t] ; fixme: condition
    ["Amend last changeset"	gitsum-amend		t] ; fixme: condition
;;     ["Tag"			gitsum-tag		t]
    ["Undo changes"		gitsum-revert		t] ; fixme: condition
    ["Add"			gitsum-add		(gitsum-line-is 'new)]
    ["Remove"			gitsum-remove		(gitsum-line-is 'file)]
    ["Ignore"			gitsum-add-to-boring	(gitsum-line-is 'file)]
    ["Add ChangeLog"		gitsum-add-change-log-entry t]
    ["Delete"			gitsum-delete		t]
    "--"
    ["(Un)activate change"	gitsum-toggle		t]
    ["(Un)mark change"		gitsum-toggle-mark
				:style toggle
				:selected (gitsum-line-is 'marked)]
    ["Next file/change"		gitsum-next-line	t]
    ["Previous file/change"	gitsum-previous-line	t]
    ["Move changeset"		gitsum-move		t]
    ["Show change context"	gitsum-toggle-context
				:style toggle :selected gitsum-show-context]
    "--"
    ["Quit"			gitsum-quit		t]
    ))

(define-derived-mode gitsum-mode fundamental-mode "Git"
  "Git summary mode is for previewing changes to become part of a patch.
\\{gitsum-mode-map}"
  :group 'gitsum
  (if (featurep 'xemacs)
      (easy-menu-add gitsum-menu gitsum-mode-map)))

(put 'gitsum-mode 'mode-class 'special)

(custom-add-option 'gitsum-mode-hook
		   '(lambda ()	    ; Should be a minor mode for this!
		      "Show trailing whitespace in changes."
		      (setq show-trailing-whitespace t)))

;;; This is the entry code, M-x gitsum

(defun gitsum-display (data &optional look-for-adds)
  (with-current-buffer (generate-new-buffer "*git*")
    (gitsum-mode)
    (set (make-local-variable 'gitsum-data) data)
    (set (make-local-variable 'gitsum-look-for-adds) look-for-adds)
    (set (make-local-variable 'gitsum-show-context) nil)
    (gitsum-refresh)
    (goto-char (point-min))
    (forward-line 3)
    (gitsum-reposition)
    (switch-to-buffer (current-buffer))))

(defun gitsum-repository-root (&optional start-directory)
  "Return the root of the repository, or nil if there isn't one."
  (let ((dir (or start-directory
                 default-directory
                 (error "No start directory given"))))
    (if (car (directory-files dir t "^\\.git$"))
        dir
      (let ((next-dir (file-name-directory (directory-file-name
                                            (file-truename dir)))))
        (unless (or (equal dir next-dir) (null next-dir))
          (gitsum-repository-root next-dir))))))

(defcustom gitsum-switches nil
  "*Switches for `gitsum'."
  :type 'string
  :group 'gitsum)

(defcustom gitsum-at-toplevel t
  "*Use top-level repository directory as default argument to \
`gitsum'."
  :type 'boolean
  :group 'gitsum)

;;;###autoload
(defun gitsum (directory &optional look-for-adds no-display show-context)
  "Run `git-status' in DIRECTORY, displaying the output in `gitsum-mode'.

When invoked interactively, prompt for the directory to display changes for."
  (interactive
   ; fancy "DDirectory: \nP"
   (let ((root
	  (if gitsum-at-toplevel
	      (gitsum-repository-root)
	    default-directory)))
     (list (funcall (if (fboundp 'read-directory-name)
			'read-directory-name
		      'read-file-name)
		    "Directory: " root root)
	   (or gitsum-look-for-adds current-prefix-arg))))
  (with-temp-buffer
    (cd directory)
    (let ((repo (gitsum-repository-root)))
      (unless repo
	(error "Directory `%s' is not under Git version control"
	       directory))
      (cd repo))
    (let ((changes (gitsum-read-changeset gitsum-default-expanded)))
      (if (and changes (not no-display))
	  (gitsum-display changes look-for-adds))
      changes)))

; lifted from diff.el
(defun gitsum-fix-switches (switch-spec)
  "Parse SWITCH-SPEC into a list of switches.
Leave it be if it's not a string."
  (if (stringp switch-spec)
      (let (result (start 0))
	(while (string-match "\\(\\S-+\\)" switch-spec start)
	  (setq result (cons (substring switch-spec (match-beginning 1)
					(match-end 1))
			     result)
		start (match-end 0)))
	(nreverse result))
    switch-spec))

;;;###autoload
(defun gitsum-view (directory)
  "View the contents of the current buffer as a Git changeset for DIRECTORY.
More precisely, searches forward from point for the next changeset-like region,
and attempts to parse that as a Git patch.

When invoked interactively, prompts for a directory; by default, the current
working directory is assumed."
  (interactive
   (list (funcall (if (fboundp 'read-directory-name)
		      'read-directory-name
		    'read-file-name)
		  "Directory: "
		  (gitsum-repository-root))))
  (unless (file-directory-p (expand-file-name "_darcs" directory))
    (error "Directory `%s' is not under darcs version control"
	   directory))
  (if (or (and (search-forward "{" nil t)
	       (goto-char (1- (point))))
	  (search-backward "{" nil t))
      (let ((changes (gitsum-parse-changeset))
	    (default-directory directory))
	(gitsum-display changes))
    (error "Cannot find a darcs patch in the current buffer")))

;;; Gnus integration code, for viewing Git patches in a changeset buffer.
;;; They cannot be recorded from there, however, since the changes have not
;;; been applied to the working tree.  To do this, you must still pipe the
;;; message to "git-apply".  This code only works as a browser for now.

(defvar gitsum-install-gnus-code nil)

(when gitsum-install-gnus-code
  (defun mm-view-git-patch (handle)
    "View HANDLE as a Git patch, using gitsum.el."
    (let* ((name (mail-content-type-get (mm-handle-type handle) 'name))
	   (directory
	    (funcall (if (fboundp 'read-directory-name)
			 'read-directory-name
		       'read-file-name)
		     "Apply patch to directory: ")))
      (mm-with-unibyte-buffer
       (mm-insert-part handle)
       (let ((coding-system-for-write 'binary))
	 (goto-char (point-min))
	 (gitsum-view directory)
	 (delete-other-windows)))))

  (defun gnus-mime-view-git-patch ()
    "Pipe the MIME part under point to a process."
    (interactive)
    (gnus-article-check-buffer)
    (let ((data (get-text-property (point) 'gnus-data)))
      (when data
	(mm-view-git-patch data))))

  (defun gnus-article-view-git-patch (n)
    "Pipe MIME part N, which is the numerical prefix."
    (interactive "p")
    (gnus-article-part-wrapper n 'mm-view-git-patch))

  (eval-after-load "gnus-art"
    '(progn
       (nconc gnus-mime-action-alist
	      '(("apply git patch" . gnus-mime-view-git-patch)))
       (nconc gnus-mime-button-commands
	      '((gnus-mime-view-git-patch "V" "Apply git patch...")))))

  (defun gnus-summary-view-git-patch (directory)
    "Apply the current article as a git patch to DIRECTORY."
    (interactive "DApply patch to directory: ")
    (gnus-summary-select-article)
    (let ((mail-header-separator ""))
      (gnus-eval-in-buffer-window gnus-article-buffer
				  (save-restriction
				    (widen)
				    (goto-char (point-min))
				    (gitsum-view directory)))))

  (eval-after-load "gnus-sum"
    '(progn
       (define-key gnus-summary-mime-map "V" 'gnus-article-view-git-patch)
       (define-key gnus-summary-article-map "V"
	 'gnus-summary-view-git-patch))))

(provide 'gitsum-new)

;;; gitsum-new.el ends here
