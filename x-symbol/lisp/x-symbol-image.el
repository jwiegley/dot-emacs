;;; x-symbol-image.el --- display glyphs at the end of image insertion commands

;; Copyright (C) 1997-1999, 2001 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.4.X
;; Keywords: WYSIWYG, LaTeX, HTML, wp, math, internationalization
;; X-URL: http://x-symbol.sourceforge.net/

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; If you want to use package x-symbol, please visit the URL (use
;; \\[x-symbol-package-web]) and read the info (use \\[x-symbol-package-info]).

;; This file requires file `x-symbol.el which does some initialization.  Thus,
;; do not put any `defcustom' commands into this file.  If you think some
;; variables in this files should be customized, move them to file
;; `x-symbol-vars.el'.

;;; Code:

(provide 'x-symbol-image)
(require 'x-symbol)
(eval-when-compile (require 'cl))



;;;;##########################################################################
;;;;  Main code
;;;;##########################################################################


(defvar x-symbol-image-process-buffer "*x-symbol-image conversion*"
  "Name of the image conversion buffer.")

(defvar x-symbol-image-process-name "Image-Conversion"
  "Name of the image conversion process.")

(defvar x-symbol-image-highlight-map
  (let ((map (make-sparse-keymap)))
    ;; CW: two independend `when's or one `if' or 2*2 `when's ?
    (if (lookup-key global-map [(button2)])
	(progn
	  ;; XEmacs bindings
	  (define-key map [(button2)] 'x-symbol-image-mouse-editor)
	  (define-key map [(button3)] 'x-symbol-image-highlight-menu))
      ;; Emacs bindings
      (define-key map [(mouse-2)] 'x-symbol-image-mouse-editor)
      (define-key map [(mouse-3)] 'x-symbol-image-highlight-menu))
    map)
  "Keymap for mouse event over image insertion commands.")


;;;===========================================================================
;;;  Internal variables
;;;===========================================================================

(defun x-symbol-image-try-special (image)
  "Return image for image specification IMAGE or [nothing].
IMAGE is an element in `x-symbol-image-special-glyphs'."
  (or (and x-symbol-image-data-directory
	   (x-symbol-create-image
	    (expand-file-name (car image) x-symbol-image-data-directory)
	    (cdr image)))
      (and (featurep 'xemacs) [nothing])))

(defvar x-symbol-image-broken-image
  (x-symbol-image-try-special (first x-symbol-image-special-glyphs))
  "Image to represent broken image files.
IMAGE is an element in `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-create-image
  (x-symbol-image-try-special (second x-symbol-image-special-glyphs))
  "Image to represent image files which are currently converted.
IMAGE is an element in `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-design-glyph
  (x-symbol-make-glyph (x-symbol-image-try-special
			(third x-symbol-image-special-glyphs)))
  "Glyph to represent image files still to be designed.
IMAGE is an element in `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-locked-glyph
  (x-symbol-make-glyph (x-symbol-image-try-special
			(fourth x-symbol-image-special-glyphs)))
  "Glyph to represent locked image files.
IMAGE is an element in `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-remote-glyph
  (x-symbol-make-glyph (x-symbol-image-try-special
			(fifth x-symbol-image-special-glyphs)))
  "Glyph to represent \"remote\" image files.
IMAGE is an element in `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-junk-glyph
  (x-symbol-make-glyph (x-symbol-image-try-special
			(sixth x-symbol-image-special-glyphs)))
  "Glyph to represent \"junk\" image files.
IMAGE is an element in `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-buffer-extents nil
  "Internal variable.  Extents for image commands in the current buffer.")
(make-variable-buffer-local 'x-symbol-image-buffer-extents)
(put 'x-symbol-image-buffer-extents 'permanent-local t)

(defvar x-symbol-image-memory-cache nil
  "Internal variable.  Buffer local memory cache for glyphs.
Each element has the form (FILE FULL . GLYPH) where FILE is the given
image file name, FULL is the full file name and GLYPH is the glyph used
for that image file.  If GLYPH is nil, it is not created yet.  See also
`x-symbol-image-use-remote'.  The memory cache is flushed with
`x-symbol-image-init-memory-cache'.")

(make-variable-buffer-local 'x-symbol-image-memory-cache)

(defvar x-symbol-image-all-recursive-dirs nil
  "Internal variable.  Used by `x-symbol-image-searchpath'.")
(defvar x-symbol-image-all-dirs nil
  "Internal variable.  Used by `x-symbol-image-searchpath'.")


;;;===========================================================================
;;;  Main functions
;;;===========================================================================

;;;###autoload
(defun x-symbol-image-parse-buffer (&optional update-cache)
  "*Parse buffer to find image insertion commands.
Parse buffer to display glyphs at the end of image insertion commands.
Image files are converted to \"image cache files\" with images not
bigger than `x-symbol-image-max-width' and `x-symbol-image-max-height'
having a image format XEmacs understands.  The conversion is done by a
program determined by `x-symbol-image-converter', currently you need
\"convert\" from ImageMagick.  To make this conversion fast, we use
asynchronous processes and two cache hierarchies:

 * Memory cache (`x-symbol-image-memory-cache'): buffer-local alist
   FILE.eps -> GLYPH, see also `x-symbol-image-use-remote'.
 * File cache: the image cache file, mentioned above, are kept, see also
   `x-symbol-image-update-cache', which is shadowed by a non-nil
   UPDATE-CACHE and `x-symbol-image-cache-directories'.

When the mouse is over an image insertion command, it is highlighted.
button2 starts an image editor, see `x-symbol-image-editor-alist'.
button3 pops up a menu, see `x-symbol-image-menu'.

The image insertion commands are recognized by keywords in the language
access `x-symbol-image-keywords' whose value have the form
  (IMAGE-REGEXP KEYWORD ...)
IMAGE-REGEXP should match all images files and is used to initialize the
buffer local memory cache, see `x-symbol-image-init-memory-cache'.

Each KEYWORD looks like (REGEXP [FUNCTION] ARG...).  Image insertion
commands matched by REGEXP are highlighted.  FUNCTION, which defaults to
`x-symbol-image-default-file-name', is called with ARGs to get the file
name of the corresponding image file.  If FUNCTION returns nil, the
command is not highlighted.

Relative image file names are expanded in the directory returned by the
function in the language access `x-symbol-master-directory', value nil
means function `default-directory'.  Implicitly relative image file
names are searched in a search path, see `x-symbol-image-use-remote'."
  (interactive)
  (save-excursion
    (x-symbol-image-init-memory-cache)
    (x-symbol-image-parse-region (point-min) (point-max) update-cache)))

;;;###autoload
(defun x-symbol-image-after-change-function (beg end old-len)
  ;; checkdoc-params: (beg end old-len)
  "Function in `after-change-functions' for image insertion commands."
  (if x-symbol-language
      (save-excursion
	(save-match-data
	  (let ((zmacs-region-stays (and (boundp 'zmacs-region-stays)
					 zmacs-region-stays)))
	    (goto-char end)
	    (end-of-line)
	    (setq end (point))
	    (goto-char beg)
	    (beginning-of-line)
	    (x-symbol-image-parse-region (point) end))))))

;; Idea from package bib-cite: OK with a relatively small number of extents
;;;###autoload
(defun x-symbol-image-delete-extents (beg end)
  "Delete x-symbol image extents covering text between BEG and END.
See also `x-symbol-image-buffer-extents'."
  (let ((extents x-symbol-image-buffer-extents) extent)
    (setq x-symbol-image-buffer-extents nil)
    (if (featurep 'xemacs)
	(while extents
	  (setq extent (pop extents))
	  (if (or (extent-detached-p extent)
		  (and (> (extent-end-position extent) beg)
		       ;; If (beginning-of-line 2) instead (end-of-line) in
		       ;; `x-symbol-image-after-change-function': (> end...)
		       (>= end (extent-start-position extent))))
	      (delete-extent extent)
	    (push extent x-symbol-image-buffer-extents)))
      (while extents
	(setq extent (pop extents))
	(if (and (> (overlay-end extent) beg)
		 ;; If (beginning-of-line 2) instead (end-of-line) in
		 ;; `x-symbol-image-after-change-function': (> end...)
		 (>= end (overlay-start extent)))
	    (delete-overlay extent)
	  (push extent x-symbol-image-buffer-extents))))))


;;;===========================================================================
;;;  Main parse function
;;;===========================================================================

(defun x-symbol-image-parse-region (beg end &optional update-cache)
  "*Parse region between BEG and END to find image insertion commands.
If optional UPDATE-CACHE is non-nil, use it instead of
`x-symbol-image-update-cache' to determine whether to create new image
cache files."
  (or update-cache (setq update-cache x-symbol-image-update-cache))
  (let ((modified (buffer-modified-p))
	(buffer-undo-list t) (inhibit-read-only t)
	buffer-file-name buffer-file-truename)
    (unwind-protect
	(let (;;(case-fold-search nil)
	      (keywords (cdr (x-symbol-language-value
			      'x-symbol-image-keywords)))
	      (cached-dirs (cons nil
				 (mapcar 'file-name-as-directory
					 (x-symbol-language-value
					  'x-symbol-image-cached-dirs))))
	      (master-dir (x-symbol-language-value 'x-symbol-master-directory))
	      keyword matcher file-fn file-args
	      file extent cache-elem extent-beg extent-end)
	  (if master-dir (funcall master-dir))
	  (x-symbol-image-delete-extents beg end)
	  (while keywords
	    (setq keyword (pop keywords)
		  matcher (car keyword)
		  file-fn #'x-symbol-image-default-file-name
		  file-args (cdr keyword))
	    (if (functionp (car file-args))
		(setq file-fn (pop file-args)))
	    (goto-char beg)
	    (while (setq extent-end (re-search-forward matcher end t))
	      (setq extent-beg (match-beginning 0))
	      (when (setq file (apply file-fn file-args))
		(if (featurep 'xemacs)
		    (progn
		      (push (setq extent (make-extent extent-beg extent-end))
			    x-symbol-image-buffer-extents)
		      (set-extent-property extent 'start-open t)
		      (set-extent-property extent 'highlight t)
		      (set-extent-property extent 'x-symbol-image-file file)
		      (set-extent-property extent 'help-echo
					   'x-symbol-image-help-echo)
		      (set-extent-property extent 'keymap
					   x-symbol-image-highlight-map)
		      (set-extent-end-glyph
		       extent
		       (if (member (file-name-directory file) cached-dirs)
			   (if (setq cache-elem
				     (cdr (assoc file x-symbol-image-memory-cache)))
			       (or (cdr cache-elem)
				   (setcdr cache-elem (x-symbol-image-create-glyph
						       (car cache-elem) update-cache
						       (stringp
							x-symbol-image-temp-name))))
			     x-symbol-image-design-glyph)
			 (if x-symbol-image-use-remote
			     (x-symbol-image-create-glyph
			      (expand-file-name file master-dir) update-cache)
			   x-symbol-image-remote-glyph))))
		  (push (setq extent (make-overlay extent-beg extent-end))
			x-symbol-image-buffer-extents)
		  (overlay-put extent 'mouse-face 'highlight)
		  (overlay-put extent 'x-symbol-image-file file)
		  (overlay-put extent 'help-echo 'x-symbol-image-help-echo)
		  (overlay-put extent 'keymap x-symbol-image-highlight-map)
		  (overlay-put
		   extent 'after-string
		   (if (member (file-name-directory file) cached-dirs)
		       (if (setq cache-elem
				 (cdr (assoc file x-symbol-image-memory-cache)))
			   (or (cdr cache-elem)
			       (setcdr cache-elem (x-symbol-image-create-glyph
						   (car cache-elem) update-cache
						   (stringp
						    x-symbol-image-temp-name))))
			 x-symbol-image-design-glyph)
		     (if x-symbol-image-use-remote
			 (x-symbol-image-create-glyph
			  (expand-file-name file master-dir) update-cache)
		       x-symbol-image-remote-glyph))))))))
      (and (not modified) (buffer-modified-p) (set-buffer-modified-p nil)))))

(defun x-symbol-image-default-file-name (num &optional regexp extension)
  "Return image file name for last match.
Default FUNCTION in language access `x-symbol-image-keywords', see
`x-symbol-image-parse-buffer'.  Return text matched by the NUMth regexp
group of the corresponding keyword regexp.  If REGEXP is non-nil and the
file name does not match REGEXP, add EXTENSION to the file name."
  (let ((file (match-string num)))
    (if regexp
	(if (string-match regexp file) file (concat file extension))
      file)))


;;;===========================================================================
;;;  Create an (empty) memory cache
;;;===========================================================================

(defun x-symbol-image-init-memory-cache ()
  "Create an empty memory cache.
Scan all directories in the searchpath and all subdirectories in the
language access `x-symbol-image-cached-dirs' for files matched by
IMAGE-REGEXP in the language access `x-symbol-image-keywords' to build
`x-symbol-image-memory-cache' where all GLYPHs are nil."
  (let* ((master-dir (funcall (x-symbol-language-value
			       'x-symbol-master-directory)))
	 (cached-dirs (x-symbol-language-value 'x-symbol-image-cached-dirs))
	 (path (x-symbol-image-searchpath master-dir))
	 (suffixes (car (x-symbol-language-value 'x-symbol-image-keywords)))
	 implicit-dirs
	 dirs dir)
    (setq x-symbol-image-memory-cache nil)
    (while cached-dirs
      (setq dir (file-name-as-directory (pop cached-dirs)))
      (if (or (string-match x-symbol-image-explicitly-relative-regexp dir)
	      (file-name-absolute-p dir))
	  (x-symbol-image-init-memory-cache-1
	   (and master-dir (file-name-as-directory master-dir)) dir suffixes)
	(push dir implicit-dirs)))
    (while path
      (setq dir (pop path)
	    dirs implicit-dirs)
      (while dirs
	(x-symbol-image-init-memory-cache-1 dir (pop dirs) suffixes))
      (x-symbol-image-init-memory-cache-1 dir nil suffixes))))

(defun x-symbol-image-init-memory-cache-1 (root subdir suffixes)
  "Initialize memory cache for image files in ROOT/SUBDIR with SUFFIXES."
  (let* ((dir (if subdir (expand-file-name subdir root) root))
	 (files (and (file-accessible-directory-p dir)
		     (file-readable-p dir)
		     (x-symbol-directory-files dir nil suffixes t t)))
	 file)
    (while files
      (setq file (pop files))
      (push (list (concat subdir file) (expand-file-name file dir))
	    x-symbol-image-memory-cache))))

(defun x-symbol-image-searchpath (master-dir)
  "Return language dependent image searchpath in reverse order.
Uses the language accesses `x-symbol-image-searchpath' and
`x-symbol-master-directory' (via argument MASTER-DIR).  Include all
subdirectories of elements in the image searchpath ending with \"//\",
except symbolic links if `x-symbol-image-searchpath-follow-symlink' is
nil."
  (let ((path (or (x-symbol-language-value 'x-symbol-image-searchpath)
		  '("./")))
	(dirs nil)
	dir truename slashslash)
    (setq x-symbol-image-all-dirs nil)
    (while path
      (setq dir (pop path)
	    slashslash (and (> (length dir) 1)
			    (string-equal (substring dir -2) "//"))
	    dir (file-name-as-directory
		 (expand-file-name (if slashslash (substring dir 0 -1) dir)
				   master-dir))
	    truename (file-truename dir))
      (unless (member truename x-symbol-image-all-dirs)
	(push truename x-symbol-image-all-dirs)
	(push dir dirs))
      (when slashslash
	(setq x-symbol-image-all-recursive-dirs (list truename))
	(setq dirs (x-symbol-image-searchpath-1 dir dirs))))
    dirs))

(defun x-symbol-image-searchpath-1 (dir dirs)
  "Add subdirectories of DIR to DIRS and return result."
  (and (file-accessible-directory-p dir)
       (file-readable-p dir)
       (let ((subs (x-symbol-directory-files dir t "[^.]" nil 'dirs))
	     truename)
	 (while subs
	   (setq dir (pop subs))
	   (when (or x-symbol-image-searchpath-follow-symlink
		     (not (file-symlink-p dir)))
	     (setq dir (file-name-as-directory dir)
		   truename (file-truename dir))
	     (unless (member truename x-symbol-image-all-recursive-dirs)
	       (push truename x-symbol-image-all-recursive-dirs)
	       (if (member truename x-symbol-image-all-dirs)
		   (setq dirs (x-symbol-image-searchpath-1 dir dirs))
		 (push truename x-symbol-image-all-dirs)
		 (setq dirs
		       (x-symbol-image-searchpath-1 dir (cons dir dirs)))))))))
  dirs)


;;;===========================================================================
;;;  Highlighting the image commands: main functions
;;;===========================================================================

(defun x-symbol-image-mouse-editor (event)
  (interactive "e")
  (let ((file (x-symbol-image-event-file event)))
    (if file
	(x-symbol-image-editor file (event-buffer event))
      (error "No image file to edit"))))

;;;###autoload
(defun x-symbol-image-editor (file &optional buffer)
  "Start image editor for the image file FILE used in BUFFER.
If BUFFER is nil, just return string describing the command.  See
`x-symbol-image-editor-alist' and `x-symbol-image-current-marker'."
  (interactive (list (read-file-name "Edit image design file for: "
				     (funcall (x-symbol-language-value
					       'x-symbol-master-directory)))
		     (current-buffer)))
  (let ((result (and file (x-symbol-match-in-alist
			   file x-symbol-image-editor-alist))))
    (and file buffer (setq file (x-symbol-image-active-file file buffer)))
    (if (and result file)
	(if (functionp (car result))
	    (apply (car result) file buffer (cdr result))
	  (setq result
		(format (car result)
			(if (cadr result)
			    (x-symbol-image-file-name file (cadr result))
			  file)))
	  (if buffer
	      (let ((default-directory (file-name-directory file)))
		(shell-command result))
	    result))
      (if buffer
	  (if file
	      (error "Do not know which image editor to use for %S" file)
	    (error "Cannot use highlighted file"))))))

(defun x-symbol-image-highlight-menu (event)
  ;; checkdoc-params: (event)
  "Popup menu over the highlighted image insertion command.
See `x-symbol-image-menu' and `x-symbol-image-editor-alist'."
  (interactive "e")
  (let ((file (x-symbol-image-event-file event)))
    (if file
	(popup-menu (x-symbol-image-active-file file (event-buffer event) t)))))

(defun x-symbol-image-help-echo (extent &optional object pos)
  "Return help echo for the EXTENT of the image insertion command.
See variable `x-symbol-image-help-echo'."
  (if object (setq extent object))	; Emacs
  (x-symbol-fancy-string
   (cons (format (car x-symbol-image-help-echo)
		 (x-symbol-image-editor (extent-property extent
							 'x-symbol-image-file)))
	 (cdr x-symbol-image-help-echo))))


;;;===========================================================================
;;;  Get files which the image editor could work on
;;;===========================================================================

(defun x-symbol-image-file-name (file &optional extension dir)
  "Return a name deduced from the image file name FILE.
Use EXTENSION as the new extension.  If DIR is non-nil, replace
directory part by DIR.  With a non-nil `x-symbol-image-scale-method',
the scale factor is deleted in the file name."
  (and file
       (let ((edit (file-name-sans-extension (file-name-nondirectory file))))
	 (or dir (setq dir (file-name-directory file)))
	 (setq file
	       (concat (if (and x-symbol-image-scale-method
				(string-match x-symbol-image-scale-method edit))
			   (substring edit 0 (match-beginning 0))
			 edit)
		       extension))
	 (if dir (expand-file-name file dir) file))))

(defun x-symbol-image-event-file (event)
  "Return image file name at position of mouse event EVENT."
  (and event
       (setq event (extent-at (if (featurep 'xemacs)
				  (or (event-point event)
				      (1- (event-closest-point event)))
				(posn-point (event-end event)))
			      (event-buffer event)
			      'x-symbol-image-file))
       (extent-property event 'x-symbol-image-file)))

(defun x-symbol-image-active-file (file buffer &optional menup)
  ;; checkdoc-params: (event)
  "Return the full name of the active image file FILE in BUFFER.
If MENUP is non-nil, return menu specified by `x-symbol-image-menu'
instead."
  (save-excursion
    (set-buffer buffer)
    (let ((master-dir (funcall (x-symbol-language-value
				'x-symbol-master-directory)))
	  path)
      (if (or (string-match x-symbol-image-explicitly-relative-regexp file)
	      (file-name-absolute-p file))
	  (setq path (list (expand-file-name (file-name-directory file)
					     master-dir))
		file (file-name-nondirectory file))
	(setq path (x-symbol-image-searchpath master-dir)))
      (if menup
	  (let ((menu (cdr x-symbol-image-menu))
		dir full exists)
	    (while path
	      (setq dir (pop path)
		    full (expand-file-name file dir)
		    exists (file-exists-p full))
	      (push (vector (if (featurep 'xemacs)
				(abbreviate-file-name dir t)
			      (abbreviate-file-name dir))
			    (list 'x-symbol-image-editor full buffer)
			    :active (if exists
					(file-readable-p full)
				      (file-writable-p full))
			    :keys (and exists x-symbol-image-current-marker))
		    menu))
	    (cons (format (car x-symbol-image-menu)
			  (x-symbol-image-editor file))
		  menu))
	(let (result full)
	  (setq path (nreverse path))
	  (while path
	    (setq full (expand-file-name file (pop path)))
	    (if (file-readable-p full)
		(setq result full
		      path nil)
	      (or result
		  (file-exists-p full)	; i.e., not readable
		  (if (file-writable-p full) (setq result full)))))
	  result)))))



;;;;##########################################################################
;;;;  Glyph creation via processes
;;;;##########################################################################


;; A stack is better than a FIFO queue since editing the current line should
;; have the highest priority.
(defvar x-symbol-image-process-stack nil
  "Internal variable.  Stack of image conversion tasks.
Each element looks like the value of `x-symbol-image-process-elem'.")

(defvar x-symbol-image-process-elem nil
  "Internal variable.  Current image conversion task element.
It has the form (CACHE GLYPH COMMAND TEMP).  CACHE is the name of the
image cache file, GLYPH is the glyph whose image will be defined by the
finished image cache file.  COMMAND is the command which starts the
process creating CACHE, see `x-symbol-image-converter'.  If TEMP is
non-nil, the image cache file will be deleted directly after its
usage.")


;;;===========================================================================
;;;  Main function for glyph creation
;;;===========================================================================

(defun x-symbol-image-create-glyph (file update-cache &optional temp)
  "Return a glyph for the image file FILE.
Start a process to create a new image cache file.  If UPDATE-CACHE is
non-nil, use it instead of `x-symbol-image-update-cache' to determine
whether this is really necessary.  If optional TEMP is non-nil, allow
the use of temporary cache files."
  (let ((infile (condition-case nil
		    (file-truename file)
		  (error nil)))
	outfile elem)
    (cond ((null infile) x-symbol-image-locked-glyph)
	  ((null (file-readable-p infile))
	   (if (and (null (file-exists-p infile))
		    (file-writable-p infile))
	       x-symbol-image-design-glyph
	     x-symbol-image-locked-glyph))
	  ((null x-symbol-image-converter) x-symbol-image-junk-glyph)
	  ((null (setq outfile
		       (x-symbol-image-cache-name
			infile
			;; TODO: temp image files don't work with Emacs
			(and temp (featurep 'xemacs) temp))))
	   x-symbol-image-junk-glyph)
	  ((and (stringp outfile)
		(null (file-writable-p outfile)))
	   x-symbol-image-junk-glyph)
	  ((and (equal outfile (car x-symbol-image-process-elem))
		(get-process x-symbol-image-process-name))
	   (cadr x-symbol-image-process-elem))
	  ((setq elem (assoc outfile x-symbol-image-process-stack))
	   (prog1 (cadr elem)
	     (x-symbol-image-process-stack)))
	  (t
	   (let* ((ofile (if (symbolp outfile)
			     (concat x-symbol-image-temp-name
				     (cadr x-symbol-image-converter))
			   outfile))
		  (image (and (null (symbolp outfile))
			      (x-symbol-create-image
			       ofile (car x-symbol-image-converter))))
		  (glyph (x-symbol-make-glyph
			  (or image x-symbol-image-create-image))))
	     (when (or (null image)
		       (eq update-cache t)
		       (and update-cache
			    (file-newer-than-file-p infile outfile)))
	       (push (list ofile glyph
			   (list (cddr x-symbol-image-converter) infile ofile)
			   (symbolp outfile))
		     x-symbol-image-process-stack)
	       (x-symbol-image-process-stack))
	     glyph)))))


;;;===========================================================================
;;;  Compute name of file cache
;;;===========================================================================

(defun x-symbol-image-cache-name (infile temp)
  "Return the name of the image cache file for the image file INFILE.
The directory part is determined by `x-symbol-image-cache-directories'.
INFILE must be a fully expanded file name, the extension by
`x-symbol-image-converter'.  Return value nil means, do not convert the
image, use `x-symbol-image-junk-glyph' instead.  If optional TEMP is
non-nil, allow the use of temporary cache files, in this case, t would
be returned."
  (let* ((case-fold-search (eq system-type 'vax-vms))
	 (indir (file-name-directory infile))
	 (outdir (x-symbol-match-in-alist indir x-symbol-image-cache-directories
					  nil t)))
    (if (symbolp outdir) (and outdir temp)
      (if (or (file-directory-p (setq outdir (expand-file-name outdir indir)))
	      (condition-case nil
		  (progn (make-directory outdir t) t)
		(error nil)))
	  (x-symbol-image-file-name
	   infile (cadr x-symbol-image-converter) outdir)))))


;;;===========================================================================
;;;  Process handling
;;;===========================================================================

(defun x-symbol-image-process-stack ()
  "Handle next task in variable `x-symbol-image-process-stack'."
  (if x-symbol-image-process-stack
      (let ((process (get-process x-symbol-image-process-name)))
	(unless (and process (eq (process-status process) 'run))
	  (if process (delete-process process))
	  (setq x-symbol-image-process-elem
		(pop x-symbol-image-process-stack))
	  (setq process (apply (caaddr x-symbol-image-process-elem)
			       (cdaddr x-symbol-image-process-elem)))
	  (set-process-sentinel process 'x-symbol-image-process-sentinel)
	  ))))

(defun x-symbol-image-convert-file (infile)
  "Put prefix before INFILE if necessary for \"convert\".
Uses `x-symbol-image-convert-file-alist'.  Also put postfix \"[0]\"
after INFILE to just use the first part of a multi-part image."
  (concat (x-symbol-match-in-alist infile x-symbol-image-convert-file-alist)
	  infile
	  "[0]"))

(defun x-symbol-image-start-convert-mono (infile outfile)
  "Start process convert INFILE to monochrome OUTFILE.
Used as value in `x-symbol-image-converter'."
  (start-process x-symbol-image-process-name
		 (get-buffer-create x-symbol-image-process-buffer)
		 x-symbol-image-convert-program "+matte"
		 "-geometry" (format "%dx%d>" x-symbol-image-max-width
				     x-symbol-image-max-height)
		 "-threshold" "190" "-monochrome"
		 (x-symbol-image-convert-file infile) outfile))

(defun x-symbol-image-start-convert-color (infile outfile)
  "Start process convert INFILE to OUTFILE with restricted colors.
Used as value in `x-symbol-image-converter'."
  (start-process x-symbol-image-process-name
		 (get-buffer-create x-symbol-image-process-buffer)
		  x-symbol-image-convert-program "+matte"
		 "-geometry" (format "%dx%d>" x-symbol-image-max-width
				     x-symbol-image-max-height)
		 "-sharpen" "58" "-colors" "4"
		 (x-symbol-image-convert-file infile) outfile))

(defun x-symbol-image-start-convert-truecolor (infile outfile)
  "Start process convert INFILE to OUTFILE using colors.
Used as value in `x-symbol-image-converter'."
  (start-process x-symbol-image-process-name
		 (get-buffer-create x-symbol-image-process-buffer)
		 x-symbol-image-convert-program "+matte"
		 "-geometry" (format "%dx%d>" x-symbol-image-max-width
				     x-symbol-image-max-height)
		 (x-symbol-image-convert-file infile) outfile))

(defun x-symbol-image-start-convert-mswindows (infile outfile)
  "Start process convert INFILE to OUTFILE using colors.
Used as value in `x-symbol-image-converter'."
  (start-process x-symbol-image-process-name
		 (get-buffer-create x-symbol-image-process-buffer)
		 x-symbol-image-convert-program "+matte"
		 "-geometry" (format "%dx%d>" x-symbol-image-max-width
				     x-symbol-image-max-height)
		 ;; for some reason [0] at the end of the file name does not
		 ;; work under ms-windows
		 (concat (x-symbol-match-in-alist
			  infile x-symbol-image-convert-file-alist)
			 infile)
		 outfile))

(defun x-symbol-image-start-convert-colormap (infile outfile)
  "Start process convert INFILE to OUTFILE using a colormap.
Produce OUTFILE with `x-symbol-image-convert-colormap' or monochrome
OUTFILE if `x-symbol-image-convert-mono-regexp' matches INFILE.  Used as
value in `x-symbol-image-converter'."
  (if (or (and x-symbol-image-convert-mono-regexp
	       (string-match x-symbol-image-convert-mono-regexp infile))
	  (null x-symbol-image-convert-colormap))
      (x-symbol-image-start-convert-mono infile outfile)
    (start-process x-symbol-image-process-name
		   (get-buffer-create x-symbol-image-process-buffer)
		   x-symbol-image-convert-program "+matte"
		   "-geometry" (format "%dx%d>" x-symbol-image-max-width
				       x-symbol-image-max-height)
		   "-map" x-symbol-image-convert-colormap
		   (x-symbol-image-convert-file infile) outfile)))

(defun x-symbol-image-process-sentinel (process event)
  "Set glyph image after process PROCESS has finished with value EVENT.
Also look for more tasks in variable `x-symbol-image-process-stack'."
  (if (memq (process-status process) '(signal exit))
      (let ((buffer (process-buffer process)))
	(if (buffer-live-p buffer)
	    ;; Don't follow info files, use some code from compile.el instead:
	    ;; do not let cursor movement influence output placement
	    (save-excursion
	      (set-buffer buffer)
	      (goto-char (point-max))
	      (insert-before-markers (current-time-string) ": "
				     (process-name process) " " event
				     "\"" (car x-symbol-image-process-elem)
				     (if (eq (process-status process) 'exit)
					 "\" created\n"
				       "\" failed\n"))))
	(x-symbol-set-glyph-image
	 (cadr x-symbol-image-process-elem)
	 (or (and (eq (process-status process) 'exit)
		  (x-symbol-create-image (car x-symbol-image-process-elem)
					 (car x-symbol-image-converter)))
	     x-symbol-image-broken-image))
	;; TODO: in Emacs, we need `clear-image-cache' for some reason, in
	;; older XEmacsen, we did need something, but it wasn't really
	;; important, and I haven't noticed it anymore...
	(or (featurep 'xemacs)
	    (and (boundp 'x-symbol-emacs-after-create-image-function)
		 (functionp x-symbol-emacs-after-create-image-function)
		 (funcall x-symbol-emacs-after-create-image-function)))
;;;	(redisplay-frame nil t)		; doesn't work
;;;	(sit-for 0)			; does that work?
	(if (cadddr x-symbol-image-process-elem)
	    (condition-case nil
		(delete-file (car x-symbol-image-process-elem))
	      (error nil)))
	(setq x-symbol-image-process-elem nil)
	(delete-process process)
	(x-symbol-image-process-stack))))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-image.el ends here
