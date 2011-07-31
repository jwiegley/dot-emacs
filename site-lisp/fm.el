;;; fm.el --- follow mode for compilation/output buffers

;; Copyright (C) 1997 Stephen Eglen

;; Author: Stephen Eglen <stephen@anc.ed.ac.uk>
;; Maintainer: Stephen Eglen <stephen@anc.ed.ac.uk>
;; Created: 03 Jul 1997
;; Version: 1.0
;; Keywords: outlines
;; location: http://www.anc.ed.ac.uk/~stephen
;; RCS: $Id: fm.el,v 1.1 2000/01/14 02:41:00 johnw Exp $

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; As you move through the lines of an output buffer (such as from
;; `grep' or `occur'), another window highlights the corresponding
;; line of the source buffer.

;; This is inspired by the table of contents code from reftex.el.
;; http://www.strw.leidenuniv.nl/~dominik/Tools/

;;; Installation
;; To use the mode, do M-x fm-start in the output buffer.  Or just add
;; it to the mode hooks, e.g.:
;; (add-hook 'occur-mode-hook 'fm-start)
;; (add-hook 'compilation-mode-hook 'fm-start)
;;

;;; Examples:
;;
;; Do an occur for the word `package' in the NEWS file:
;; C-h n
;; M-x occur RTN package RTN

;; or test it on the current file:
;; (grep "grep -n 'def' fm.el")
;; (occur "def")

;; Once following is activated in a buffer, it can be toggled with the
;; "f" key in that buffer.

;; To extend this code to handle other types of output buffer, you
;; need to add an entry to the alist `fm-modes'.

;; If you want to use fm in a buffer that doesn't have a useful major
;; mode, you can always set the value of fm-defun yourself.  For
;; example, the cscope buffer is in fundamental mode, so in this case
;; we set fm-defun as a local variable to be the defun to use for
;; visiting the corresponding line of the source buffer.

(add-hook 'cscope-query-hook 'cscope-run-fm)

(defun cscope-run-fm ()
  "Run cscope in the fm buffer."
  (set (make-local-variable 'fm-defun) '(cscope-interpret-output-line))
  (fm-start))

;; If you are using this in the compile mode, you may find it easier
;; to use the key M-p to go to the previous error.  Otherwise, you may
;; find that if you go up one line, and this line doesn't have an
;; error on it, it goes down one line again, taking you back where you
;; started!

;;; TODO
;; ??

;;; Code:

;; fm-highlight is currently used to highlight the regions of both
;; the source(0) and output(1) buffers.

(defvar fm-modes
  '( (compilation-mode compile-goto-error)
     (occur-mode  occur-mode-goto-occurrence)
     (outlines-mode  outlines-goto-line) ;; sje hack
     ;;(fundamental-mode cscope-interpret-output-line) ;;todo big time
     )
  "Alist of modes and the corresponding defun to visit source buffer.")

;; toggles...
(defvar fm-working t)

(defun fm-start ()
  "Set up `follow-mode' to run on the current buffer.
This should be added to buffers through hooks, such as
`occur-mode-hook'."
  (interactive)
  (let ((l))
    ;; first check to see if it is worth running fm in this mode.
    (if (not (boundp 'fm-defun))
	(progn
	  (setq f (cdr (assoc major-mode fm-modes)))
	  (if f
	      (set (make-local-variable 'fm-defun) f))))

    (if (boundp 'fm-defun)
	(progn
	  (make-local-hook 'post-command-hook)
	  (make-local-hook 'pre-command-hook)
	  (setq post-command-hook '(fm-post-command-hook))
	  (setq pre-command-hook  '(fm-pre-command-hook))
	  (local-set-key "f" 'fm-toggle)
	  )
      ;; else
      (error "Cannot use fm in this mode."))))

(defun fm-pre-command-hook ()
  "Remove highlighing in both source and output buffers."
  ;; used as pre command hook in *toc* buffer
  (if fm-working
      (progn
	(fm-unhighlight 0)
	(fm-unhighlight 1)
	)))

(defun fm-post-command-hook ()
  "Add the highlighting if possible to both source and output buffers."
  ;;(message (format "run post in %s" (buffer-name)) )
  (if fm-working
      (let (ret)
	(progn
	  (let ((buf (buffer-name))
		(f nil))


	    ;; select current line.
	    (if (not (boundp 'fm-defun))
		(error "Cannot use fm in this buffer."))

	    (setq ret
		  (condition-case nil
		      (eval fm-defun)
		    (error 'failed)))
	    ;;(message "ret is %s" ret)

	    (if (not (eq ret 'failed))
		(progn
		  ;; make the highlight in the source buffer.
		  (save-excursion
		    (fm-highlight 0
				  (progn (beginning-of-line) (point))
				  (progn (end-of-line) (point))))


		  ;; make the highlight in the output buffer.
		  (pop-to-buffer buf)
		  (and (> (point) 1)
		       (save-excursion
			 (fm-highlight 1
				       (progn (beginning-of-line) (point))
				       (progn (end-of-line) (point)))))

		  )
	      ;; else there was an error
	      (progn
		;; make sure we stay in output buffer.
		(pop-to-buffer buf)
	      (message "couldn't find line..."))))))))

(defun fm-toggle ()
  "Toggle the fm behaviour on and off."
  (interactive)
  (setq fm-working (not fm-working)))

;;; Highlighting (copied from reftex.el -- cheers Carsten!)

;; Highlighting uses overlays.  If this is for XEmacs, we need to load
;; the overlay library, available in version 19.15
(and (not (fboundp 'make-overlay))
     (condition-case nil
	 (require 'overlay)
       ('error
	(error "Fm needs overlay emulation (available in XEmacs 19.15)"))))

;; We keep a vector with several different overlays to do our highlighting.
(defvar fm-highlight-overlays [nil nil])

;; Initialize the overlays
(aset fm-highlight-overlays 0 (make-overlay 1 1))
(overlay-put (aref fm-highlight-overlays 0) 'face 'highlight)
(aset fm-highlight-overlays 1 (make-overlay 1 1))
(overlay-put (aref fm-highlight-overlays 1) 'face 'highlight)

;; Two functions for activating and deactivation highlight overlays
(defun fm-highlight (index begin end &optional buffer)
  "Highlight a region with overlay INDEX."
  (move-overlay (aref fm-highlight-overlays index)
		begin end (or buffer (current-buffer))))
(defun fm-unhighlight (index)
  "Detatch overlay INDEX."
  (delete-overlay (aref fm-highlight-overlays index)))

(provide 'fm)
;;; fm.el ends here
