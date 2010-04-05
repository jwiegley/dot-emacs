;;; radio.el --- memex-style multi-file topic tag link navigator

;; Copyright (C) 2007, 2008  David O'Toole

;; Author: David O'Toole <dto@gnu.org>
;; Keywords: convenience, hypermedia

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Add something like the following to your .emacs:
;;
;; (require 'radio)
;; (add-hook 'emacs-lisp-mode-hook #'radio-mode)
;; (setf radio-configuration-alist 
;;       `(("/home/dto/rlx" 
;; 	 "browser.lisp"
;; 	 "cells.lisp"
;; 	 "clon.lisp"
;; 	 "console.lisp"
;; 	 "math.lisp"
;; 	 "rgb.lisp"
;; 	 "rlx.lisp"
;; 	 "radio.el"
;; 	 "widgets.lisp"
; 	 "worlds.lisp")))

;; TODO todo tags

(require 'cl)

;;; Configuring which files to search

(defun* radio-buffer-directory (&optional (buffer (current-buffer)))
  (file-name-directory (expand-file-name (buffer-file-name buffer))))

(defun* radio-bare-file-name (&optional (buffer (current-buffer)))
  (file-name-nondirectory (expand-file-name (buffer-file-name buffer))))

(defvar *radio-files* nil)

(defvar radio-configuration-alist nil)

(defun radio-choose-project ()
  (interactive)
  (completing-read "Choose project: " radio-configuration-alist))

(defvar *radio-project* nil)

(defun radio-project-files (project)
  (cdr-safe (assoc project radio-configuration-alist)))

(defun radio-project-file (project file)
  (let ((entry (assoc project radio-configuration-alist)))
    (when entry (expand-file-name file (car entry)))))

(defun* radio-switch-project (&optional (project (radio-choose-project)))
  (interactive)
  (setf *radio-project* project)
  (setf *radio-files* (radio-project-files project))
  (message "Switched to radio project %s with %d files." project (length *radio-files*)))

;;; Reading and writing tags

(defconst radio-tag-regexp (concat "\\(:\\.\\)[[:space:]]*\\(.*\\)[[:space:]]*\\(>\\)")
  "Regular expression matching tags.")

(defun radio-format-tag-regexp (string)
  "Make a regexp to find STRING as a tag."
  (concat ":" "\\.[[:space:]]*" string "[[:space:]]*>"))

(defun radio-read-next-tag (&optional bound)
  "Find the next tag, if any, regardless of tag content."
  (interactive)
  (save-excursion
    (when (re-search-forward radio-tag-regexp bound :noerror)
      (match-string-no-properties 2))))

(defun radio-read-previous-tag (&optional bound)
  "Find the previous tag, if any, regardless of tag content."
  (interactive)
  (save-excursion
    (when (re-search-backward radio-tag-regexp bound :noerror)
      (match-string-no-properties 2))))

(defun radio-tag-on-current-line ()
  (save-excursion
    (goto-char (point-at-bol))
    (radio-read-next-tag (point-at-eol))))

(defun radio-auto-choose-tag ()
  (interactive)
  (or (radio-tag-on-current-line)
      (radio-read-previous-tag)))

;;; Finding all tags in a project

(defvar *radio-tags* nil)

(defun* radio-all-tags-in-buffer (&optional (buffer (current-buffer)))
  (interactive)
  (save-excursion
    (let (tags)
      (goto-char (point-min))
      (while (re-search-forward radio-tag-regexp nil :noerror)
	(push (match-string-no-properties 2) tags))
      tags)))

(defun* radio-all-tags-in-project (&optional (project *radio-project*))
  (with-temp-buffer
    (let ((files (radio-project-files project))
	  tags)
      (dolist (f files)
	(delete-region (point-min) (point-max))
	(insert-file-contents-literally (radio-project-file project f))
	(setf tags (union tags (remove-duplicates (radio-all-tags-in-buffer) :test 'equal))))
      (sort tags #'string<))))

(defun* radio-rescan-tags (&optional (project *radio-project*))
  (interactive)
  (message "Scanning project for tags...")
  (setf *radio-tags* (radio-all-tags-in-project project))
  (message "Scanning project for tags... Done."))

(defun radio-choose-tag ()
  (interactive)
  (when (null *radio-tags*)
    (radio-rescan-tags))
  (completing-read "Choose tag: " *radio-tags*))

(defun radio-find-tag ()
  (interactive)
  (radio-seek-tag (radio-choose-tag)))
  
;;; Navigating groups of tags within the current buffer

(defun* radio-next-tag-in-buffer (&optional (tag (radio-auto-choose-tag)) noerror nowrap bound)
  "Find the next tag with name TAG in the current buffer."
  (interactive)
  (let ((search-string (radio-format-tag-regexp tag))
	(match-point nil))
    (block searching
      (when (setf match-point (re-search-forward search-string bound t))
	(return-from searching match-point))
      ;; otherwise go to beginning and look again
      (unless nowrap
	(goto-char (point-min))
	(re-search-forward search-string nil noerror)))))

(defun* radio-previous-tag-in-buffer (&optional (tag (radio-auto-choose-tag)) noerror nowrap bound)
  "Find the previous tag with name TAG in the current buffer."
  (interactive)
  (let ((search-string (radio-format-tag-regexp tag))
	(match-point nil))
    (block searching
      (when (setf match-point (re-search-backward search-string bound t))
	(return-from searching match-point))
      (unless nowrap
	(goto-char (point-max))
	(re-search-backward search-string nil noerror)))))

;;; Navigating to the next tag in the project

(defvar radio-use-flash nil)

(defvar radio-flash-length 1.0)

(defun radio-flash-header (string)
  (lexical-let ((old-format header-line-format)
		(buffer header-line-format))
    (setf header-line-format (propertize string
					 'face 'radio-attention-face))
    (run-at-time radio-flash-length nil (lambda ()
					  (with-current-buffer buffer
					  (setf header-line-format old-format))))))

(defun* radio-seek-tag (&optional (tag (radio-auto-choose-tag)) backward)
  (when tag
    (let* ((start-buffer (current-buffer))
	   (start-point (point))
	   (filename (radio-bare-file-name))
	   (pos nil)
	   (point-min-or-max (if backward #'point-max #'point-min))
	   (seek-function (if backward #'radio-previous-tag-in-buffer
			      #'radio-next-tag-in-buffer))
	   (current-file filename)
	   (new-file nil)
	   (found-elsewhere nil))
      (message "Seeking %S" tag)
      (unless (funcall seek-function tag :noerror :nowrap)
	(setf found-elsewhere
	      (block seeking
		(loop 
		   do
		     (progn 
		       (find-file (radio-project-file *radio-project* current-file))
		       (when (not (string= current-file filename))
			 (goto-char (funcall point-min-or-max)))
		       (when (funcall seek-function tag :noerror :nowrap)
			 (when radio-use-flash 
			   (radio-flash-header (concat (format "  %s @  %s"
							       tag current-file))))
			 (return-from seeking :found))
		       ;; didn't find it. choose a new file from the list.
		       (setf pos (position current-file *radio-files*
					   :test 'equal))
		       (setf new-file (nth (mod (+ pos (if backward -1 1))
						(length *radio-files*))
					   *radio-files*))
			 (setf current-file new-file))
		     ;; did we wrap around to the buffer we started with?
		     while (not (string= new-file filename)))
		  (return-from seeking nil)))
	  (when (not found-elsewhere)
	    ;; see if we could wrap around in the original buffer.
	    (switch-to-buffer start-buffer)
	    (goto-char (funcall point-min-or-max))
	    (unless (funcall seek-function tag :noerror :nowrap)
	      (error "No such tag found.")))))
    (recenter)))
	    
(defun* radio-next-tag (&optional (tag (radio-auto-choose-tag)))
  (interactive)
  (radio-seek-tag tag))

(defun* radio-previous-tag (&optional (tag (radio-auto-choose-tag)))
  (interactive)
  (radio-seek-tag tag :backward))

;;; Font-locking the tags

(defface radio-annotation-delimiter-face
'((t (:foreground "gold3")))
  "Face for radio tags.")

(defvar radio-annotation-delimiter-face
'radio-annotation-delimiter-face)

(defface radio-annotation-delimiter-alt-face
    '((t (:foreground "gray30")))
  "Face for radio tags.")

(defvar radio-annotation-delimiter-alt-face
  'radio-annotation-delimiter-alt-face)

(defface radio-annotation-data-face
'((t (:foreground "gray70")))
  "Face for radio tag data.")

(defvar radio-annotation-data-face
  'radio-annotation-data-face)

(defface radio-attention-face
'((t (:foreground "yellow" :background "red")))
  "Face for things that should get your attention.")

(defvar radio-attention-face
  'radio-attention-face)

(defvar radio-font-lock-keywords 
  `((,radio-tag-regexp 
     (1 radio-annotation-delimiter-face prepend)
     (2 radio-annotation-data-face prepend)
     (3 radio-annotation-delimiter-alt-face prepend))))

(defun radio-do-font-lock (add-or-remove)
  (dolist (keyword radio-font-lock-keywords)
    (apply add-or-remove (list nil (list keyword)))))

(defun radio-enable ()
  (radio-do-font-lock 'font-lock-add-keywords)
  (font-lock-fontify-buffer))

(defun radio-disable ()
  (radio-do-font-lock 'font-lock-remove-keywords)
  (font-lock-fontify-buffer))

;;; Minor mode 

(defvar radio-keymap nil)
(when (null radio-keymap)
  (setq radio-keymap (make-sparse-keymap))
  (define-key radio-keymap (kbd "C-c , n") 'radio-next-tag)
  (define-key radio-keymap (kbd "C-c , p") 'radio-previous-tag)
  (define-key radio-keymap (kbd "C-c , c") 'radio-find-tag))
  ;; (define-key radio-keymap (kbd "C-c , t") 'radio-show-todo-list)
  ;; (define-key radio-keymap (kbd "C-c , b") 'radio-edit-binary-annotation))

(define-minor-mode radio-mode
  "Tag lines of a file with Org entries kept in another file."
  nil 				
  :lighter " Radio"
  :keymap radio-keymap
  (if radio-mode
      (radio-enable)
    (radio-disable)))

;; (add-hook 'emacs-lisp-mode-hook #'radio-enable)

(provide 'radio)
;;; radio.el ends here

