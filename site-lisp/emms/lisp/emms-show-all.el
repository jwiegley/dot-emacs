;;; emms-show-all.el --- Detailed track information for Emms.

;; Copyright (C) 2016  Free Software Foundation, Inc.

;; Author: Yoni Rabkin <yrk@gnu.org>

;; This file is part of EMMS.

;; EMMS is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; EMMS is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with EMMS; if not, write to the Free Software Foundation,
;; Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;;
;;; Shows all of the available information Emms can provide on the
;;; currently playing track. Based on an idea suggested on the
;;; emms-help mailing list by Ivan Truskov.

;;; Code:

(require 'emms)
(require 'emms-tag-editor)


(defvar emms-show-all-buffer-name "Emms Track Information"
  "Name of buffer used by `emms-show-all'.")

(defvar emms-show-all-kill-buffer-on-quit-p nil
  "If t, kill the show-all buffer when quitting.")

(defvar emms-show-all-track-alist nil
  "Declare so as to silence the compiler.")

(define-derived-mode emms-show-all-mode text-mode "Emms-Show-All"
  "Major mode for `emms-show-all'
  \\{emms-show-all-mode-map}")

(defconst emms-show-all-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map text-mode-map)
    (define-key map (kbd "q") 'emms-show-all-mode-bury-buffer)
    (define-key map (kbd "E") 'emms-show-all-edit-track)
    map)
  "Keymap for `emms-show-all-mode'.")


(defun emms-show-all-edit-track ()
  "Edit the track being shown."
  (interactive)
  (let ((track emms-show-all-track-alist))
    (emms-show-all-mode-bury-buffer)
    (emms-tag-editor-edit-track track)))

(defun emms-show-all-mode-bury-buffer ()
  "Bury, and optionally kill the show buffer."
  (interactive)
  (bury-buffer emms-show-all-buffer-name)
  (delete-window)
  (when emms-show-all-kill-buffer-on-quit-p
    (kill-buffer emms-show-all-buffer-name)))

(defun emms-show-all-setup-buffer ()
  "Prepare the display buffer."
  (let ((buffer (get-buffer-create emms-show-all-buffer-name)))
    (with-current-buffer buffer
      (when (not (local-variable-p 'emms-show-all-track-alist))
	(make-local-variable 'emms-show-all-track-alist))
      (setq buffer-read-only t)
      (when (not (equal major-mode 'emms-show-all-mode))
	(emms-show-all-mode))
      (let ((inhibit-read-only t))
	(erase-buffer)))
    buffer))

(defun emms-show-all-format (track)
  "Format information for TRACK."
  (let ((s ""))
    (dolist (e (mapcar #'(lambda (tag)
			   (cons
			    (format "%s" (car tag))
			    (or (emms-track-get track (car tag)) "")))
		       emms-tag-editor-tags))
      (setq s (concat s (format "%-17s: %s\n" (car e) (cdr e)))))
    s))

(defun emms-show-all-insert (track)
  "Insert information for TRACK in current buffer."
  (let ((type (emms-track-type track)))
    (cond ((eq 'file type)
	   (insert (emms-show-all-format track)))
	  ((eq 'url type)
	   (insert
	    (emms-format-url-track-name (emms-track-name track))))
	  (t (concat (symbol-name type)
		     ": " (emms-track-name track))))))

(defun emms-show-all-track (track)
  "Display information for TRACK."
  (let ((buffer (emms-show-all-setup-buffer)))
    (with-current-buffer buffer
      (let ((inhibit-read-only t))
	(setq emms-show-all-track-alist track)
      	(emms-show-all-insert track))
      (pop-to-buffer (current-buffer)))))

(defun emms-show-all ()
  "Describe the current EMMS track in detail."
  (interactive)
  (if emms-player-playing-p
      (emms-show-all-track
       (emms-playlist-current-selected-track))
    (message "nothing playing right now")))


(provide 'emms-show-all)

;;; emms-playlist-mode.el ends here
