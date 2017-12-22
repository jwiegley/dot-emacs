;;; emms-metaplaylist-mode.el --- A major mode for lists of Emms playlists

;; Copyright (C) 2006, 2007, 2008, 2009, 2017 Free Software Foundation, Inc.

;; Author: Yoni Rabkin <yrk@gnu.org>

;; This file is part of EMMS.

;; EMMS is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; EMMS is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with EMMS; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:
;;
;; `emms-metaplaylist-mode' creates an interactive list of all the
;; Emms playlist buffers. The currently active buffer is
;; highlighted. You can choose a buffer from the list with RET and get
;; taken there.

;;; Code:

(require 'emms)
(require 'emms-playlist-mode)

;;; --------------------------------------------------------
;;; Variables, customisation and faces
;;; --------------------------------------------------------

(defgroup emms-metaplaylist-mode nil
  "*The Emacs Multimedia System meta-playlist mode."
  :prefix "emms-metaplaylist-mode-"
  :group 'multimedia)

(defcustom emms-metaplaylist-mode-buffer-name "*Emms Playlist Buffers*"
  "*Name of the buffer in which Emms playlists will be listed."
  :type 'string
  :group 'emms-metaplaylist-mode)

(defcustom emms-metaplaylist-mode-hooks nil
  "*List of hooks to run on entry to emms-metaplaylist-mode."
  :type 'list
  :group 'emms-metaplaylist-mode)

(defface emms-metaplaylist-mode-face
  '((((class color) (background dark))
     (:foreground "AntiqueWhite3"))
    (((class color) (background light))
     (:foreground "red3"))
    (((type tty) (class mono))
     (:inverse-video t))
    (t (:background "WhiteSmoke")))
  "Face for the buffer names in the playlists buffer."
  :group 'emms-metaplaylist-mode)

(defface emms-metaplaylist-mode-current-face
  '((((class color) (background dark))
     (:foreground "red2"))
    (((class color) (background light))
     (:background "red3" :foreground "white"))
    (((type tty) (class mono))
     (:inverse-video t))
    (t (:background "red3")))
  "Face for the current buffer name in the playlists buffer."
  :group 'emms-metaplaylist-mode)

;;; --------------------------------------------------------
;;; Keymap
;;; --------------------------------------------------------

(defconst emms-metaplaylist-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map text-mode-map)
    (define-key map (kbd "n")   'next-line)
    (define-key map (kbd "p")   'previous-line)
    (define-key map (kbd "RET") 'emms-metaplaylist-mode-goto-current)
    (define-key map (kbd "SPC") 'emms-metaplaylist-mode-set-active)
    (define-key map (kbd "g")   'emms-metaplaylist-mode-update)
    (define-key map (kbd "C")   'emms-metaplaylist-mode-new-buffer)
    (define-key map (kbd "C-k") 'emms-metaplaylist-mode-kill-buffer)
    (define-key map (kbd "c")   'emms-metaplaylist-mode-center-current)
    (define-key map (kbd "q")   'kill-this-buffer)
    (define-key map (kbd "?")   'describe-mode)
    map)
  "Keymap for `emms-metaplaylist-mode'.")

;;; --------------------------------------------------------
;;; Metaplaylist
;;; --------------------------------------------------------

(defun emms-metaplaylist-mode-goto-current ()
  "Switch to the buffer at point."
  (interactive)
  (let ((buffer (get-buffer
		 (buffer-substring (point-at-bol)
				   (point-at-eol)))))
  (emms-playlist-set-playlist-buffer buffer)
  (switch-to-buffer buffer)))

(defun emms-metaplaylist-mode-write (playlists)
  "Print the sorted list of PLAYLISTS."
  (delete-region (point-min) (point-max))
  (mapc (lambda (buf)
	  (let ((inhibit-read-only t))
	    (insert (buffer-name buf))
	    (add-text-properties
	     (point-at-bol) (point-at-eol)
	     (list 'face
		   (if (eq buf emms-playlist-buffer)
		       'emms-metaplaylist-mode-current-face
		     'emms-metaplaylist-mode-face)))
	    (newline)))
	playlists))

;; Emms' list changes order, and that's OK, but we want something
;; stable for display purposes.
(defun emms-metaplaylist-mode-sorted-buffer-list ()
  "Return a sorted list of playlist buffers."
  (sort
   (copy-tree		    
    (emms-playlist-buffer-list))
   #'(lambda (a b)
       (string< (buffer-name a)
		(buffer-name b)))))

(defun emms-metaplaylist-mode-center-current ()
  "Center on the current playlist buffer"
  (interactive)
  (when (not emms-playlist-buffer)
    (error "no current playlist buffer"))
  (goto-char (point-min))
  (when (not (search-forward-regexp
	      (or (buffer-name emms-playlist-buffer)
		  "")
	      (point-max) t))
    (goto-char (point-min)))
  (goto-char (point-at-bol)))

(defun emms-metaplaylist-mode-create ()
  "Create the meta-playlist buffer."
  (let ((name emms-metaplaylist-mode-buffer-name)
	(playlists (emms-metaplaylist-mode-sorted-buffer-list)))
    (if playlists
	(with-current-buffer (get-buffer-create name)
	  (emms-metaplaylist-mode)
	  (emms-metaplaylist-mode-write playlists)
	  (emms-metaplaylist-mode-center-current)
	  (current-buffer))
      (error "No Emms playlist buffers"))))

(defun emms-metaplaylist-mode-assert-buffer ()
  "Assert that we are in the metaplaylist mode buffer."
  (when (not (eq (current-buffer)
		 (get-buffer emms-metaplaylist-mode-buffer-name)))
    (error "not the metalplaylist buffer")))

(defun emms-metaplaylist-mode-update ()
  "Update the metalplaylist display."
  (interactive)
  (emms-metaplaylist-mode-assert-buffer)
  (let ((inhibit-read-only t))
    (emms-metaplaylist-mode-write
     (emms-metaplaylist-mode-sorted-buffer-list)))
  (emms-metaplaylist-mode-center-current))

(defun emms-metaplaylist-mode-kill-buffer ()
  "Kill the buffer at point"
  (interactive)
  (let ((buffer (get-buffer
		 (buffer-substring (point-at-bol)
				   (point-at-eol)))))
    (when (not buffer)
      (error "can't find buffer at point"))
    (if (y-or-n-p (format "kill playlist buffer \"%s\"?"
			  (buffer-name buffer)))
	(kill-buffer buffer)
      (message "Buffer kill aborted."))
    (emms-metaplaylist-mode-update)))


;;; --------------------------------------------------------
;;; Playlist Management
;;; --------------------------------------------------------

(defun emms-metaplaylist-mode-new-buffer (buffer-name)
  "Creates a new buffer playlist buffer BUFFER-NAME."
  (interactive "sBuffer Name: ")
  (if (get-buffer buffer-name)
      (error "Buffer must not exist.")
    (let ((buf (get-buffer-create buffer-name)))
      (with-current-buffer buf
	(emms-playlist-mode)
	(setq emms-playlist-buffer-p t)))
    (emms-metaplaylist-mode-update)))

(defun emms-metaplaylist-mode-set-active ()
  "Set the buffer at point to be the active playlist."
  (interactive)
  (emms-playlist-set-playlist-buffer 
   (get-buffer (buffer-substring (point-at-bol) (point-at-eol))))
  (emms-metaplaylist-mode-update))


;;; --------------------------------------------------------
;;; Mode entry
;;; --------------------------------------------------------

(defun emms-metaplaylist-mode-go ()
  "Single entry point to the metaplaylist interface."
  (interactive)
  (let ((mpm-buffer (get-buffer emms-metaplaylist-mode-buffer-name)))
    (if mpm-buffer
	(with-current-buffer mpm-buffer
	  (emms-metaplaylist-mode-update))
      (setq mpm-buffer (emms-metaplaylist-mode-create)))
    (switch-to-buffer mpm-buffer)))

(defun emms-metaplaylist-mode ()
  "A major mode for Emms playlists."
  ;;  (interactive)
  (kill-all-local-variables)

  (use-local-map emms-metaplaylist-mode-map)
  (setq major-mode 'emms-metaplaylist-mode
	mode-name "Emms-MetaPlaylist")

  (setq buffer-read-only t)

  (run-hooks 'emms-metaplaylist-mode-hooks))

(provide 'emms-metaplaylist-mode)

;;; emms-metaplaylist-mode.el ends here
