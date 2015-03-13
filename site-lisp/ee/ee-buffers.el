;;; ee-buffers.el --- display and manipulate Emacs buffers

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee

;; This file is [not yet] part of GNU Emacs.

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this package; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; See the file README and documentation for more information.

;;; Code:

(require 'ee)

;;; Constants

(defconst ee-buffers-mode-name "ee-buffers")

;;; Customizable Variables

(defgroup ee-buffers nil
  "Display and manipulate Emacs buffers."
  :prefix "ee-buffers-"
  :group 'ee)

;; TODO: move to view/buffers.ee?
(defcustom ee-buffers-auto-refresh nil;t
  "Refresh ee-buffers view buffer if buffer is visible."
  :type 'boolean
  :group 'ee-buffers)

;; TODO: move to view/buffers.ee?
(defcustom ee-buffers-faded-timeout 600 ;3600
  "Timeout in seconds, after which items will be displayed in ee-shadow."
  :type 'integer
  :group 'ee-buffers)

(defcustom ee-buffers-directory-name-regexp-alist nil
  "Alist of directory name patterns vs corresponding category names.
Each element looks like (REGEXP . CATEGORY-NAME).
Used in the view description to place the buffer file directory name
into different categories depending on the file directory name.

Example:
  '((\"ee\" . \"ee\")
    (\"emacs\" . \"emacs\")
    (\"\\\\(html\\\\|www\\\\)\" . \"www\"))"
  :type '(repeat (cons (regexp :tag "Directory name regexp")
                       (string :tag "Category name")))
  :group 'ee-buffers)

(defcustom ee-buffers-file-name-regexp-alist nil
  "Alist of file name patterns vs corresponding category names.
Each element looks like (REGEXP . CATEGORY-NAME).
Used in the view description to place the buffer file directory name
into different categories depending on the file name.

Example:
  '((\".emacs\" . \"emacs\"))"
  :type '(repeat (cons (regexp :tag "File name regexp")
                       (string :tag "Category name")))
  :group 'ee-buffers)

;;; Global Variables

(defvar ee-buffers-mark-save 'S
  "Symbol used to mark records for saving.")

;;; Buffer-Local Variables

(defvar ee-buffers-prev-buffer nil
  "Previously visited buffer.")
(make-variable-buffer-local 'ee-buffers-prev-buffer)

;;; Data Description

(defvar ee-buffers-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/buffers.ee")
     (collector . ee-buffers-data-collect)
     (fields type buffer buffer-name major-mode mode-name file-name directory size read-only modified modtime display-time display-count file-truename file-format file-coding-system mark ())
     (key-fields buffer))])

;;; Data Extraction

(defun ee-buffers-data-collect (data)
  (let* ((field-names (ee-data-meta-field-get data 'fields)) ;; TODO: use (ee-data-field-names data)?
         (old-data (if ee-data
                       (mapcar (lambda (r)
                                 (ee-field 'buffer r))
                               (ee-data-records-find ee-data '(mark . D)))))
         (new-data
          (ee-data-convert-lists-to-vectors
           (mapcar
            (lambda (buffer)
              (with-current-buffer buffer
                (mapcar
                 (lambda (field-name)
                   (cond
                    ((eq field-name 'type) 'buffer) ; TEST
                    ((eq field-name 'buffer) buffer)
                    ((eq field-name 'buffer-name) (buffer-name buffer))
                    ((eq field-name 'major-mode) major-mode)
                    ((eq field-name 'mode-name) (format-mode-line mode-name nil nil buffer))
                    ((eq field-name 'file-name) (buffer-file-name buffer))
                    ((eq field-name 'directory) default-directory)
                    ((eq field-name 'size) (buffer-size))
                    ((eq field-name 'saved-size) buffer-saved-size) ; NOT USED
                    ((eq field-name 'backed-up) buffer-backed-up) ; NOT USED
                    ((eq field-name 'read-only) buffer-read-only)
                    ((eq field-name 'modified) (buffer-modified-p buffer))
                    ((eq field-name 'modtime) (visited-file-modtime))
                    ((eq field-name 'display-time)
                     (and (boundp 'buffer-display-time) buffer-display-time))
                    ((eq field-name 'display-count)
                     (and (boundp 'buffer-display-count) buffer-display-count))
                    ((eq field-name 'file-truename) buffer-file-truename)
                    ((eq field-name 'file-format) buffer-file-format)
                    ((eq field-name 'file-coding-system) buffer-file-coding-system)))
                 field-names)))
            (buffer-list (selected-frame))))))
    (aset new-data 0 (aref data 0))
    (if old-data
        (ee-data-records-do
         new-data
         (lambda (r ri)
           (if (memq (ee-field 'buffer r) old-data)
               (ee-field-set 'mark 'D r)))))
    new-data))

(defun ee-buffers-buffer-name ()
  (format "*%s*" ee-buffers-mode-name))

(defun ee-buffers-post-update ()
  "Find previously visited buffer to place point on it after calling ee-buffers."
  (let ((data-getters (ee-data-meta-getters-get-set ee-data)))
    (or ee-current-c-key-field
        ee-current-r-key-field
        (ee-view-record-by-key ee-parent-buffer))
    (if (eq ee-parent-buffer (ee-field 'buffer))
        (if ee-buffers-prev-buffer
            (ee-view-record-by-key ee-buffers-prev-buffer)
          (ee-view-record-next)))
    (or (eq ee-buffers-prev-buffer ee-parent-buffer)
        (setq ee-buffers-prev-buffer ee-parent-buffer))))

;;; Buffers view functions

;; TODO: better name?
(defun ee-buffers-view-buffer-current ()
  (interactive)
  (let ((buffers (member ee-parent-buffer (buffer-list (selected-frame)))))
    (if buffers
        ;; cycle buffers until visible is found
        (while (not (ee-view-record-by-key (car buffers)))
          (setq buffers (cdr buffers))))))

(defun ee-buffers-view-buffer-next ()
  (interactive)
  (let ((buffers (cdr (member (ee-field 'buffer) (buffer-list (selected-frame))))))
    (if buffers
        ;; cycle buffers until visible is found
        (while (not (ee-view-record-by-key (car buffers)))
          (setq buffers (cdr buffers)))))
  ;; TODO: rename to ee-buffers-view-buffer-next-or-prev
  ;; and by C-u change direction to prev/next
  )

(defun ee-buffers-view-buffer-visible ()
  (let ((buf (get-buffer (ee-buffers-buffer-name)))
        visible)
    (walk-windows
     (lambda (w) (if (eq (window-buffer w) buf) (setq visible t)))
     nil
     'visible)
    visible))

;; TODO: add condition of auto-refresh to view description
;; TODO: look why deep recursion occurs here
;; TODO: move next functions to ee.el
(defun ee-buffers-auto-refresh-view-buffer ()
  (if (eq (current-buffer) (get-buffer (ee-buffers-buffer-name))) ;; (ee-buffers-view-buffer-visible)
      (let ((buffer (get-buffer (ee-buffers-buffer-name))))
        (if buffer
            (with-current-buffer buffer
              ;; (ee-view-record-next)
              (ee-view-buffer-update t))))))

(defun ee-buffers-auto-refresh-delay ()
  "Add `ee-buffers-auto-refresh-delayed' to `post-command-hook'.
For use on, eg, `kill-buffer-hook', to update view buffer
after some buffer deletion."
  (if t ;; TODO: ee-update-after-kill-buffer-p
      (add-hook 'post-command-hook
                'ee-buffers-auto-refresh-delayed)))

(defun ee-buffers-auto-refresh-delayed ()
  "Rerationalize buffer names and remove self from `post-command-hook'.
See also `ee-buffers-auto-refresh-delay' for hook setter."
  (let ((buffer (get-buffer (ee-buffers-buffer-name))))
    (if buffer
        (with-current-buffer buffer
          (ee-view-record-next)
          (ee-view-buffer-update t))))
  (remove-hook 'post-command-hook
               'ee-buffers-auto-refresh-delayed))

;; TODO: toggle
;; TODO: FEATURE-unload-hook
(defun ee-buffers-auto-refresh-hook-change ()
  (interactive)
  ;;   (if ee-buffers-auto-refresh
  ;;       (add-hook 'post-command-hook 'ee-buffers-auto-refresh-view-buffer)
  ;;     (remove-hook 'post-command-hook 'ee-buffers-auto-refresh-view-buffer))
  (if ee-buffers-auto-refresh
      (add-hook 'kill-buffer-hook 'ee-buffers-auto-refresh-delay)
    (remove-hook 'kill-buffer-hook 'ee-buffers-auto-refresh-delay)))

(ee-buffers-auto-refresh-hook-change)

;;; Actions

(defun ee-buffers-switch-to-buffer (&optional arg other-window)
  (interactive)
  (let ((buffer (ee-field 'buffer)))
    (if (and buffer (buffer-name buffer))
        (cond ((eq other-window 'display) (display-buffer buffer t))
              (other-window (switch-to-buffer-other-window buffer))
              (t (switch-to-buffer buffer)))
      (error "Invalid buffer"))))

(defun ee-buffers-switch-to-buffer-other-window (&optional arg)
  (interactive)
  (ee-buffers-switch-to-buffer arg t))

(defun ee-buffers-display-buffer (&optional arg)
  (interactive)
  (ee-buffers-switch-to-buffer arg 'display))

(defun ee-buffers-mark-save (&optional arg)
  "Mark buffer on this line to be saved by \\<ee-mode-map>\\[ee-view-records-execute] command.
Prefix arg is how many records to save.
Negative arg means save backwards."
  (interactive "p")
  (ee-view-mark-lines ee-data-mark-field-name ee-buffers-mark-save arg))

(defun ee-buffers-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-mark-del)
            (let ((buffer (ee-field 'buffer r)))
              (if (not (eq (get-buffer (ee-buffers-buffer-name)) buffer))
                  (kill-buffer buffer))))
           ((eq mark ee-buffers-mark-save)
            (with-current-buffer (ee-field 'buffer r)
              (save-buffer)))))
        marks))

;;; Key Bindings

(defvar ee-buffers-keymap nil
  "Local keymap for ee-buffers mode.")

;; TODO: move to defvar
(defun ee-buffers-keymap-make-default ()
  "Defines default key bindings for `ee-buffers-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "s" 'ee-buffers-mark-save)
    (define-key map "." 'ee-buffers-view-buffer-current)
    (define-key map "," 'ee-buffers-view-buffer-next)
    (define-key map "o" 'ee-buffers-switch-to-buffer-other-window)
    (define-key map "\C-o" 'ee-buffers-display-buffer)

    ;; TODO: other bindings from buff-menu.el
    ;(define-key map "v" 'Buffer-menu-select)
    ;;     (define-key map "2" 'Buffer-menu-2-window)
    ;;     (define-key map "1" 'Buffer-menu-1-window)
    ;;     (define-key map "f" 'Buffer-menu-this-window)
    ;; ;;     (define-key map "e" 'Buffer-menu-this-window)
    ;;     (define-key map "\C-m" 'Buffer-menu-this-window)
    ;;     (define-key map "\177" 'Buffer-menu-backup-unmark)
    ;;     (define-key map "~" 'Buffer-menu-not-modified)
    ;;     (define-key map "t" 'Buffer-menu-visit-tags-table)
    ;;     (define-key map "%" 'Buffer-menu-toggle-read-only)
    ;;     (define-key map [mouse-2] 'Buffer-menu-mouse-select)

    ;; HINT: next is useful with (define-key global-map [(control tab)] 'ee-buffers)
    (define-key map [(control tab)] 'ee-buffers-switch-to-buffer)
    (setq ee-buffers-keymap map)))

(or ee-buffers-keymap
    (ee-buffers-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-buffers (&optional arg)
  "Display and manipulate Emacs buffers."
  (interactive "P")
  (ee-view-buffer-create
   (ee-buffers-buffer-name)
   ee-buffers-mode-name
   ee-buffers-keymap
   ee-buffers-data))

(provide 'ee-buffers)

;;; ee-buffers.el ends here
