;;; moccur-edit.el --- apply replaces to multiple files
;; -*- Mode: Emacs-Lisp -*-

;;  $Id: moccur-edit.el,v 2.16 2008/08/01 09:32:18 akihisa Exp $

;; Author: Matsushita Akihisa <akihisa@mail.ne.jp>
;; Keywords: moccur edit

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; moccur-edit provides to edit moccur buffer of color-moccur.el and
;; to apply the changes to the file.

;; This file requires color-moccur.el
;; The latest version of these program can be downloaded from
;; http://www.bookshelf.jp/elc/color-moccur.el.

;;; Install:

;; Put this file into load-path'ed directory, and byte compile it if
;; desired.  And put the following expression into your ~/.emacs.
;;
;;     (require 'moccur-edit)

;; The latest version of this program can be downloaded from
;; http://www.bookshelf.jp/elc/moccur-edit.el

;;; Hint (.emacs)

;; Modified buffers are saved automatically.
;; Thanks request!

;; (defadvice moccur-edit-change-file
;;  (after save-after-moccur-edit-buffer activate)
;;  (save-buffer))

;;; Usage:

;; You can start editing the names of the files by typing "C-c C-i" or
;; "C-x C-q".
;; Use C-c C-f when finished or C-c C-k to abort or C-c C-r to remove
;; the changes in the region.

;; History:

;; moccur-edit 1.0 was released to the net on 12/03/2002

;;; Code:

(require 'color-moccur)

(defgroup moccur-edit nil
  "Customize moccur-edit"
  :group 'matching)

(defface moccur-edit-face
  '((((class color)
      (background dark))
     (:background "Pink" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "ForestGreen" :bold t))
    (t
     ()))
  "*Face used for the changed text on moccur buffer."
  :group 'moccur-edit)

(defface moccur-edit-file-face
  '((((class color)
      (background dark))
     (:background "gray30" :bold t))
    (((class color)
      (background light))
     (:background "ForestGreen" :bold t))
    (t
     ()))
  "*Face used for the changed text on file buffer."
  :group 'moccur-edit)

(defface moccur-edit-done-face
  '((((class color)
      (background dark))
     (:foreground "gray30" :bold t))
    (((class color)
      (background light))
     (:foreground "ForestGreen" :bold t))
    (t
     ()))
  "*Face used for the line on moccur buffer that can apply to file."
  :group 'moccur-edit)

(defface moccur-edit-reject-face
  '((((class color)
      (background dark))
     (:foreground "hot pink" :bold t))
    (((class color)
      (background light))
     (:foreground "red" :bold t))
    (t
     ()))
  "*Face used for the line on moccur buffer that can not apply to file."
  :group 'moccur-edit)

(defcustom moccur-edit-highlight-edited-text nil
  "*Non-nil means to highlight the edited text."
  :group 'moccur-edit
  :type 'boolean
  )

(defcustom moccur-edit-remove-overlays nil
  "*Non-nil means to remove overlays when moccur-quit is run."
  :group 'moccur-edit
  :type 'boolean
  )

(defcustom moccur-edit-remove-overlays-after-save-buffer t
  "*Non-nil means to remove overlays after save-buffer."
  :group 'moccur-edit
  :type 'boolean
  )

(defcustom moccur-query-when-buffer-read-only t
  "*Non-nil means query if read-only buffers should be made writable."
  :group 'moccur-edit
  :type 'boolean)

(defvar moccur-edit-overlays nil)
(defvar moccur-edit-file-overlays nil)
(defvar moccur-edit-result-overlays nil)
(make-local-variable 'moccur-edit-file-overlays)
(defvar moccur-edit-change-face-flg nil)
(defvar moccur-edit-old-content)
(make-local-variable 'moccur-edit-old-content)

(defun moccur-mode-edit-set-key ()
  (define-key moccur-mode-map "r"
    'moccur-edit-mode-in)
  (define-key moccur-mode-map "\C-x\C-q"
    'moccur-edit-mode-in)
  (define-key moccur-mode-map "\C-c\C-i"
    'moccur-edit-mode-in)

  (define-key moccur-ee-mode-map "r"
    'moccur-edit-mode-in)
  (define-key moccur-ee-mode-map "\C-x\C-q"
    'moccur-edit-mode-in)
  (define-key moccur-ee-mode-map "\C-c\C-i"
    'moccur-edit-mode-in)
  )

(if moccur-mode-map
    (moccur-mode-edit-set-key))

(defun moccur-mode-change-face (beg end leng-before)
  (interactive)
  (let ((ov (overlays-in beg end))
        (edit-ov nil)
        (exist-ovelays nil))
    (if moccur-edit-change-face-flg
        (progn
          (save-excursion
            (while ov
              (if (overlay-get (car ov) 'moccur-edit)
                  (setq exist-ovelays t))
              (setq ov (cdr ov)))
            (if exist-ovelays
                ()
              (setq edit-ov (make-overlay (line-beginning-position) (line-end-position)))
              (overlay-put edit-ov 'moccur-edit t)
              (overlay-put edit-ov 'face 'moccur-edit-face)
              (overlay-put edit-ov 'priority 0)
              (setq moccur-edit-overlays (cons edit-ov moccur-edit-overlays))
              ))))))

(defvar moccur-edit-buf "")
(defvar moccur-edit-line "")
(defvar moccur-edit-text "")

(defun moccur-edit-get-info ()
  (save-excursion
    (beginning-of-line)
    (when (re-search-backward "^[-+ ]*Buffer:" nil t)
      (if (re-search-forward "File (grep)" (line-end-position) t)
          (progn
            (if (re-search-forward ":[ ]+\\([^\r\n]+\\)$" (line-end-position) t)
                (setq moccur-edit-buf
                      (cons "grep"
                            (buffer-substring-no-properties
                             (match-beginning 1)
                             (match-end 1))
                            ))
              (setq moccur-edit-buf "grep")))
        (beginning-of-line)
        (if (re-search-forward
             "^[-+ ]*Buffer: \\([^\r\n]*\\) File:" (line-end-position) t)
            (setq moccur-edit-buf (buffer-substring-no-properties
                                   (match-beginning 1)
                                   (match-end 1)))))))
  (save-excursion
    (beginning-of-line)
    (if (re-search-forward "^[ ]*\\([0-9]+\\) \\([^\n]+$\\)" (line-end-position) t)
        (progn
          (setq moccur-edit-line
                (string-to-number (buffer-substring-no-properties
                                   (match-beginning 1)
                                   (match-end 1))))
          (setq moccur-edit-text (buffer-substring-no-properties
                                  (match-beginning 2)
                                  (match-end 2))))))
  )

(defun moccur-edit-change-file ()
  "*The changes on the moccur buffer apply to the file"
  (if buffer-read-only
      (if (and moccur-query-when-buffer-read-only
               (buffer-file-name)
               ;;(file-writable-p (buffer-file-name))
               (y-or-n-p (format "Make buffer %s writable?"
                                 (current-buffer)))
               (or (toggle-read-only -1) t)
               (not buffer-read-only))
          (moccur-edit-change-file)
        (display-warning             ; (Not defined in old Emacses! *)
         'moccur-edit
         (format "Buffer read only: %s" (current-buffer)))
        nil)
    (goto-line moccur-edit-line)
    (delete-region (line-beginning-position)
                   (line-end-position))
    (insert moccur-edit-text)
    t))

(defun moccur-edit-put-color-file ()
  "*Highlight the changed line of the file"
  (let ((fileov))
    (setq fileov (make-overlay
		  (line-beginning-position)
		  (line-end-position)))
    (overlay-put fileov 'face 'moccur-edit-file-face)
    (overlay-put fileov 'priority 0)
    (setq moccur-edit-file-overlays (cons fileov moccur-edit-file-overlays))
    ))

(defun moccur-edit-put-face (face)
  (let ((ov))
    (beginning-of-line)
    (re-search-forward "^[ ]*[0-9]+ " nil t)
    (setq ov (make-overlay (point) (line-end-position)))
    (overlay-put ov 'moccur-edit t)
    (overlay-put ov 'face face)
    (overlay-put ov 'priority 0)
    (setq moccur-edit-result-overlays (cons ov moccur-edit-result-overlays))
    ))

(defun moccur-edit-remove-overlays ()
  "Remove all overlays in all buffers."
  (interactive)
  (save-current-buffer
    (let (ov buf (buflist (buffer-list)))
      (while buflist
        (setq buf (car buflist))
        (setq buflist (cdr buflist))
        (when (and buf
                   (buffer-live-p buf))
          (set-buffer buf)
          (while moccur-edit-file-overlays
            (delete-overlay (car moccur-edit-file-overlays))
            (setq moccur-edit-file-overlays (cdr moccur-edit-file-overlays))))))))

(defadvice moccur-quit (before moccur-edit-kill-buffer activate)
  (when moccur-edit-remove-overlays
    (moccur-edit-remove-overlays)))

(defadvice basic-save-buffer (before moccur-remove-overlays-before-save-buffer activate)
  (when moccur-edit-remove-overlays-after-save-buffer
    (moccur-edit-remove-overlays)))

(defun moccur-edit-finish-edit ()
  "*The changes on the grep buffer apply to the file"
  (interactive)
  (let ((ov) fileov beg filename text line local-buf cbuf line)
    (setq cbuf (current-buffer))
    (while moccur-edit-overlays
      (setq ov (car moccur-edit-overlays))
      (setq moccur-edit-overlays (cdr moccur-edit-overlays))
      (setq beg (overlay-start ov))
      (when beg
        (goto-char beg)
        (moccur-edit-get-info)

        (if (and
             (listp moccur-edit-buf)
             (string= (car moccur-edit-buf) "grep"))
            (set-buffer (find-file-noselect (cdr moccur-edit-buf)))
          (set-buffer moccur-edit-buf))
        ;; <WL: fixed a bug here>
        (if (moccur-edit-change-file)
            ;; File is changed. t: success
            (progn
              (when moccur-edit-highlight-edited-text
                (moccur-edit-put-color-file)) ;; Highlight changed text
              (set-buffer cbuf)
              (moccur-edit-put-face 'moccur-edit-done-face))
         (set-buffer cbuf)
         (moccur-edit-put-face 'moccur-edit-reject-face))
        ;; Return previous buffer
        (set-buffer cbuf)
        (delete-overlay ov)
        )))
  (moccur-edit-reset-key))

(defun moccur-edit-remove-change (beg end)
  (interactive "r")
  (let ((ov (overlays-in beg end)))
    (while ov
      (if (overlay-get (car ov) 'moccur-edit)
          (delete-overlay (car ov)))
      (setq ov (cdr ov))))
  (setq mark-active nil))

(defun moccur-edit-mode-in ()
  (interactive)
  (moccur-edit-mode)
  (force-mode-line-update)
  (setq moccur-edit-old-content
        (buffer-substring (point-min) (point-max)))
  (setq moccur-edit-change-face-flg nil)
  (setq buffer-read-only nil)
  (moccur-edit-set-readonly-area)
  (setq moccur-edit-change-face-flg t)

  (setq line-move-ignore-invisible nil)
  ;; Cause use of ellipses for invisible text.
  (setq buffer-invisibility-spec nil)

  (add-hook 'after-change-functions 'moccur-mode-change-face nil t)
  )

(defun current-line ()
  "Return the vertical position of point..."
  (1+ (count-lines 1 (point))))

(defun max-line ()
  "Return the vertical position of point..."
  (save-excursion
    (goto-char (point-max))
    (current-line)))

(defun moccur-edit-kill-all-change ()
  (interactive)
  (let (pos)
    (setq pos (current-line))
    (moccur-edit-remove-change (point-min) (point-max))
    (moccur-edit-reset-key)
    (let ((inhibit-read-only t))
      (erase-buffer)
      (if (and (string= mode-name "Moccur-ee")
               (get-buffer "*Moccur*"))
          (progn
            (if (get-buffer "*ee-outline*/*Moccur*")
                (kill-buffer (get-buffer "*ee-outline*/*Moccur*")))
            (switch-to-buffer (get-buffer "*Moccur*"))
            ;;(set-buffer (get-buffer "*Moccur*"))
            (ee-outline)
            (moccur-mode t)
            ;;(use-local-map moccur-mode-map)
            (setq moccur-mocur-buffer (current-buffer))
            ;; highlight Moccur buffer
            (moccur-buffer-color)
            ;;(insert-before-markers-and-inherit moccur-edit-old-content)
            )
        (insert moccur-edit-old-content)
        (moccur-buffer-color)
        ))
    (if (> pos (max-line))
        (goto-line (max-line))
      (goto-line pos))
    ))

(defun moccur-edit-set-readonly-area ()
  (let ((inhibit-read-only t) beg end)
    (save-excursion
      (goto-char (point-min))
      (setq beg (point))
      (end-of-line)
      (setq end (point))
      (put-text-property beg end 'read-only t)
      (put-text-property beg end 'front-sticky '(read-only))
      (while (re-search-forward "\\(^[-+ ]*Buffer: [^\n]*File[^\n]+$\\)" nil t)
        (put-text-property (match-beginning 0)
                               (match-end 0) 'read-only t)
        (put-text-property (match-beginning 0) (match-end 0) 'front-sticky '(read-only)))
      (goto-char (point-min))
      (while (re-search-forward "\\(^[ ]*[0-9]+\\)" nil t)
        (put-text-property (match-beginning 1)
                           (match-end 1) 'read-only t)
        (put-text-property (match-beginning 0) (match-end 0) 'front-sticky '(read-only)))
      (goto-char (point-min))
      (while (re-search-forward "^\\([\r\n]+\\)" nil t)
        (put-text-property (match-beginning 1)
                           (match-end 1) 'read-only t)
        (put-text-property (match-beginning 0) (match-end 0) 'front-sticky '(read-only)))
      )))

(defun moccur-edit-reset-key ()
  (interactive)
  (setq buffer-read-only t)
  (cond
   ((string= mode-name "Moccurg-edit")
    (moccur-grep-mode))
   ((string= mode-name "Moccure-edit")
    (moccur-mode t))
   (t
    (moccur-mode)))
  (make-local-variable 'line-move-ignore-invisible)
  (setq line-move-ignore-invisible t)
  (if (not (and (boundp 'running-xemacs) running-xemacs))
      (add-to-invisibility-spec '(moccur . t)))
  (force-mode-line-update)
  )

;; moccur-mode
(defvar moccur-edit-mode-map ())
(defun moccur-edit-set-key ()
  (define-key moccur-edit-mode-map '[down] 'moccur-next)
  (define-key moccur-edit-mode-map '[up] 'moccur-prev)
  (define-key moccur-edit-mode-map "\C-c\C-r"
    'moccur-edit-remove-change)
  (define-key moccur-edit-mode-map "\C-c\C-f"
    'moccur-edit-finish-edit)
  (define-key moccur-edit-mode-map "\C-x\C-s"
    'moccur-edit-finish-edit)
  (define-key moccur-edit-mode-map "\C-c\C-c"
    'moccur-edit-finish-edit)
  (define-key moccur-edit-mode-map "\C-c\C-k"
    'moccur-edit-kill-all-change)
  (define-key moccur-edit-mode-map "\C-xk"
    'moccur-edit-kill-all-change)
  (define-key moccur-edit-mode-map "\C-ck"
    'moccur-edit-kill-all-change)
  (define-key moccur-edit-mode-map "\C-c\C-u"
    'moccur-edit-kill-all-change)
  )

(if moccur-edit-mode-map
    ()
  (setq moccur-edit-mode-map (make-sparse-keymap))
  (moccur-edit-set-key)
  )

(defun moccur-edit-mode ()
  "Major mode"
  (let ((ee
         (cond
          ((string= major-mode 'moccur-grep-mode)
           'grep)
          ((string= "Moccur-ee" mode-name)
           'ee)
          (t nil))))
    (kill-all-local-variables)
    (use-local-map moccur-edit-mode-map)
    (setq major-mode 'moccur-edit-mode)
    (cond
     ((string= ee 'grep)
      (setq mode-name "Moccurg-edit"))
     ((string= ee 'ee)
      (setq mode-name "Moccure-edit"))
     (t
      (setq mode-name "Moccur-edit")))
    (moccur-edit-set-key)))

;; advice for query-replace
(defun moccur-edit-add-skip-in-replace (command)
  "Advice COMMAND to skip matches while they have read-only properties.
This is useful to avoid \"read-only\" errors in search and replace
commands.  This advice only has effect in moccur-edit mode."
  (eval
   `(defadvice ,command (around moccur-edit-discard-read-only activate)
      ,(format "Make %s to work better with moccur-edit,\n%s."  command
               "skipping read-only matches when invoked without argument")
      ad-do-it
      (if (eq major-mode 'moccur-edit-mode)
          (while (and ad-return-value
                      (text-property-any
                       (max 1 (1- (match-beginning 0))) (match-end 0)
                       'read-only t))
            ad-do-it))
      ad-return-value)))

(defun moccur-edit-replace-advice (command)
  "Advice COMMAND to skip matches while they have read-only properties.
This is useful to avoid \"read-only\" errors in search and replace
commands.  This advice only has effect in moccur-edit mode."
  (eval
   `(defadvice ,command (around moccur-edit-grok-read-only activate)
      ,(format "Make %s to work better with moccur-edit,\n%s."  command
               "skipping read-only matches when invoked without argument")
      (if (eq major-mode 'moccur-edit-mode)
          (progn
            (moccur-edit-add-skip-in-replace 'search-forward)
            (moccur-edit-add-skip-in-replace 're-search-forward)
            (unwind-protect
                ad-do-it
              (progn
                (ad-remove-advice 'search-forward
                                  'around 'moccur-edit-discard-read-only)
                (ad-remove-advice 're-search-forward
                                  'around 'moccur-edit-discard-read-only)
                (ad-update 'search-forward)
                (ad-update 're-search-forward))))
        ad-do-it)
      ad-return-value)))

(defadvice moccur-mode (after moccur-edit-set-key activate)
  (moccur-mode-edit-set-key))

(defadvice moccur-grep-mode (after moccur-edit-set-key activate)
  (moccur-mode-edit-set-key))

(mapcar 'moccur-edit-replace-advice
        '(query-replace query-replace-regexp replace-string))

(provide 'moccur-edit)
;;; moccur-edit.el ends here
