;;; super-save.el --- Auto-save buffers, based on your activity. -*- lexical-binding: t -*-

;; Copyright © 2015-2016 Bozhidar Batsov <bozhidar@batsov.com>

;; Author: Bozhidar Batsov <bozhidar@batsov.com>
;; URL: https://github.com/bbatsov/super-save
;; Keywords: convenience
;; Version: 0.2.0
;; Package-Requires: ((emacs "24.4"))

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; super-save saves buffers when they lose focus.
;;
;;; Code:
(defgroup super-save nil
  "Smart-saving of buffers."
  :group 'tools
  :group 'convenience)

(defvar super-save-mode-map (make-sparse-keymap)
  "super-save mode's keymap.")

(defcustom super-save-triggers
  '("switch-to-buffer" "other-window" "windmove-up" "windmove-down" "windmove-left" "windmove-right" "next-buffer" "previous-buffer")
  "A list of commands which would trigger `super-save-command'."
  :group 'super-save
  :type '(repeat string))

(defcustom super-save-auto-save-when-idle nil
  "Save current buffer automatically when Emacs is idle."
  :group 'super-save
  :type 'boolean)

(defcustom super-save-idle-duration 5
  "The number of seconds Emacs has to be idle, before auto-saving the current buffer.
See `super-save-auto-save-when-idle'."
  :group 'super-save
  :type 'integer)

(defun super-save-command ()
  "Save the current buffer if needed."
  (when (and buffer-file-name
             (buffer-modified-p (current-buffer))
             (file-writable-p buffer-file-name))
    (save-buffer)))

(defvar super-save-idle-timer)

(defun super-save-command-advice (&rest _args)
  "A simple wrapper around `super-save-command' that's advice-friendly."
  (super-save-command))

(defun super-save-advise-trigger-commands ()
  "Apply super-save advice to the commands listed in `super-save-triggers'."
  (mapc (lambda (command)
          (advice-add (intern command) :before #'super-save-command-advice))
        super-save-triggers))

(defun super-save-remove-advice-from-trigger-commands ()
  "Remove super-save advice from to the commands listed in `super-save-triggers'."
  (mapc (lambda (command)
          (advice-remove (intern command) #'super-save-command-advice))
        super-save-triggers))

(defun super-save-initialize-idle-timer ()
  "Initialize super-save idle timer if `super-save-auto-save-when-idle' is true."
  (setq super-save-idle-timer
        (when super-save-auto-save-when-idle
          (run-with-idle-timer super-save-idle-duration t #'super-save-command))))

(defun super-save-stop-idle-timer ()
  "Stop super-save idle timer if `super-save-idle-timer' is set."
  (when super-save-idle-timer
    (cancel-timer super-save-idle-timer)))

(defun super-save-initialize ()
  "Setup super-save's advices and hooks."
  (super-save-advise-trigger-commands)
  (super-save-initialize-idle-timer)
  (add-hook 'mouse-leave-buffer-hook #'super-save-command)
  (add-hook 'focus-out-hook #'super-save-command))

(defun super-save-stop ()
  "Cleanup super-save's advices and hooks."
  (super-save-remove-advice-from-trigger-commands)
  (super-save-stop-idle-timer)
  (remove-hook 'mouse-leave-buffer-hook #'super-save-command)
  (remove-hook 'focus-out-hook #'super-save-command))

;;;###autoload
(define-minor-mode super-save-mode
  "A minor mode that saves your Emacs buffers when they lose focus."
  :lighter " super-save"
  :keymap super-save-mode-map
  :group 'super-save
  :global t
  (cond
   (super-save-mode (super-save-initialize))
   (t (super-save-stop))))

(provide 'super-save)
;;; super-save.el ends here
