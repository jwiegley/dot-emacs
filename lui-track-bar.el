;;; lui-track-bar.el --- Provides a bar to track the last read position

;; Copyright (C) 2016 Vasilij Schneidermann <v.schneidermann@gmail.com>

;; Author: Vasilij Schneidermann <v.schneidermann@gmail.com>

;; This file is part of LUI.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301  USA

;;; Commentary:

;; This allows you to track where you've last left off a buffer.

;; Use (enable-lui-track-bar) to enable this mode globally. You can
;; customize `lui-track-bar-behavior' to change when the track bar
;; moves. You can also use M-x lui-track-bar-move to move the track
;; bar manually.

;;; Code:

(require 'lui)
(require 'tracking)

(defgroup lui-track-bar nil
  "Last read position tracking for LUI"
  :prefix "lui-track-bar-"
  :group 'lui)

(defcustom lui-track-bar-behavior 'before-switch-to-buffer
  "When to move the track bar.

The following values are possible.

before-switch-to-buffer (default)
  Move the bar to the bottom of the buffer when switching away
  from a buffer.

before-tracking-next-buffer
  Move the bar when switching to the next buffer using
  \\[tracking-next-buffer].

after-send
  Move the bar after sending a message."
  :type '(choice (const :tag "Before switching buffers"
                        before-switch-to-buffer)
                 (const :tag "Before tracking switch"
                        before-tracking-next-buffer)
                 (const :tag "After sending"
                        after-send))
  :group 'lui-track-bar)

(defface lui-track-bar
  '((((type graphic) (background light))
     :inherit default :background "dim gray" :height 0.1)
    (((type graphic) (background dark))
     :inherit default :background "light gray" :height 0.1)
    (((type tty))
     :inherit (font-lock-comment-face default) :underline t))
  "Track bar face"
  :group 'lui-track-bar)

(defvar lui-track-bar-overlay nil)
(make-variable-buffer-local 'lui-track-bar-overlay)

;;;###autoload
(defun enable-lui-track-bar ()
  "Enable a bar in Lui buffers that shows where you stopped reading."
  (interactive)
  (defadvice switch-to-buffer (before lui-track-bar activate)
    (when (and (eq lui-track-bar-behavior 'before-switch-to-buffer)
               ;; Do not move the bar if the buffer is displayed still
               (<= (length (get-buffer-window-list (current-buffer)))
                   1))
      (lui-track-bar-move)))
  (defadvice tracking-next-buffer (before lui-track-bar activate)
    (when (eq lui-track-bar-behavior 'before-tracking-next-buffer)
      (lui-track-bar-move)))
  (add-hook 'lui-pre-input-hook 'lui-track-bar--move-pre-input))

(defun lui-track-bar--move-pre-input ()
  (when (eq lui-track-bar-behavior 'after-send)
    (lui-track-bar-move)))

(defun lui-track-bar-move ()
  "Move the track bar down."
  (interactive)
  (when (derived-mode-p 'lui-mode)
    (when (not lui-track-bar-overlay)
      (setq lui-track-bar-overlay (make-overlay (point-min) (point-min)))
      (overlay-put lui-track-bar-overlay 'after-string
                   (propertize "\n" 'face 'lui-track-bar)))
    (move-overlay lui-track-bar-overlay
                  lui-output-marker lui-output-marker)))

(provide 'lui-track-bar)
;;; lui-track-bar.el ends here
