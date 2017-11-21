;;; vlf-follow.el --- VLF chunk follows point functionality  -*- lexical-binding: t -*-

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Keywords: large files, follow, recenter
;; Author: Andrey Kotlarski <m00naticus@gmail.com>
;; URL: https://github.com/m00natic/vlfi

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
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;; This package provides `vlf-toggle-follow' command which toggles
;; continuous recenter of chunk around current point.

;;; Code:

(require 'vlf)

(defvar vlf-follow-timer nil
  "Contains timer if vlf buffer is set to continuously recenter.")
(make-variable-buffer-local 'vlf-follow-timer)
(put 'vlf-follow-timer 'permanent-local t)

(defun vlf-recenter (vlf-buffer)
  "Recenter chunk around current point in VLF-BUFFER."
  (and vlf-follow-timer
       (eq (current-buffer) vlf-buffer)
       (or (pos-visible-in-window-p (point-min))
           (pos-visible-in-window-p (point-max)))
       (let ((current-pos (+ vlf-start-pos (position-bytes (point))))
             (half-batch (/ vlf-batch-size 2)))
         (if (buffer-modified-p)
             (progn
               (let ((edit-end (+ (position-bytes (point-max))
                                  vlf-start-pos)))
                 (vlf-move-to-chunk (min vlf-start-pos
                                         (- current-pos half-batch))
                                    (max edit-end
                                         (+ current-pos half-batch))))
               (goto-char (byte-to-position (- current-pos
                                               vlf-start-pos))))
           (vlf-move-to-batch (- current-pos half-batch))
           (and (< half-batch current-pos)
                (< half-batch (- vlf-file-size current-pos))
                (goto-char (byte-to-position (- current-pos
                                                vlf-start-pos))))))))

(defun vlf-stop-follow ()
  "Stop continuous recenter."
  (when vlf-follow-timer
    (cancel-timer vlf-follow-timer)
    (setq vlf-follow-timer nil)))

(defun vlf-start-follow (interval)
  "Continuously recenter chunk around point every INTERVAL seconds."
  (setq vlf-follow-timer (run-with-idle-timer interval interval
                                              'vlf-recenter
                                              (current-buffer)))
  (add-hook 'kill-buffer-hook 'vlf-stop-follow nil t))

(defun vlf-toggle-follow ()
  "Toggle continuous chunk recenter around current point."
  (interactive)
  (if vlf-mode
      (if vlf-follow-timer
          (progn (vlf-stop-follow)
                 (message "Following stopped"))
        (vlf-start-follow (read-number "Number of seconds: " 1)))))

(provide 'vlf-follow)

;;; vlf-follow.el ends here
