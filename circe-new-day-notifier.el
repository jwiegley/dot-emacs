;;; circe-new-day-notifier.el --- Send a message every midnight to all
;;; channels

;; Copyright (C) 2015 Pásztor János

;; Author: Pásztor János <model87@freemail.hu>

;; This file is part of Circe.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301 USA

;;; Commentary:

;; This Circe module adds the ability to send a notification to all
;; channels every midnight

;; Some ideas/code copied from circe-lagmon.el and
;; circe-color-nicks.el

;; To use it, put the following into your .emacs:

;; (require 'circe-new-day-notifier)
;; (enable-circe-new-day-notifier)

;;; Code:

(require 'circe)

(defgroup circe-new-day-notifier nil
  "Midnight notification to Circe"
  :prefix "circe-new-day-notifier-"
  :group 'circe)

(defcustom circe-new-day-notifier-format-message "*** Day changed to {day}"
  "The format string which will be printed to the channels. It
should contain {day} to print the date. See `circe-display' for
further documentation"
  :type 'string
  :group 'circe-new-day-notifier)

(defcustom circe-new-day-notifier-date-format "%Y-%m-%d, %A"
  "The date format, which will be used at
circe-new-day-notifier-format-message. See `format-time-string' for
documentation"
  :type 'string
  :group 'circe-new-day-notifier)

(defvar circe-new-day-notifier-timer nil)

;;;###autoload
(defun enable-circe-new-day-notifier ()
  (interactive)
    (unless circe-new-day-notifier-timer
      (setq circe-new-day-notifier-timer
            (run-at-time "24:00:00" (* 24 60 60) 'circe-new-day-notification))))

;;;###autoload
(defun disable-circe-new-day-notifier ()
  (interactive)
  (when circe-new-day-notifier-timer
    (cancel-timer circe-new-day-notifier-timer)
    (setq circe-new-day-notifier-timer nil)))

(defun circe-new-day-notification ()
  "This function prints the new day notification to each query and chat buffer"
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (derived-mode-p 'circe-chat-mode)
        (circe-display 'circe-new-day-notifier-format-message
                       :day (format-time-string circe-new-day-notifier-date-format))))))

(provide 'circe-new-day-notifier)
;;; circe-new-day-notifier.el ends here
