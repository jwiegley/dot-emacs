;;; stopwatch.el --- stop watch

;;; Commentary:
;;
;; Version 1
;;
;; M-x stopwatch stop and starts the stopwatch
;;
;; Within the stopwatch buffer the space bar toggles the stop watch
;; and q kills the buffer
;;
;; The latest version is available at
;;
;; http://kanis.fr/vcs/emacs/ivan/stopwatch.el
;;
;;; THANKS:

;;; BUGS:

;;; INSTALLATION:
;;
;; put this file somewhere in your load path
;; put the following in your emacs:
;;
;; (require 'stopwatch)
;;
;; Alternatively you can use autoload mechanism
;;
;; If you are going to use this often you probably want to bind it to
;; a key, for example to bind it to function 9 you would do:
;;
;; (global-set-key (kbd "<f9>") 'stopwatch)

;;; Code:

(defvar stopwatch-buffer-name "*stopwatch*"
  "Name of the stop watch buffer.")

(defvar stopwatch-update-interval 1
  "Time in seconds of the stop watch update.")

(defvar stopwatch-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map " " 'stopwatch-toggle)
    (define-key map "q" 'stopwatch-exit)
    map)
  "Keymap of the stop watch mode")

;; internal variables
(defvar stopwatch-start nil)
(defvar stopwatch-timer nil)

;;;###autoload
(defun stopwatch ()
  "Setup stopwatch buffer and mode then toggles timer."
  (interactive)
  (with-current-buffer (get-buffer-create stopwatch-buffer-name)
    (pop-to-buffer stopwatch-buffer-name)
    (fit-window-to-buffer)
    (stopwatch-timer-start)
    (stopwatch-mode)
    (stopwatch-toggle)))

(defun stopwatch-mode ()
  "Stopwatch mode setup key bindings."
  (kill-all-local-variables)
  (setq
   buffer-undo-list t
   major-mode 'stopwatch-mode
   mode-name "Stop watch")
  (use-local-map stopwatch-mode-map))

(defun stopwatch-exit ()
  "Exit stop watch, cancel timer, set time to zero."
  (interactive)
  (let ((window (get-buffer-window stopwatch-buffer-name)))
    (kill-buffer stopwatch-buffer-name)
    (stopwatch-timer-stop)
    (setq stopwatch-start nil)
    (when (and window (not (one-window-p window)))
      (delete-window window))))

(defun stopwatch-timer-start ()
  "Start stopwatch timer."
  (when (not stopwatch-timer)
    (setq stopwatch-timer
          (run-at-time t stopwatch-update-interval 'stopwatch-display))))

(defun stopwatch-timer-stop ()
  "Stop stopwatch timer."
  (when stopwatch-timer
    (cancel-timer stopwatch-timer)
    (setq stopwatch-timer nil)))
  
(defun stopwatch-toggle ()
  "Turn stopwatch on and off."
  (interactive)
  (with-current-buffer stopwatch-buffer-name
    (setq buffer-read-only nil)
    (erase-buffer)
    (if stopwatch-start
        (progn
          (insert (stopwatch-human (stopwatch-delta) t))
          (setq stopwatch-start nil)
          (stopwatch-timer-stop))
      (setq stopwatch-start (current-time))
      (insert "00:00 00'")
      (stopwatch-timer-start))
    (setq buffer-read-only t)))

(defun stopwatch-display ()
  "Stopwatch timer function will update display"
  (with-current-buffer stopwatch-buffer-name
    (setq buffer-read-only nil)
    (erase-buffer)
    (insert (stopwatch-human (stopwatch-delta)))
    (setq buffer-read-only t)))

(defun stopwatch-delta ()
  "Calculate time difference from timer start."
  (time-subtract (current-time) stopwatch-start))

(defun stopwatch-human (time &optional show-fraction)
  "Turn epoch time to human readable format."
  (let ((total-second (+ (lsh (car time) 16) (nth 1 time)))
        (second 0)
        (minute 0)
        (hour 0)
        (day 0))
    (when (not (= total-second 0))
        (setq minute (/ total-second 60))
        (setq second (% total-second 60)))
    (when (> minute 59)
      (setq hour (/ minute 60))
      (setq minute (% minute 60)))
    (when (> hour 23)
      (setq day (/ hour 24))
      (setq hour (% hour 24)))
    (concat
     (when (not (= day 0))
       (format "%d day " day))
     (format "%02d:%02d %02d'" hour minute second)
     (when show-fraction
       (format "%02d" (/ (nth 2 time) 10000))))))

(provide 'stopwatch)

;; Local Variables:
;; compile-command: "make"
;; End:

;; Copyright (C) 2011 Ivan Kanis
;; Author: Ivan Kanis
;;
;; This program is free software ; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation ; either version 2 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY ; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program ; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
;;
;; vi:et:sw=4:ts=4:
