;;; alert --- Growl-style notification system for Emacs

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 24 Aug 2011
;; Version: 1.0
;; Keywords: notification emacs message
;; X-URL: https://github.com/jwiegley/alert

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Alert is a Growl-workalike for Emacs that uses a common notification
;; interface with multiple, selectable "styles", whose use can be fully
;; customized by the user.  They can even use multiple styles for a given
;; event.  It pretty much works just like Growl, so I'd recommend learning
;; about how that system functions if this doesn't make sense.
;;
;; The builtin styles currently are:
;;
;;  alert-growl     - Growl itself (surprised?)
;;  alert-message   - `message', with face showing severity, with a
;;                    `ding' for high/urgent
;;  alert-error     - `error'
;;  alert-mode-line - Persistent text in the mode-line, in different
;;                    faces according to severity, similar to how ERC's
;;                    track feature works
;;  alert-fringe    - Turning the fringe a different color, based on
;;                    severity
;;
;; It's easy to create a new style, such as playing a sound, sending an
;; e-mail, logging a message to syslog, queueing text to a log file, etc.:
;;
;;   (alert-define-style 'alert-append
;;     :on-alert (lambda (...) ...)
;;     :on-clear (lambda (...) ...)
;;     :persistent nil)
;;
;; To programmers: See the docstring for `alert' for more details

(eval-when-compile
  (require 'cl))

(defgroup alert nil
  "Notification system for Emacs similar to Growl"
  :group 'emacs)

(defcustom alert-severity-colors
  '((urgent   . "red")
    (high     . "orange")
    (moderate . "yellow")
    (normal   . "green")
    (low      . "blue")
    (trivial  . "purple"))
  "Colors associated by default with Alert severities."
  :type '(alist :key-type symbol :value-type color)
  :group 'alert)

(defcustom alert-minimum-idle-time 120
  "If idle this many seconds, show alerts that would otherwise be hidden."
  :type 'integer
  :group 'alert)

(defcustom alert-alert-styles nil
  ""
  ;; jww (2011-08-24): Make these sexps more specific
  :type '(repeat (list sexp sexp sexp sexp))
  :group 'alert)

(defsubst alert-alert-modes      (alert-style) (nth 0 alert-style))
(defsubst alert-alert-severities (alert-style) (nth 1 alert-style))
(defsubst alert-alert-statuses   (alert-style) (nth 2 alert-style))
(defsubst alert-alert-notifiers  (alert-style) (nth 3 alert-style))
(defsubst alert-alert-predicate  (alert-style) (nth 4 alert-style))

;;;###autoload
(defun alert-configure-alert (modes severities statuses notifiers
                                   &optional predicate)
  (add-to-list 'alert-alert-styles
               (list (cond ((eq t modes) t)
                           ((symbolp modes) (list modes))
                           (t modes))
                     (cond ((eq t severities) t)
                           ((symbolp severities) (list severities))
                           (t severities))
                     (cond ((eq t statuses) t)
                           ((symbolp statuses) (list statuses))
                           (t statuses))
                     (cond ((eq t notifiers) t)
                           ((symbolp notifiers) (list notifiers))
                           (t notifiers))
                     predicate)))

(defun alert-message-notify (severity &optional text title buffer data)
  (message text)
  (if (memq severity '(high urgency))
      (ding)))

(copy-face 'fringe 'alert-saved-fringe-face)

(defun alert-fringe-restore ()
  (copy-face 'alert-saved-fringe-face 'fringe))

(defun alert-fringe-notify (severity &optional text title buffer data)
  (set-face-background 'fringe (cdr (assq severity alert-severity-colors)))
  (with-current-buffer (or buffer (current-buffer))
    (add-hook 'post-command-hook 'alert-fringe-restore nil t)))

(defcustom alert-growl-command (executable-find "growlnotify")
  "The path to growlnotify"
  :type 'file
  :group 'alert)

(defcustom alert-growl-priorities
  '((urgent   . 2)
    (high     . 2)
    (moderate . 1)
    (normal   . 0)
    (low      . -1)
    (trivial  . -2))
  ""
  :type '(alist :key-type symbol :value-type integer)
  :group 'alert)

(defsubst alert-encode-string (str)
  (encode-coding-string str (keyboard-coding-system)))

(defun alert-growl-notify (severity &optional text title buffer data)
  (if alert-growl-command
      (call-process alert-growl-command nil nil nil
                    "-a" "Emacs" "-n" "Emacs"
                    "-t" (alert-encode-string title)
                    "-m" (alert-encode-string text)
                    "-p" (number-to-string
                          (cdr (assq severity alert-growl-priorities))))
    (alert-message-notify severity text title buffer data)))

(defun alert-buffer-status (&optional buffer)
  (with-current-buffer (or buffer (current-buffer))
    (let ((wind (get-buffer-window)))
      (if wind
          (if (eq wind (selected-window))
              (if (and (current-idle-time)
                       (> (float-time (current-idle-time))
                          alert-minimum-idle-time))
                  'idle
                'selected)
            'visible)
        'buried))))

;;;###autoload
(defun alert (severity &optional text title buffer data)
  "Notify the user that something has happened, ala Growl.

The interface for programmers is simple:

  (alert SYMBOL SEVERITY MESSAGE &optional TITLE BUFFER DATA)

SYMBOL is a symbol which identifies the message.  That, in
conjunction with the major mode, is used for looking up which
style(s) are used to notify the user.  SEVERITY is one of the
following, along with its typically associated color:

  `urgent'    (red)
  `high'      (orange)
  `moderate'  (yellow)
  `normal'    (green)
  `low'       (blue)
  `trivial'   (purple)

If no TITLE is given, it's assumed to be the buffer-name.  If
BUFFER is nil, it is taken to be the current buffer.  Knowing
which buffer an alert comes from allows the user the easily
navigate through all the buffers which had unviewed alerts.  This
is again similar to erc-track.  DATA is an opaque value which
modules can pass through to their own styles.  If a style chosen
by the user does not support it, it is ignored.

Furthermore, users can configure what happens if an alert occurs
in a buried buffer, a buffer that's visible in a window in any or
the current frame, or a buffer that's visible in the currently
selected window.  This is followed by a set of keybindings for
cycling through unvisited alerts, listing past alerts (with
unvisited ones in bold), and popping back to the frame/window
configuration the user was at before they started cycling."
  (ignore
   (destructuring-bind (current-major-mode current-buffer-status)
       (with-current-buffer (or buffer (current-buffer))
         (list major-mode (alert-buffer-status)))
     (dolist (alert-style alert-alert-styles)
       (if (and (let ((modes (alert-alert-modes alert-style)))
                  (or (eq t modes)
                      (memq current-major-mode modes)))
                (let ((severities (alert-alert-severities alert-style)))
                  (or (eq t severities)
                      (memq severity severities)))
                (let ((statuses (alert-alert-statuses alert-style)))
                  (or (eq t statuses)
                      (memq current-buffer-status statuses)))
                (let ((predicate (alert-alert-predicate alert-style)))
                  (or (eq t predicate)
                      (funcall predicate severity text title buffer data))))
           (mapc (lambda (func)
                   (funcall func severity text title buffer data))
                 (alert-alert-notifiers alert-style)))))))

(provide 'alert)

;;; alert.el ends here
