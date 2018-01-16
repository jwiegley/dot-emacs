;;; magithub-notification.el --- notification handling  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: lisp

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; View and interact with notifications

;;; Code:

(require 'magithub-issue-view)

(defvar magit-magithub-notification-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magithub-map)
    (define-key m [remap magit-visit-thing] #'magithub-notification-visit)
    (define-key m [remap magithub-browse-thing] #'magithub-notification-browse)
    (define-key m [remap magit-refresh] #'magithub-notification-refresh)
    m))

(defvar magit-magithub-notifications-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magithub-map)
    (define-key m [remap magit-refresh] #'magithub-notification-refresh)
    m))

(defun magithub-notifications (&optional include-read only-participating since before)
  "Get notifications for the currently-authenticated user.
If INCLUDE-READ is non-nil, read notifications are returned as
well.

If ONLY-PARTICIPATING is non-nil, only return notifications that
the user is directly participating in.

If SINCE/BEFORE are non-nil, they are time values.  Only
notifications received since/before this value will be returned.
See also Info node `(elisp)Time of Day'."
  (let (args)
    (when include-read
      (push '(:all "true") args))
    (when only-participating
      (push '(:participating "true") args))
    (when since
      (push `(:since ,(format-time-string "%FT%T%z" since)) args))
    (when before
      (push `(:before ,(format-time-string "%FT%T%z" before)) args))
    (magithub-cache :notification
      `(magithub-request
        (ghubp-unpaginate
         (ghubp-get-notifications ,@(apply #'append args)))))))

(defun magithub-notification-refresh ()
  (interactive)
  (magithub-cache-without-cache :notification
    (magit-refresh))
  (message "(magithub) notifcations refreshed"))

(defun magithub-notification-unread-p (notification)
  "Non-nil if NOTIFICATION has been read."
  (alist-get 'unread notification))

(defconst magithub-notification-reasons
  '(("assign" . "You were assigned to the Issue.")
    ("author" . "You created the thread.")
    ("comment" . "You commented on the thread.")
    ("invitation" . "You accepted an invitation to contribute to the repository.")
    ("manual" . "You subscribed to the thread (via an Issue or Pull Request).")
    ("mention" . "You were specifically @mentioned in the content.")
    ("state_change" . "You changed the thread state (for example, closing an Issue or merging a Pull Request).")
    ("subscribed" . "You're watching the repository.")
    ("team_mention" . "You were on a team that was mentioned."))
  "Human-readable description of possible notification reasons.
Stripped from the Github API Docs:

    URL `https://developer.github.com/v3/activity/notifications/#notification-reasons'.")

(defun magithub-notification-reason (notification &optional expanded)
  "Get the reason NOTIFICATION exists.
If EXPANDED is non-nil, use `magithub-notification-reasons' to
get a more verbose explanation."
  (let-alist notification
    (if expanded
        (cdr (assoc-string .reason magithub-notification-reasons
                           "(Unknown)"))
      .reason)))

(defalias 'magithub-notification-visit #'magithub-notification-browse)
(defun magithub-notification-browse (notification)
  "Visits the URL pointed to by NOTIFICATION."
  (interactive (list (magithub-thing-at-point 'notification)))
  (if notification
      (let-alist notification
        (cond
         ((or (string= .subject.type "Issue")
              (string= .subject.type "PullRequest"))
          (magithub-issue-view (magithub-request (ghubp-follow-get .subject.url))))
         (t (if-let ((url (or .subject.latest_comment_url .subject.url))
                     (html-url (alist-get 'html_url (magithub-request (ghubp-follow-get url)))))
                (browse-url html-url)
              (user-error "No target URL found")))))
    (user-error "No notification here")))

(defvar magithub-notification-details-hook
  '(magithub-notification-detail-insert-type
    magithub-notification-detail-insert-updated
    magithub-notification-detail-insert-expanded-reason)
  "Detail functions for notification-type sections.
These details appear under notifications as expandable content.

Each function takes the notification object as its only
argument.")

(defun magithub-notification-insert-section (notification)
  "Insert NOTIFICATION as a section into the buffer."
  (let-alist notification
    (magit-insert-section (magithub-notification notification (not .unread))
      (magit-insert-heading
        (format "%-12s %s"
                (propertize (magithub-notification-reason notification)
                            'face 'magithub-notification-reason
                            'help-echo (magithub-notification-reason notification t))
                (propertize (concat .subject.title "\n")
                            'face (if .unread 'highlight))))
      (run-hook-with-args 'magithub-notification-details-hook notification))))

(defun magithub-notification-detail-insert-type (notification)
  "Insert NOTIFICATION's type."
  (let-alist notification
    (insert (format "%-12s %s\n" "Type:"
                    (propertize .subject.type 'face 'magit-dimmed)))))

(defun magithub-notification-detail-insert-updated (notification)
  "Insert a timestamp of when NOTIFICATION was last updated."
  (let-alist notification
    (insert (format "%-12s %s\n" "Updated:"
                    (propertize .updated_at 'face 'magit-dimmed)))))

(defun magithub-notification-detail-insert-expanded-reason (notification)
  "Insert NOTIFICATION's expanded reason.
See also `magithub-notification-reasons'."
  (insert (format "%-12s %s\n" "Reason:"
                  (propertize (or (magithub-notification-reason notification t)
                                  "(no description available)")
                              'face 'magit-dimmed))))

(provide 'magithub-notification)
;;; magithub-notification.el ends here
