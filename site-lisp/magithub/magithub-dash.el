;;; magithub-dash.el --- magithub dashboard          -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: hypermedia

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

;; Magithub-Dash is a dashboard for your Github activity.

;;; Code:

(require 'magit)
(require 'magithub-core)
(require 'magithub-notification)
(require 'magithub-issue)

(declare-function magithub-dispatch-popup "magithub.el")

(defcustom magithub-dashboard-show-unread-notifications nil
  "Show unread notifications in the dashboard."
  :type 'boolean
  :group 'magithub)

(magit-define-popup magithub-dashboard-popup
  "Popup console for the dashboard."
  'magithub-commands
  :actions '("Notifications"
             (?r "Toggle showing unread notifications"
                 magithub-dashboard-show-unread-notifications-toggle)))

(defun magithub-dashboard-show-unread-notifications-toggle ()
  (interactive)
  (setq magithub-dashboard-show-unread-notifications
        (not magithub-dashboard-show-unread-notifications))
  (magit-refresh-buffer))

;;;###autoload
(defun magithub-dashboard ()
  "View your Github dashboard."
  (interactive)
  (let ((magit-generate-buffer-name-function
         (lambda (&rest _) "*magithub-dash*")))
    (magit-mode-setup #'magithub-dash-mode)))

(defvar magithub-dash-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magit-mode-map)
    (define-key m (kbd "5") #'magit-section-show-level-5)
    (define-key m (kbd "M-5") #'magit-section-show-level-5-all)
    (define-key m (kbd ";") #'magithub-dashboard-popup)
    (define-key m (kbd "H") #'magithub-dispatch-popup)
    m)
  "Keymap for `magihtub-dash-mode'.")

(define-derived-mode magithub-dash-mode
  magit-mode "Magithub-Dash"
  "Major mode for your Github dashboard."
  (use-local-map magithub-dash-map))

(defun magithub-dash-refresh-buffer (&rest _args)
  "Refresh the dashboard.
Runs `magithub-dash-sections-hook'."
  (interactive)
  (magit-insert-section (magithub-dash-buf)
    (run-hooks 'magithub-dash-sections-hook)))

(defvar magithub-dash-sections-hook
  '(magithub-dash-insert-headers
    magithub-dash-insert-notifications
    magithub-dash-insert-issues)
  "Sections inserted by `magithub-dashboard'.")

(defvar magithub-dash-headers-hook
  '(magithub-dash-insert-user-name-header
    magithub-dash-insert-ratelimit-header
    magithub-maybe-report-offline-mode)
  "Headers inserted by `magithub-dash-insert-headers'.")

(defun magithub-dash-insert-headers ()
  "Insert dashboard headers.
See also `magithub-dash-headers-hook'."
  (magit-insert-headers magithub-dash-headers-hook))

(defun magithub-dash-insert-user-name-header (&optional user)
  "Inserts a header for USER's name and login."
  (setq user (or user (magithub-user-me)))
  (let-alist user
    (when .login
      (let ((login (propertize .login 'face 'magithub-user)))
        (magit-insert-section (magithub-user user)
          (insert (format "%-10s" "User:")
                  (if .name
                      (format "%s (%s)" .name login)
                    login)
                  "\n"))))))

(defun magithub-dash-insert-ratelimit-header ()
  "If API requests are being rate-limited, insert relevant information."
  (magithub-request
   (when-let ((ratelimit (ghubp-ratelimit)))
     (when (time-less-p (alist-get 'reset ratelimit) (current-time))
       (ghub-get "/rate_limit" nil :auth 'magithub)))
   (let-alist (ghubp-ratelimit)
     (when .limit
       (magit-insert-section (magithub-ratelimit)
         (let* ((seconds-until-reset (time-to-seconds
                                      (time-subtract .reset
                                                     (current-time))))
                (ratio (/ (float .remaining) .limit)))
           (insert
            (format "%-10s%s - %d/%d requests; %s until reset\n" "Requests:"
                    (cond
                     ((< 0.50 ratio) (propertize "OK" 'face 'success))
                     ((< 0.25 ratio) (propertize "Running low..." 'face 'warning))
                     (t (propertize "Danger!" 'face 'error)))
                    .remaining
                    .limit
                    (magithub-cache--time-out seconds-until-reset)))))))))

(defun magithub-dash-insert-notifications (&optional notifications)
  "Insert NOTIFICATIONS into the buffer bucketed by repository."
  (setq notifications (or notifications (magithub-notifications
                                         magithub-dashboard-show-unread-notifications)))
  (if notifications
      (let* ((bucketed (magithub-core-bucket notifications (apply-partially #'alist-get 'repository)))
             (unread (-filter #'magithub-notification-unread-p notifications))
             (hide (null unread)))
        (magit-insert-section (magithub-notifications notifications hide)
          (magit-insert-heading
            (if magithub-dashboard-show-unread-notifications
                (format "%s (%d unread of %d)"
                        (propertize "Notifications" 'face 'magit-section-heading)
                        (length unread)
                        (length notifications))
              (format "%s (%d)"
                      (propertize "Notifications" 'face 'magit-section-heading)
                      (length notifications))))
          (magithub-for-each-bucket bucketed repo repo-notifications
            (setq hide (null (-filter #'magithub-notification-unread-p repo-notifications)))
            (magit-insert-section (magithub-repo repo hide)
              (magit-insert-heading
                (concat (propertize (magithub-repo-name repo) 'face 'magithub-repo)
                        (propertize "..." 'face 'magit-dimmed)))
              (mapc #'magithub-notification-insert-section repo-notifications)
              (insert "\n")))
          (insert "\n")))
    (magit-insert-section (magithub-notifications)
      (magit-insert-heading "Notifications")
      (insert (propertize (if magithub-dashboard-show-unread-notifications
                              "No notifications"
                            "No unread notifications")
                          'face 'magit-dimmed)
              "\n\n"))))

(defun magithub-dash-insert-issues (&optional issues title)
  "Insert ISSUES bucketed by their source repository.

If ISSUES is not defined, all issues assigned to the current user
will be used."
  (magithub-request
   (setq issues (or issues (magithub-cache :issues `(magithub-request
                                                     (ghubp-get-issues))))
         title (or title "Issues Assigned to Me"))
   (when-let ((user-repo-issue-buckets
               ;; bucket by user then by repo
               (magithub-core-bucket-multi issues
                 #'magithub-issue-repo
                 (lambda (repo) (alist-get 'owner repo)))))
     (magit-insert-section (magithub-users-repo-issue-buckets)
       (magit-insert-heading (format "%s (%d)"
                                     (propertize title 'face 'magit-section-heading)
                                     (length issues)))
       (magithub-for-each-bucket user-repo-issue-buckets user repo-issue-buckets
         (magit-insert-section (magithub-user-repo-issues)
           (magit-insert-heading
             (propertize (alist-get 'login user) 'face 'magithub-user)
             (propertize "/..."                  'face 'magit-dimmed))
           (magithub-for-each-bucket repo-issue-buckets repo repo-issues
             (magit-insert-section (magithub-repo-issues repo)
               (magit-insert-heading
                 (format "%s:" (propertize (alist-get 'name repo) 'face 'magithub-repo)))
               (magithub-issue-insert-sections repo-issues)
               (insert "\n")))))
       (insert "\n")))))

(provide 'magithub-dash)
;;; magithub-dash.el ends here
