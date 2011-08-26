
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

(defcustom alert-severity-faces
  '((urgent   . alert-urgent-face)
    (high     . alert-high-face)
    (moderate . alert-moderate-face)
    (normal   . alert-normal-face)
    (low      . alert-low-face)
    (trivial  . alert-trivial-face))
  "Colors associated by default with Alert severities."
  :type '(alist :key-type symbol :value-type color)
  :group 'alert)

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

(defcustom alert-reveal-idle-time 5
  "If idle this many seconds, show alerts that would otherwise be hidden."
  :type 'integer
  :group 'alert)

(defcustom alert-persist-idle-time 900
  "If idle this many seconds, alerts become persistent."
  :type 'integer
  :group 'alert)

(defcustom alert-fade-time 5
  "If the user is not idle, alerts disappear after this many seconds."
  :type 'integer
  :group 'alert)

(defcustom alert-hide-all-notifications nil
  "If non-nil, no alerts are ever shown to the user."
  :type 'boolean
  :group 'alert)

(defcustom alert-log-messages t
  "If non-nil, log alerts to the *Alerts* buffer."
  :type 'boolean
  :group 'alert)

(defvar alert-styles nil)

(defun alert-styles-radio-type (widget-name)
  (append
   (list widget-name :tag "Style")
   (mapcar (lambda (style)
             (list 'const
                   :tag (or (plist-get (cdr style) :title)
                            (symbol-name (car style)))
                   (car style)))
           (setq alert-styles
                 (sort alert-styles
                       (lambda (l r)
                         (string< (symbol-name (car l))
                                  (symbol-name (car r)))))))))

(defcustom alert-default-style 'message
  "The style to use if none match the current configuration.
If a configured rule does match an alert, this style is not used.
It is strictly a fallback."
  :type (alert-styles-radio-type 'radio)
  :group 'alert)

(defun alert-configuration-type ()
  (list 'repeat
        (list
         'list :tag "Select style if alert matches selector"
         '(repeat
           :tag "Selector"
           (choice
            (cons :tag "Severity"
                  (const :format "" :severity)
                  (set (const :tag "Urgent" urgent)
                       (const :tag "High" high)
                       (const :tag "Moderate" moderate)
                       (const :tag "Normal" normal)
                       (const :tag "Low" low)
                       (const :tag "Trivial" trivial)))
            (cons :tag "User Status"
                  (const :format "" :status)
                  (set (const :tag "Buffer not visible" buried)
                       (const :tag "Buffer visible" visible)
                       (const :tag "Buffer selected" selected)
                       (const :tag "Buffer selected, user idle" idle)))
            (cons :tag "Major Mode"
                  (const :format "" :mode)
                  regexp)
            (cons :tag "Category"
                  (const :format "" :category)
                  regexp)
            (cons :tag "Title"
                  (const :format "" :title)
                  regexp)
            (cons :tag "Message"
                  (const :format "" :message)
                  regexp)
            (cons :tag "Predicate"
                  (const :format "" :predicate)
                  function)))
         (alert-styles-radio-type 'choice)
         '(set :tag "Options"
               (cons :tag "Make alert display persistent"
                     (const :format "" :persistent)
                     (choice :value t (const :tag "Yes" t)
                             (function :tag "Predicate")))
               (cons :tag "Continue to next rule"
                     (const :format "" :continue)
                     (choice :value t (const :tag "Yes" t)
                             (function :tag "Predicate")))
               ;;(list :tag "Change Severity"
               ;;      (radio :tag "From"
               ;;             (const :tag "Urgent" urgent)
               ;;             (const :tag "High" high)
               ;;             (const :tag "Moderate" moderate)
               ;;             (const :tag "Normal" normal)
               ;;             (const :tag "Low" low)
               ;;             (const :tag "Trivial" trivial))
               ;;      (radio :tag "To"
               ;;             (const :tag "Urgent" urgent)
               ;;             (const :tag "High" high)
               ;;             (const :tag "Moderate" moderate)
               ;;             (const :tag "Normal" normal)
               ;;             (const :tag "Low" low)
               ;;             (const :tag "Trivial" trivial)))
               ))))

(defcustom alert-user-configuration nil
  "Configure how and when alerts are displayed.
The default is to use the Emacs `message' function, which will
also `ding' the user if the :severity of the message is either
`high' or `urgent'."
  :type (alert-configuration-type)
  :group 'alert)

(defvar alert-internal-configuration nil
  "Rules added by `alert-add-rule'.
For customization, use the variable `alert-user-configuration'.")

(defface alert-urgent-face
  '((t (:foreground "Red" :bold t)))
  "Urgent alert face."
  :group 'alert)

(defface alert-high-face
  '((t (:foreground "Dark Orange" :bold t)))
  "High alert face."
  :group 'alert)

(defface alert-moderate-face
  '((t (:foreground "Gold" :bold t)))
  "Moderate alert face."
  :group 'alert)

(defface alert-normal-face
  '((t))
  "Normal alert face."
  :group 'alert)

(defface alert-low-face
  '((t (:foreground "Dark Blue")))
  "Low alert face."
  :group 'alert)

(defface alert-trivial-face
  '((t (:foreground "Dark Purple")))
  "Trivial alert face."
  :group 'alert)

(defun alert-define-style (name &rest plist)
  (add-to-list 'alert-styles (cons name plist))
  (put 'alert-user-configuration 'custom-type (alert-configuration-type))
  (put 'alert-define-style 'custom-type (alert-styles-radio-type 'radio)))

(alert-define-style 'ignore :title "Ignore Alert"
                    :notifier #'ignore
                    :remover #'ignore)

(defun* alert-add-rule (&key severity status mode category title
                             message predicate (style alert-default-style)
                             persistent continue append)
  (let ((rule (list (list t) style (list t))))
    (if severity
        (nconc (nth 0 rule)
               (list (cons :severity
                           (if (listp severity)
                               severity
                             (list severity))))))
    (if status
        (nconc (nth 0 rule)
               (list (cons :status
                           (if (listp status)
                               status
                             (list status))))))
    (if mode
        (nconc (nth 0 rule)
               (list (cons :mode
                           (if (stringp mode)
                               mode
                             (concat "\\`" (symbol-name mode)
                                     "\\'"))))))
    (if category
        (nconc (nth 0 rule) (list (cons :category category))))
    (if title
        (nconc (nth 0 rule) (list (cons :title title))))
    (if message
        (nconc (nth 0 rule) (list (cons :message message))))
    (if predicate
        (nconc (nth 0 rule) (list (cons :predicate predicate))))
    (setcar rule (cdr (nth 0 rule)))

    (if persistent
        (nconc (nth 2 rule) (list (cons :persistent persistent))))
    (if continue
        (nconc (nth 2 rule) (list (cons :continue continue))))
    (setcdr (cdr rule) (list (cdr (nth 2 rule))))

    (if (null alert-internal-configuration)
        (setq alert-internal-configuration (list rule))
      (if append
          (nconc alert-internal-configuration (list rule))
        (setq alert-internal-configuration
              (cons rule alert-internal-configuration))))

    rule))

(alert-define-style 'ignore :title "Don't display alert")

(defun alert-colorize-message (message severity)
  (set-text-properties 0 (length message)
                       (list 'face (cdr (assq severity
                                              alert-severity-faces)))
                       message)
  message)

(defun alert-log-notify (info)
  (with-current-buffer
      (get-buffer-create "*Alerts*")
    (goto-char (point-max))
    (insert (format-time-string "%H:%M %p - ")
            (alert-colorize-message (plist-get info :message)
                                    (plist-get info :severity))
            ?\n)))

(defun alert-log-clear (info)
  (with-current-buffer
      (get-buffer-create "*Alerts*")
    (goto-char (point-max))
    (insert (format-time-string "%H:%M %p - ")
            "Clear: " (plist-get info :message)
            ?\n)))

(alert-define-style 'log :title "Log to *Alerts* buffer"
                    :notifier #'alert-log-notify
                    ;;:remover #'alert-log-clear
                    )

(defun alert-message-notify (info)
  (message (alert-colorize-message (plist-get info :message)
                                   (plist-get info :severity)))
  ;;(if (memq (plist-get info :severity) '(high urgency))
  ;;    (ding))
  )

(defun alert-message-remove (info)
  (message ""))

(alert-define-style 'message :title "Display message in minibuffer"
                    :notifier #'alert-message-notify
                    :remover #'alert-message-remove)

(copy-face 'fringe 'alert-saved-fringe-face)

(defun alert-fringe-notify (info)
  (set-face-background 'fringe (cdr (assq (plist-get info :severity)
                                          alert-severity-colors))))

(defun alert-fringe-restore (info)
  (copy-face 'alert-saved-fringe-face 'fringe))

(alert-define-style 'fringe :title "Change the fringe color"
                    :notifier #'alert-fringe-notify
                    :remover #'alert-fringe-restore)

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

(defun alert-growl-notify (info)
  (if alert-growl-command
      (let ((args
             (list "--appIcon"  "Emacs"
                   "--name"     "Emacs"
                   "--title"    (alert-encode-string (plist-get info :title))
                   "--message"  (alert-encode-string (plist-get info :message))
                   "--priority" (number-to-string
                                 (cdr (assq (plist-get info :severity)
                                            alert-growl-priorities))))))
        (if (plist-get info :persistent)
            (nconc args (list "--sticky")))
        (apply #'call-process alert-growl-command nil nil nil args))
    (alert-message-notify info)))

(alert-define-style 'growl :title "Notify using Growl"
                    :notifier #'alert-growl-notify)

(defun alert-frame-notify (info)
  (let ((buf (plist-get info :buffer)))
    (if (eq (alert-buffer-status buf) 'buried)
        (let ((current-frame (selected-frame)))
          (with-selected-frame
              (make-frame '((width                . 80)
                            (height               . 20)
                            (top                  . -1)
                            (left                 . 0)
                            (left-fringe          . 0)
                            (right-fringe         . 0)
                            (tool-bar-lines       . nil)
                            (menu-bar-lines       . nil)
                            (vertical-scroll-bars . nil)
                            (unsplittable         . t)
                            (has-modeline-p       . nil)
                            (minibuffer           . nil)))
            (switch-to-buffer buf)
            ;;(set (make-local-variable 'mode-line-format) nil)
            (nconc info (list :frame (selected-frame))))
          (select-frame current-frame)))))

(defun alert-frame-remove (info)
  (unless (eq this-command 'handle-switch-frame)
    (delete-frame (plist-get info :frame) t)))

;; jww (2011-08-25): Not quite working yet
;;(alert-define-style 'frame :title "Popup buffer in a frame"
;;                    :notifier #'alert-frame-notify
;;                    :remover #'alert-frame-remove)

(defun alert-buffer-status (&optional buffer)
  (with-current-buffer (or buffer (current-buffer))
    (let ((wind (get-buffer-window)))
      (if wind
          (if (eq wind (selected-window))
              (if (and (current-idle-time)
                       (> (float-time (current-idle-time))
                          alert-reveal-idle-time))
                  'idle
                'selected)
            'visible)
        'buried))))

(defvar alert-active-alerts nil)

(defun alert-remove-when-active (remover info)
  (let ((idle-time (and (current-idle-time)
                        (float-time (current-idle-time)))))
    (cond
     ((and idle-time (> idle-time alert-persist-idle-time)))
     ((and idle-time (> idle-time alert-reveal-idle-time))
      (run-with-timer alert-fade-time nil
                      #'alert-remove-when-active remover info))
     (t
      (funcall remover info)))))

(defun alert-remove-on-command ()
  (let (to-delete)
    (dolist (alert alert-active-alerts)
      (when (eq (current-buffer) (nth 0 alert))
        (push alert to-delete)
        (if (nth 2 alert)
            (funcall (nth 2 alert) (nth 1 alert)))))
    (dolist (alert to-delete)
      (setq alert-active-alerts (delq alert alert-active-alerts)))))

;;;###autoload
(defun* alert (message &key (severity 'normal) title category
                       buffer mode data style persistent)
  "Alert the user that something has happened.
MESSAGE is what the user will see.  You may also use keyword
arguments to specify some additional details.  Here is a full
example:

  (alert \"This is a message\"
         :title \"Title\"         ;; optional title
         :category 'example       ;; a symbol to identify the message
         :mode 'text-mode         ;; normally determined automatically
         :buffer (current-buffer) ;; this is the default
         :data nil                ;; unused by alert.el itself
         :persistent nil          ;; force the alert to be persistent
                                  ;; it is best not to use this
         :style 'fringe           ;; force a given style to be used
                                  ;; this is only for debugging!
         :severity 'high)         ;; the default severity is `normal'

If no :title is given, it's assumed to be the buffer-name.  If
:buffer is nil, it is taken to be the current buffer.  Knowing
which buffer an alert comes from allows the user the easily
navigate through buffers which have unviewed alerts.  :data is an
opaque value which modules can pass through to their own styles
if they wish."
  (ignore
   (destructuring-bind
       (alert-buffer current-major-mode current-buffer-status
                     current-buffer-name)
       (with-current-buffer (or buffer (current-buffer))
         (list (current-buffer)
               (or mode major-mode)
               (alert-buffer-status)
               (buffer-name)))

     (let ((base-info (list :message message
                            :title (or title current-buffer-name)
                            :severity severity
                            :category category
                            :buffer alert-buffer
                            :mode current-major-mode
                            :data data))
           matched)

       (if alert-log-messages
           (alert-log-notify base-info))

       (catch 'finish
         (dolist (config (append alert-user-configuration
                                 alert-internal-configuration))
           (let* ((style-def (cdr (assq (or style (nth 1 config))
                                        alert-styles)))
                  (options (nth 2 config))
                  (persist-p (or persistent
                                 (cdr (assq :persistent options))))
                  (persist (if (functionp persist-p)
                               (funcall persist-p base-info)
                             persist-p))
                  (continue (cdr (assq :continue options)))
                  (info (if (not (memq :persistent base-info))
                            (append base-info (list :persistent persist))
                          base-info)))
             (when
                 (or style              ; using :style always "matches"
                     (not
                      (memq
                       nil
                       (mapcar
                        (lambda (condition)
                          (case (car condition)
                            (:severity
                             (memq severity (cdr condition)))
                            (:status
                             (memq current-buffer-status (cdr condition)))
                            (:mode
                             (string-match (cdr condition)
                                           (symbol-name current-major-mode)))
                            (:category
                             (and category
                                  (string-match (cdr condition)
                                                (if (stringp category)
                                                    category
                                                  (symbol-name category)))))
                            (:title
                             (and title
                                  (string-match (cdr condition) title)))
                            (:message
                             (string-match (cdr condition) message))
                            (:predicate
                             (funcall (cdr condition) info))))
                        (nth 0 config)))))

               (let ((notifier (plist-get style-def :notifier)))
                 (if notifier
                     (funcall notifier info)))
               (setq matched t)

               (let ((remover (plist-get style-def :remover)))
                 (add-to-list 'alert-active-alerts
                              (list alert-buffer info remover))
                 (with-current-buffer alert-buffer
                   (add-hook 'post-command-hook
                             'alert-remove-on-command nil t))
                 (if (and remover (not persist))
                     (run-with-timer alert-fade-time nil
                                     #'alert-remove-when-active
                                     remover info))
                 (if (or style
                         (not (if (functionp continue)
                                  (funcall continue info)
                                continue)))
                     (throw 'finish t)))))))

       (if (and alert-default-style
                (not matched))
           (let ((notifier
                  (plist-get (cdr (assq alert-default-style
                                        alert-styles))
                             :notifier)))
             (if notifier
                 (funcall notifier info))))))))

;;(alert "Hello" :severity 'moderate :buffer (get-buffer "*scratch*")
;;       :style 'fringe)

(provide 'alert)

;;; alert.el ends here

