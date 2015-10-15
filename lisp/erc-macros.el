(eval-when-compile
  (require 'cl)

  (defvar erc-fools))

(defun erc-cmd-FOOL (term &rest ignore)
  (add-to-list 'erc-fools term))

(defun erc-cmd-UNFOOL (term &rest ignore)
  (setq erc-fools (delete term erc-fools)))

(defun erc-cmd-OPME ()
  "Request chanserv to op me."
  (erc-message "PRIVMSG"
               (format "chanserv op %s %s"
                       (erc-default-target)
                       (erc-current-nick)) nil))

(defun erc-cmd-DEOPME ()
  "Deop myself from current channel."
  (erc-cmd-DEOP (format "%s" (erc-current-nick))))

(defun erc-cmd-BAN (nick &optional redirect whole-ip)
  (let* ((chan (erc-default-target))
         (who (erc-get-server-user nick))
         (host (erc-server-user-host who))
         (user (erc-server-user-login who)))
    (erc-send-command
     (format "MODE %s +b *!%s@%s%s"
             chan (if whole-ip "*" user) host (or redirect "")))))

(defun erc-cmd-KICKBAN (nick &rest reason)
  (setq reason (mapconcat #'identity reason " "))
  (and (string= reason "")
       (setq reason nil))
  (erc-cmd-OPME)
  (sleep-for 0 250)
  (erc-cmd-BAN nick)
  (erc-send-command (format "KICK %s %s %s"
                            (erc-default-target)
                            nick
                            (or reason
                                "Kicked (kickban)")))
  (sleep-for 0 250)
  (erc-cmd-DEOPME))

(defun erc-cmd-QUIET (nick)
  (erc-cmd-OPME)
  (sleep-for 0 250)
  (erc-send-command (format "QUIET %s %s"
                            (erc-default-target)
                            nick))
  (sleep-for 0 250)
  (erc-cmd-DEOPME))

(defun erc-cmd-KICKBANIP (nick &rest reason)
  (setq reason (mapconcat #'identity reason " "))
  (and (string= reason "")
       (setq reason nil))
  (erc-cmd-OPME)
  (sleep-for 0 250)
  (erc-cmd-BAN nick nil t)
  (erc-send-command (format "KICK %s %s %s"
                            (erc-default-target)
                            nick
                            (or reason
                                "Kicked (kickbanip)")))
  (sleep-for 0 250)
  (erc-cmd-DEOPME))

(defun erc-cmd-KICKTROLL (nick &rest reason)
  (setq reason (mapconcat #'identity reason " "))
  (and (string= reason "")
       (setq reason nil))
  (erc-cmd-OPME)
  (sleep-for 0 250)
  (erc-cmd-BAN nick "$#haskell-ops")
  (erc-send-command (format "KICK %s %s %s"
                            (erc-default-target)
                            nick
                            (or reason
                                "Kicked (kicktroll)")))
  (sleep-for 0 250)
  (erc-cmd-DEOPME))

;; this is essentially a refactored `erc-cmd-KICK'
(defun erc-cmd-REMOVE (target &optional reason-or-nick &rest reasonwords)
  "Remove a user from the default or specified channel.
    LINE has the format: \"#CHANNEL NICK REASON\" or \"NICK REASON\"."
  (let* ((target-channel-p (erc-channel-p target))
         (channel (if target-channel-p target (erc-default-target)))
         (nick (if target-channel-p reason-or-nick target))
         (reason
          (mapconcat 'identity
                     (or (if target-channel-p reasonwords
                           (and reason-or-nick
                                (cons reason-or-nick reasonwords)))
                         `("Requested by" ,(erc-current-nick)))
                     " "))
         (server-command (format "REMOVE %s %s :%s" channel nick reason)))
    (if (not channel)
        (erc-display-message nil 'error (current-buffer)
                             'no-default-channel)
      (erc-log (format "cmd: REMOVE: %s/%s: %s" channel nick reason))
      (erc-server-send server-command))))

(defun erc-cmd-UNTRACK (&optional target)
  "Add TARGET to the list of target to be tracked."
  (if target
      (erc-with-server-buffer
       (let ((untracked
              (car (erc-member-ignore-case target erc-track-exclude))))
         (if untracked
             (erc-display-line
              (erc-make-notice
               (format "%s is not currently tracked!" target))
              'active)
           (add-to-list 'erc-track-exclude target)
           (erc-display-line
            (erc-make-notice (format "Now not tracking %s" target))
            'active))))

    (if (null erc-track-exclude)
        (erc-display-line
         (erc-make-notice "Untracked targets list is empty") 'active)

      (erc-display-line (erc-make-notice "Untracked targets list:") 'active)
      (mapc #'(lambda (item)
                (erc-display-line (erc-make-notice item) 'active))
            (erc-with-server-buffer erc-track-exclude))))
  t)

(defun erc-cmd-TRACK (target)
  "Remove TARGET of the list of targets which they should not be tracked.
   If no TARGET argument is specified, list contents of `erc-track-exclude'."
  (when target
    (erc-with-server-buffer
     (let ((tracked
            (not (car (erc-member-ignore-case target erc-track-exclude)))))
       (if tracked
           (erc-display-line
            (erc-make-notice (format "%s is currently tracked!" target))
            'active)
         (setq erc-track-exclude (remove target erc-track-exclude))
         (erc-display-line
          (erc-make-notice (format "Now tracking %s" target))
          'active)))))
  t)

(defun erc-cmd-HOWMANY (&rest ignore)
  "Display how many users (and ops) the current channel has."
  (erc-display-message
   nil 'notice (current-buffer)
   (let ((hash-table (with-current-buffer
                         (erc-server-buffer)
                       erc-server-users))
         (users 0)
         (ops 0))
     (maphash (lambda (k v)
                (when (member (current-buffer)
                              (erc-server-user-buffers v))
                  (incf users))
                (when (erc-channel-user-op-p k)
                  (incf ops)))
              hash-table)
     (format
      "There are %s users (%s ops) on the current channel"
      users ops))))

(provide 'erc-macros)
