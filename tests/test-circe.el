;; -*-lexical-binding: t-*-

(require 'circe)

(describe "Circe chat mode"
  (describe "creation function"
    (it "should have circe-server-buffer set in the mode hook"
      (let* ((csb-value nil)
             (circe-server-killed-confirmation nil)
             (circe-chat-mode-hook (list
                                    (lambda ()
                                      (setq csb-value circe-server-buffer))))
             buf)
        (with-temp-buffer
          (circe-server-mode)
          (spy-on 'irc-isupport--case-fold :and-return-value "foo")

          (setq buf (circe-server-create-chat-buffer "foo" 'circe-chat-mode))
          (kill-buffer buf)

          (expect csb-value :to-equal (current-buffer)))))))

(describe "The `circe-version' command"
  (it "should display the current version"
    (spy-on 'message)
    (spy-on 'circe--version :and-return-value "23.5")

    (call-interactively 'circe-version)

    (expect 'message
            :to-have-been-called-with "Circe %s" "23.5")))

(describe "The `circe-duration-string' function"
  (it "should handle very short amounts of time"
    (expect (circe-duration-string 0)
            :to-equal "a moment"))

  (it "should support second granularity"
    (expect (circe-duration-string 1)
            :to-equal "1 second")
    (expect (circe-duration-string 2)
            :to-equal "2 seconds"))

  (it "should support minute granularity"
    (expect (circe-duration-string 60)
            :to-equal "1 minute")
    (expect (circe-duration-string 61)
            :to-equal "1 minute 1 second")
    (expect (circe-duration-string 62)
            :to-equal "1 minute 2 seconds")
    (expect (circe-duration-string 122)
            :to-equal "2 minutes 2 seconds"))

  (it "should support monthly granularity"
    (expect (circe-duration-string (+ (* 24 60 60 30)
                                      120))
            :to-equal "1 month 2 minutes")))

(describe "Circe's completion facility"
  (let (proc channel-buffer server-buffer)
    (before-each
      (setq server-buffer (generate-new-buffer "*Test Server*"))
      (set-buffer server-buffer)
      (circe-server-mode)
      (setq proc (start-process "test" nil "cat")
            circe-server-process proc)
      (setq circe-server-killed-confirmation nil)
      (setq channel-buffer (circe-server-create-chat-buffer
                            "test" 'circe-channel-mode))
      (set-buffer channel-buffer)
      (setq circe-channel-killed-confirmation nil)
      (spy-on 'circe-nick :and-return-value "mynick")
      (spy-on 'circe-channel-nicks :and-return-value '("testnick"))
      (spy-on 'irc-connection-channel))

    (after-each
      (delete-process proc)
      (kill-buffer channel-buffer)
      (kill-buffer server-buffer))

    (it "should complete nicks with colon at the beginning of the input"
      (insert "TESTNICK")
      (completion-at-point)
      (expect (buffer-substring lui-input-marker (point-max))
              :to-equal "testnick: "))

    (it "should complete nicks without colon later in the input"
      (insert "some stuff TESTNICK")
      (completion-at-point)
      (expect (buffer-substring lui-input-marker (point-max))
              :to-equal "some stuff testnick "))))

(describe "Display of"
  (let ((current-time 1434995549))
    (before-each
      (spy-on 'circe-display)
      (spy-on 'float-time :and-return-value (+ current-time 5))
      (set-buffer (get-buffer-create "*Test*"))
      (spy-on 'circe-server-last-active-buffer
              :and-return-value (current-buffer)))

    (after-each
      (kill-buffer (current-buffer)))

    (describe "RPL_WHOISREPLY"
      (it "should show idle time"
        (circe-display-317 "sender" nil "317" "target" "nick"
                           "23" "seconds idle")

        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-server-whois-idle
                :whois-nick "nick"
                :idle-seconds 23
                :idle-duration "23 seconds"))

      (it "should show idle time and signon time"
        (circe-display-317 "sender" nil "317" "target" "nick"
                           "23" (format "%s" current-time)
                           "seconds idle, signon time")

        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-server-whois-idle-with-signon
                :whois-nick "nick"
                :idle-seconds 23
                :idle-duration "23 seconds"
                :signon-time current-time
                :signon-date (current-time-string
                              (seconds-to-time current-time))
                :signon-ago "5 seconds")))

    (describe "RPL_TOPICWHOTIME"
      (it "should show current topic time"
        (spy-on 'circe-server-get-chat-buffer
                :and-return-value (current-buffer))

        (circe-display-333 "sender" nil "333" "target"
                           "#channel" "setter!user@host"
                           (format "%s" current-time))

        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-server-topic-time
                :nick "target"
                :channel "#channel"
                :setter "setter"
                :setter-userhost "user@host"
                :topic-time current-time
                :topic-date (current-time-string
                             (seconds-to-time current-time))
                :topic-ago "5 seconds"))

      (it "should show current topic time in a different channel"
        (spy-on 'circe-server-get-chat-buffer
                :and-return-value nil)
        (spy-on 'circe-server-last-active-buffer
                :and-return-value (current-buffer))

        (circe-display-333 "sender" nil "333" "target"
                           "#channel" "setter!user@host"
                           (format "%s" current-time))

        (expect 'circe-server-last-active-buffer
                :to-have-been-called)

        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-server-topic-time-for-channel
                :nick "target"
                :channel "#channel"
                :setter "setter"
                :setter-userhost "user@host"
                :topic-time current-time
                :topic-date (current-time-string
                             (seconds-to-time current-time))
                :topic-ago "5 seconds")))

    (describe "CTCP ACTION"
      (it "should show a query in a query buffer"
        (spy-on 'circe-query-auto-query-buffer
                :and-return-value (current-buffer))
        (spy-on 'circe-server-my-nick-p :and-return-value t)

        (circe-display-ctcp-action "nick" "user@host" "irc.ctcp.ACTION"
                                   "my-nick" "the text")

        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-action
                :nick "nick" :userhost "user@host" :body "the text"))

      (it "should show a query in the current buffer"
        (spy-on 'circe-server-my-nick-p :and-return-value t)
        (spy-on 'circe-query-auto-query-buffer
                :and-return-value nil)
        (spy-on 'circe-server-last-active-buffer
                :and-return-value (current-buffer))

        (circe-display-ctcp-action "nick" "user@host" "irc.ctcp.ACTION"
                                   "my-nick" "the text")

        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-message-action
                :nick "nick" :userhost "user@host" :body "the text"))

      (it "should show a channel action"
        (spy-on 'circe-server-my-nick-p :and-return-value nil)
        (spy-on 'circe-server-get-or-create-chat-buffer
                :and-return-value (current-buffer))
        (spy-on 'circe-lurker-display-active)

        (circe-display-ctcp-action "nick" "user@host" "irc.ctcp.ACTION"
                                   "#channel" "the text")

        (expect 'circe-lurker-display-active :to-have-been-called)
        (expect 'circe-display
                :to-have-been-called-with
                'circe-format-action
                :nick "nick" :userhost "user@host" :body "the text")))
    
    (describe "CTCP PING"
      (it "should display unknown seconds when passed nil for text"
	(spy-on 'circe-server-my-nick-p :and-return-value nil) 
	(spy-on 'circe-server-get-or-create-chat-buffer
		:and-return-value (current-buffer))
	(spy-on 'circe-display)
	
	(circe-display-ctcp-ping "nick" "user@host" "irc.ctcp.PING"
				 "target" nil)

	(expect 'circe-display
		:to-have-been-called-with
		'circe-format-server-ctcp-ping
		:nick "nick" :userhost "user@host" :target "target" :body "" :ago "unknown seconds")))))
