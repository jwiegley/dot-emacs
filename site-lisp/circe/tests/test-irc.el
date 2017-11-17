;; -*-lexical-binding: t-*-

(require 'buttercup)
(require 'irc)

;;;;;;;;;;;;;;;;;;;;;;;
;;; Connection function

(describe "The `irc-connect' function"
  :var (process-status)
  (before-each
    (spy-on 'make-tls-process :and-return-value 'the-test-tls-process)
    (spy-on 'make-network-process :and-return-value 'the-test-process)
    (spy-on 'process-status :and-call-fake (lambda (proc) process-status))
    (spy-on 'irc--sentinel :and-return-value nil))

  (it "should call `make-network-process' if tls was not requested"
    (irc-connect :host "irc.local"
                 :service 6667)

    (expect 'make-network-process
            :to-have-been-called-with
            :name "irc.local" :host "irc.local" :service 6667
            :family nil
            :coding 'no-conversion :nowait t :noquery t
            :filter #'irc--filter :sentinel #'irc--sentinel
            :plist '(:host "irc.local" :service 6667) :keepalive t))

  (it "should call `make-tls-process' if tls was requested"
    (irc-connect :host "irc.local"
                 :service 6667
                 :tls t)

    (expect 'make-tls-process
            :to-have-been-called))

  (it "should return a process when using non-tls connections"
    (expect (irc-connect :host "irc.local"
                         :service 6667)
            :to-be 'the-test-process))

  (it "should return a process when using tls connections"
    (expect (irc-connect :host "irc.local"
                         :service 6667
                         :tls t)
            :to-be 'the-test-tls-process))

  (it "should not use nowait if it is not supported"
    (spy-on 'featurep :and-return-value nil)

    (irc-connect :host "irc.local"
                 :service 6667)

    (expect 'featurep
            :to-have-been-called-with
            'make-network-process '(:nowait t))

    (expect 'make-network-process
            :to-have-been-called-with
            :name "irc.local" :host "irc.local" :service 6667
            :family nil
            :coding 'no-conversion :nowait nil :noquery t
            :filter #'irc--filter :sentinel #'irc--sentinel
            :plist '(:host "irc.local" :service 6667) :keepalive t))

  (it "should call the sentinel if nowait is not supported"
    (setq process-status 'open)

    (irc-connect :host "irc.local"
                 :service 6667)

    (expect 'irc--sentinel
            :to-have-been-called-with
            'the-test-process
            "open manually")))

(describe "Connection options"
  (let (proc)
    (before-each
      (setq proc (start-process "test" nil "cat")))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should retrieve options set"
      (irc-connection-put proc :key "value")

      (expect (irc-connection-get proc :key)
              :to-equal
              "value"))))

(describe "The `irc--sentinel' function"
  (before-each
    (spy-on 'irc-event-emit))

  (it "should emit conn.failed for a failed event"
    (irc--sentinel 'proc "failed to do something\n")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "conn.failed")

    (spy-calls-reset 'irc-event-emit)

    (irc--sentinel 'proc "failed\n")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "conn.failed"))

  (it "should emit conn.connected on an open event"
    (irc--sentinel 'proc "open\n")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "conn.connected"))

  (it "should emit conn.disconnected for a broken connection"
    (irc--sentinel 'proc "connection broken by remote peer\n")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "conn.disconnected"))

  (it "should emit conn.disconnected for a finished process"
    (irc--sentinel 'proc "finished\n")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "conn.disconnected"))

  (it "should emit conn.disconnected for an exiting process"
    (irc--sentinel 'proc "exited abnormally with code 54\n")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "conn.disconnected"))

  (it "should ignored killed processes"
    (irc--sentinel 'proc "killed\n")

    (expect 'irc-event-emit
            :not :to-have-been-called-with))

  (it "should ignore deleted processes"
    (irc--sentinel 'proc "deleted\n")

    (expect 'irc-event-emit
            :not :to-have-been-called))

  (it "should raise an error for unknown events"
    (expect (irc--sentinel 'proc "bla bla\n")
            :to-throw)))

(describe "The `irc--filter' function"
  (let (proc)
    (before-each
      (spy-on 'irc--handle-line)
      (setq proc (start-process "test" nil "cat")))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should handle single lines"
      (irc--filter proc "line\r\n")

      (expect 'irc--handle-line
              :to-have-been-called-with
              proc "line"))

    (it "should handle single lines even without CR"
      (irc--filter proc "line\n")

      (expect 'irc--handle-line
              :to-have-been-called-with
              proc "line"))

    (it "should handle multiple lines at once"
      (irc--filter proc "line1\r\nline2\r\nline3\r\n")

      (expect (spy-calls-all-args 'irc--handle-line)
              :to-equal
              `((,proc "line1")
                (,proc "line2")
                (,proc "line3"))))

    (it "should handle partial lines"
      (irc--filter proc "line1\r\nli")

      (expect 'irc--handle-line
              :to-have-been-called-with
              proc "line1")

      (spy-calls-reset 'irc--handle-line)

      (irc--filter proc "ne2\r\n")

      (expect 'irc--handle-line
              :to-have-been-called-with
              proc "line2"))

    (it "should not handle a line received while others are processed"
      ;; If you wonder what this is about, see the docstring of
      ;; `irc--filter-running-p'
      (spy-on 'irc--handle-line :and-call-fake
              (lambda (proc line)
                (when (equal line "line1")
                  (irc--filter proc "line3\r\n"))))

      (irc--filter proc "line1\r\nline2\r\n")

      (expect (spy-calls-all-args 'irc--handle-line)
              :to-equal
              `((,proc "line1")
                (,proc "line2")
                (,proc "line3"))))))

(describe "The `irc--handle-line' function"
  (before-each
    (spy-on 'irc-event-emit))

  (it "should emit an event for the command"
    (irc--handle-line 'proc ":sender COMMAND arg1 arg2")

    (expect 'irc-event-emit
            :to-have-been-called-with
            'proc "COMMAND" "sender" "arg1" "arg2")))

(describe "The `irc--parse' function"
  (it "should parse a command without anything else"
    (expect (irc--parse "COMMAND")
            :to-equal
            '(nil "COMMAND")))

  (it "should parse a command with a single argument"
    (expect (irc--parse "COMMAND arg")
            :to-equal
            '(nil "COMMAND" "arg")))

  (it "should parse a command with two arguments"
    (expect (irc--parse "COMMAND arg1 arg2")
            :to-equal
            '(nil "COMMAND" "arg1" "arg2")))

  (it "should treat single space as argument separator"
      (expect (irc--parse "COMMAND arg1  arg3")
              :to-equal
              '(nil "COMMAND" "arg1" "" "arg3")))

  (it "should parse a command with rest argument"
    (expect (irc--parse "COMMAND arg1 arg2 :arg3 still arg3")
            :to-equal
            '(nil "COMMAND" "arg1" "arg2" "arg3 still arg3")))

  (it "should parse a command with sender and no arguments"
    (expect (irc--parse ":sender COMMAND")
            :to-equal
            '("sender" "COMMAND")))

  (it "should parse a command with sender and a single argument"
    (expect (irc--parse ":sender COMMAND arg")
            :to-equal
            '("sender" "COMMAND" "arg")))

  (it "should parse a command with sender and two arguments"
    (expect (irc--parse ":sender COMMAND arg1 arg2")
            :to-equal
            '("sender" "COMMAND" "arg1" "arg2")))

  (it "should parse a command with sender and rest argument"
    (expect (irc--parse ":sender COMMAND arg1 arg2 :arg3 still arg3")
            :to-equal
            '("sender" "COMMAND" "arg1" "arg2" "arg3 still arg3")))

  (it "should decode arguments"
    (expect (irc--parse "PRIVMSG #channel :m\xc3\xb6p")
            :to-equal
            '(nil "PRIVMSG" "#channel" "möp")))

  (it "should decode arguments individually"
    ;; Undecided is broken in older Emacsen
    (when (version< emacs-version "24.4")
      (signal 'buttercup-pending t))
    ;; This is utf-16
    (expect (irc--parse
             (concat ":\xff\xfe\x6d\x00\xf6\x00\x70\x00 "
                     "PRIVMSG #channel :\xff\xfe\x6d\x00\xf6\x00\x70\x00"))
            :to-equal
            '("möp" "PRIVMSG" "#channel" "möp"))))

(describe "The `irc-userstring-nick' function"
  (it "should return the nick of a nick!user@host userstring"
    (expect (irc-userstring-nick "nick!user@host")
            :to-equal
            "nick"))

  (it "should return the string verbatim if it's something else"
    (expect (irc-userstring-nick "nick!usernoathost")
            :to-equal
            "nick!usernoathost")))

(describe "The `irc-userstring-userhost' function"
  (it "should return the user@host of a nick!user@host userstring"
    (expect (irc-userstring-userhost "nick!user@host")
            :to-equal
            "user@host"))

  (it "should return nil if it's something else"
    (expect (irc-userstring-userhost "nick!usernoathost")
            :to-equal
            nil)))

(describe "The `irc-event-emit' function"
  (let (proc handler-table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            handler-table (irc-handler-table))
      (irc-connection-put proc :handler-table handler-table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should run the irc-handler for the event"
      (let ((called-with nil))
        (irc-handler-add handler-table "the.event"
                         (lambda (&rest args)
                           (setq called-with args)))

        (irc-event-emit proc "the.event" 1 2 3)

        (expect called-with
                :to-equal
                `(,proc "the.event" 1 2 3))))

    (it "should run the irc-handler for nil"
      (let ((called-with nil))
        (irc-handler-add handler-table nil
                         (lambda (&rest args)
                           (setq called-with args)))

        (irc-event-emit proc "the.event" 1 2 3)

        (expect called-with
                :to-equal
                `(,proc "the.event" 1 2 3))))))

;;;;;;;;;;;;;;;;;;;;;;;
;;; Event handler table

(describe "The event handler table API"
  (it "should run an event that was added"
    (let ((table (irc-handler-table))
          (called-with nil))
      (irc-handler-add table "the.event" (lambda (&rest args)
                                           (setq called-with args)))

      (irc-handler-run table "the.event" 1 2 3)

      (expect called-with :to-equal '(1 2 3))))

  (it "should not throw an error if a handler throws one"
    (let ((table (irc-handler-table))
          (debug-on-error nil))
      (spy-on 'message)

      (irc-handler-add table "the.event" (lambda (&rest args)
                                           (error "Oops!")))

      (expect (irc-handler-run table "the.event")
              :not :to-throw)))

  (it "should not throw an error if a handler throws one and debug-on-error"
    (let ((table (irc-handler-table))
          (debug-on-error t))
      (irc-handler-add table "the.event" (lambda (&rest args)
                                           (error "Oops!")))

      (expect (irc-handler-run table "the.event")
              :to-throw)))

  (it "should not run a remove handler"
    (let* ((table (irc-handler-table))
           (called-with nil)
           (handler (lambda (&rest args)
                      (setq called-with args))))
      (irc-handler-add table "the.event" handler)
      (irc-handler-remove table "the.event" handler)

      (irc-handler-run table "the.event" 1 2 3)

      (expect called-with :to-equal nil))))

;;;;;;;;;;;
;;; Sending

(describe "The `irc-send-raw' function"
  (let (proc current-time)
    (before-each
      (setq proc (start-process "test" nil "cat")
            current-time (float-time))
      (spy-on 'process-send-string)
      (spy-on 'run-at-time)
      (spy-on 'float-time :and-call-fake (lambda ()
                                           current-time)))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (after-each
      (ignore-errors
        (delete-process proc)))

   (it "should send single messages immediately"
     (irc-send-raw proc "the line")

     (expect 'process-send-string
             :to-have-been-called-with
             proc "the line\r\n"))

   (it "should not create a timer for a single message"
     (irc-send-raw proc "the line")

     (expect 'run-at-time
             :not :to-have-been-called))

   (it "should prevent flooding"
     (dolist (line '("line1" "line2" "line3"
                     "line4" "line5" "line6"))
       (irc-send-raw proc line))

     (expect (spy-context-args
              (spy-calls-most-recent 'process-send-string))
             :to-equal
             `(,proc "line4\r\n")))

   (it "should continue sending after a delay"
     (dolist (line '("line1" "line2" "line3"
                     "line4" "line5" "line6"))
       (irc-send-raw proc line))
     (expect 'run-at-time
             :to-have-been-called)

     ;; Two minutes later
     (setq current-time (+ current-time 120))
     (irc-send--queue proc)

     (expect (spy-context-args
              (spy-calls-most-recent 'process-send-string))
             :to-equal
             `(,proc "line6\r\n")))

   (it "should drop lines if the flood queue is full and :drop is given"
     (dolist (line '("line1" "line2" "line3"
                     "line4" "line5" "line6"))
       (irc-send-raw proc line))

     (irc-send-raw proc "dropped" :drop)
     (setq current-time (+ current-time 120))
     (irc-send--queue proc)

     (expect (spy-context-args
              (spy-calls-most-recent 'process-send-string))
             :to-equal
             `(,proc "line6\r\n")))

   (it "should send items immediately if :nowait is given"
     (dolist (line '("line1" "line2" "line3"
                     "line4" "line5" "line6"))
       (irc-send-raw proc line))

     (irc-send-raw proc "priority" :nowait)

     (expect (spy-context-args
              (spy-calls-most-recent 'process-send-string))
             :to-equal
             `(,proc "priority\r\n")))

   (it "should encode strings being sent as utf-8"
     (irc-send-raw proc "möp")

     (expect 'process-send-string
             :to-have-been-called-with
             proc "m\xc3\xb6p\r\n"))))

(describe "The `irc-send-command'"
  (before-each
    (spy-on 'irc-send-raw))

  (it "should send properly-formatted commands"
    (irc-send-command 'proc "PRIVMSG" "#emacs" "Hello, World!")

    (expect 'irc-send-raw
            :to-have-been-called-with
            'proc "PRIVMSG #emacs :Hello, World!"))

  (it "should quote a final argument if it starts with a colon"
    (irc-send-command 'proc "PRIVMSG" "#emacs" ":-D")

    (expect 'irc-send-raw
            :to-have-been-called-with
            'proc "PRIVMSG #emacs ::-D"))

  (it "should fail if any argument is not a string"
    (expect (irc-send-command 'proc "PRIVMSG" 23 "Hi!")
            :to-throw))

  (it "should fail if any argument but the last has a space"
    (expect (irc-send-command 'proc "PRIVMSG" "#my channel" "Hello")
            :to-throw)))

(describe "The send function"
  (before-each
    (spy-on 'irc-send-raw))

  (describe "`irc-send-AUTHENTICATE'"
    (it "should send an AUTHENTICATE message"
      (irc-send-AUTHENTICATE 'proc "1234567890abcdef")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "AUTHENTICATE 1234567890abcdef")))

  (describe "`irc-send-AUTHENTICATE'"
    (it "should send an AWAY message with reason"
      (irc-send-AWAY 'proc "Away reason")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "AWAY :Away reason"))

    (it "should send an AWAY message without reason to return"
      (irc-send-AWAY 'proc)

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "AWAY")))

  (describe "`irc-send-CAP'"
    (it "should send a CAP message"
      (irc-send-CAP 'proc "LS")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "CAP LS")))

  (describe "`irc-send-INVITE'"
    (it "should send an INVITE message"
      (irc-send-INVITE 'proc "nick" "#channel")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "INVITE nick #channel")))

  (describe "`irc-send-JOIN'"
    (it "should send a normal JOIN"
      (irc-send-JOIN 'proc "#channel")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "JOIN #channel"))

    (it "should send a JOIN with key"
      (irc-send-JOIN 'proc "#channel" "secret key")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "JOIN #channel :secret key")))

  (describe "`irc-send-NAMES'"
    (it "should send a NAMES message with no arguments"
      (irc-send-NAMES 'proc)

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "NAMES"))

    (it "should send a NAMES message with a channel argument"
      (irc-send-NAMES 'proc "#channel")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "NAMES #channel")))

  (describe "`irc-send-NICK'"
    (it "should send a NICK message"
      (irc-send-NICK 'proc "New_Nick")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "NICK New_Nick")))

  (describe "`irc-send-NOTICE'"
    (it "should send a NOTICE message"
      (irc-send-NOTICE 'proc "#channel" "Hello, World")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "NOTICE #channel :Hello, World")))

  (describe "`irc-send-PART'"
    (it "should send a PART message"
      (irc-send-PART 'proc "#channel" "the reason")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "PART #channel :the reason")))

  (describe "`irc-send-PASS'"
    (it "should send a PASS message"
      (irc-send-PASS 'proc "top-secret-password")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "PASS top-secret-password")))

  (describe "`irc-send-PONG'"
    (it "should send a PONG message to a single server"
      (irc-send-PONG 'proc "server1")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "PONG server1" :nowait)))

  (describe "`irc-send-PRIVMSG'"
    (it "should send a PRIVMSG message"
      (irc-send-PRIVMSG 'proc "#channel" "Hello, World")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "PRIVMSG #channel :Hello, World")))

  (describe "`irc-send-QUIT'"
    (it "should send a QUIT message"
      (irc-send-QUIT 'proc "the reason")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "QUIT :the reason")))

  (describe "`irc-send-TOPIC'"
    (it "should retrieve a TOPIC with no new topic"
      (irc-send-TOPIC 'proc "#channel")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "TOPIC #channel"))

    (it "should set a TOPIC with new topic argument"
      (irc-send-TOPIC 'proc "#channel" "new topic")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "TOPIC #channel :new topic")))

  (describe "`irc-send-USER'"
    (it "should send a USER message"
      (irc-send-USER 'proc "username" 8 "My Real Name (honest)")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "USER username 8 * :My Real Name (honest)")))

  (describe "`irc-send-WHOIS'"
    (it "should send a WHOIS message"
      (irc-send-WHOIS 'proc "user")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "WHOIS user"))

    (it "should allow for an optional WHOIS argument"
      (irc-send-WHOIS 'proc "user" "user")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "WHOIS user user")))

  (describe "`irc-send-WHOWAS'"
    (it "should send a WHOWAS message"
      (irc-send-WHOWAS 'proc "user")

      (expect 'irc-send-raw
              :to-have-been-called-with
              'proc "WHOWAS user"))))

;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Registration

(defun client-messages ()
  (mapcar #'cadr (spy-calls-all-args 'irc-send-raw)))

(describe "The registration handler"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)
      (irc-connection-put proc :nick "My_Nick")
      (irc-connection-put proc :user "username")
      (irc-connection-put proc :mode 8)
      (irc-connection-put proc :realname "My Real Name")

      (spy-on 'irc-send-raw)

      (irc-handle-registration table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (describe "on conn.connected"
      (it "should send the standard registration on connect"
        (irc-event-emit proc "conn.connected")

        (expect (client-messages)
                :to-equal
                '("NICK My_Nick"
                  "USER username 8 * :My Real Name")))

      (it "should set the connection state to connected"
        (expect (irc-connection-state proc)
                :not :to-be
                'connected)

        (irc-event-emit proc "conn.connected")

        (expect (irc-connection-state proc)
                :to-be
                'connected))

      (it "should send a PASS message if a password is given"
        (irc-connection-put proc :pass "top-secret")

        (irc-event-emit proc "conn.connected")

        (expect (client-messages)
                :to-equal
                '("PASS top-secret"
                  "NICK My_Nick"
                  "USER username 8 * :My Real Name")))

      (it "should send a CAP request if the connection specifies it"
        (irc-connection-put proc :cap-req '("sasl"))

        (irc-event-emit proc "conn.connected")

        (expect (client-messages)
                :to-equal
                '("CAP LS"
                  "NICK My_Nick"
                  "USER username 8 * :My Real Name"))))

    (describe "on conn.disconnected"
      (it "should set the connection state to disconnected"
        (expect (irc-connection-state proc)
                :not :to-be
                'disconnected)

        (irc-event-emit proc "conn.disconnected")

        (expect (irc-connection-state proc)
                :to-be
                'disconnected)))

    (describe "on 001 RPL_WELCOME"
      (it "should set the connection stat to registered"
        (expect (irc-connection-state proc)
                :not :to-be
                'registered)

        (irc-event-emit proc "001" "irc.server" "My_Nick" "Welcome!")

        (expect (irc-connection-state proc)
                :to-be
                'registered))

      (it "should emit the irc.registered event"
        (let ((registered nil))
          (irc-handler-add table "irc.registered"
                           (lambda (conn event my-nick)
                             (setq registered my-nick)))

          (irc-event-emit proc "001" "irc.server" "My_Nick" "Welcome!")

          (expect registered :to-equal "My_Nick")))

      (it "should not fail when there are spurious arguments"
        (irc-event-emit proc "001" "irc.server" "My_Nick"
                        "Some" "broken" "arguments")))

    (describe "on a CAP message"
      (it "should do the full negotiation"
        (irc-connection-put proc :cap-req '("multi-prefix"))
        (irc-event-emit proc "conn.registered")
        (spy-calls-reset 'irc-send-raw)
        (irc-event-emit proc "CAP" "irc.server" "*" "LS" "multi-prefix")
        (irc-event-emit proc "CAP" "irc.server" "*" "ACK" "multi-prefix")

        (expect (client-messages)
                :to-equal
                '("CAP REQ multi-prefix"
                  "CAP END")))

      (it "should not negotiation with no common capabilities"
        (irc-connection-put proc :cap-req '("sasl"))
        (irc-event-emit proc "conn.registered")
        (spy-calls-reset 'irc-send-raw)
        (irc-event-emit proc "CAP" "irc.server" "*" "LS" "multi-prefix")

        (expect (client-messages)
                :to-equal
                '("CAP END"))))

    (describe "on SASL authentication"
      (it "should do the full negotiation"
        (irc-connection-put proc :cap-req '("sasl"))
        (irc-connection-put proc :sasl-username "my_nick")
        (irc-connection-put proc :sasl-password "top-secret")
        (irc-event-emit proc "conn.registered")
        (spy-calls-reset 'irc-send-raw)
        (irc-event-emit proc "CAP" "irc.server" "*" "LS" "sasl")
        (irc-event-emit proc "CAP" "irc.server" "*" "ACK" "sasl")
        (irc-event-emit proc "AUTHENTICATE" nil "+")

        (expect (client-messages)
                :to-equal
                '("CAP REQ sasl"
                  "AUTHENTICATE PLAIN"
                  "AUTHENTICATE bXlfbmljawBteV9uaWNrAHRvcC1zZWNyZXQ="
                  "CAP END"))))

    (describe "on SASL authentication"
      (it "should emit sasl.login for 900 numeric"
        (let (auth-args)
          (irc-handler-add table "sasl.login"
                           (lambda (&rest args)
                             (setq auth-args args)))

          (irc-event-emit proc "900" "irc.server" "mynick"
                          "mynick!user@host" "account"
                          "You are now logged in as mynick")

          (expect auth-args
                  :to-equal
                  (list proc "sasl.login" "mynick!user@host" "account")))))))

(describe "The `irc-connection-state' function"
  (let (proc)
    (before-each
      (setq proc (start-process "test" nil "cat")))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should return the connection state"
      (irc-connection-put proc :connection-state 'registered)

      (expect (irc-connection-state proc)
              :to-be
              'registered))

    (it "should return connecting if nothing was set"
      (expect (irc-connection-state proc)
              :to-be
              'connecting))))

;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Ping-Pong

(describe "The ping-pong handler"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)

      (spy-on 'irc-send-raw)

      (irc-handle-ping-pong table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should send PONG on a PING"
      (irc-event-emit proc "PING" "irc.server" "arg")

      (expect (client-messages)
              :to-equal
              '("PONG arg")))))

;;;;;;;;;;;;;;;;;;;;;
;;; Handler: ISUPPORT

(describe "The 005 RPL_ISUPPORT handler"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)

      (irc-handle-isupport table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should set the :isupport connection option"
      (irc-event-emit proc "005" "irc.server" "mynick" "WITHARG=#" "NOARG")

      (expect (irc-isupport proc "WITHARG")
              :to-equal
              "#")
      (expect (irc-isupport proc "NOARG")
              :to-equal
              t)
      (expect (irc-isupport proc "SOMETHINGELSE")
              :to-equal
              nil))

    (describe "string comparison function"
      (it "should compare with rfc1459 by default"
        (expect (irc-string-equal-p proc
                                    "FOO[]\\^"
                                    "foo{}|~")
                :to-be t))

      (it "should compare with rfc1459 if CASEMAPPING is rfc1459"
        (irc-event-emit proc "005" "irc.server" "mynick"
                        "CASEMAPPING=rfc1459")

        (expect (irc-string-equal-p proc
                                    "FOO[]\\^"
                                    "foo{}|~")
                :to-be t))

      (it "should compare with ascii mapping if casemapping is ascii"
        (irc-event-emit proc "005" "irc.server" "mynick"
                        "CASEMAPPING=ascii")
        (expect (irc-string-equal-p proc
                                    "FOO[]\\^"
                                    "foo[]\\^")
                :to-be t)
        (expect (irc-string-equal-p proc
                                    "FOO[]\\^"
                                    "foo{}|~")
                :not :to-be t))

      (it "should compare with rfc1459-strict mapping if casemapping is that"
        (irc-event-emit proc "005" "irc.server" "mynick"
                        "CASEMAPPING=rfc1459-strict")

        (expect (irc-string-equal-p proc
                                    "FOO[]\\"
                                    "foo{}|")
                :to-be t)
        (expect (irc-string-equal-p proc
                                    "FOO[]\\^"
                                    "foo{}|~")
                :not :to-be t)))

    (describe "the channel name identification"
      (it "should identify a channel name"
        (irc-event-emit proc "005" "irc.server" "mynick"
                        "CHANTYPES=#+")

        (expect (irc-channel-name-p proc "#foo") :to-be t)
        (expect (irc-channel-name-p proc "&foo") :not :to-be t)
        (expect (irc-channel-name-p proc "!foo") :not :to-be t)
        (expect (irc-channel-name-p proc "+foo") :to-be t)))

    (describe "the `irc-nick-without-prefix' function"
      (it "should remove a prefix"
        (irc-event-emit proc "005" "irc.server" "mynick"
                        "PREFIX=(ov)@+")

        (expect (irc-nick-without-prefix proc "@nick") :to-equal "nick")
        (expect (irc-nick-without-prefix proc "+nick") :to-equal "nick")
        (expect (irc-nick-without-prefix proc "%nick") :to-equal "%nick")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Initial nick acquisition

(describe "The initial nick acquisition handler"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)
      (irc-connection-put proc :nick-alternatives '("alt1" "alt2"))
      (spy-on 'irc-send-raw)

      (irc-handle-initial-nick-acquisition table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should try an alternative nick if the initial nick is bogus"
      (irc-event-emit proc "432" "irc.server" "*" "bogus"
                      "Erroneous Nickname")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "NICK alt1")
      (expect (irc-connection-get proc :nick-alternatives)
              :to-equal
              '("alt2")))

    (it "should try an alternative nick if the initial nick is in use"
      (irc-event-emit proc "433" "irc.server" "*" "inuse"
                      "Nickname is already in use.")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "NICK alt1")
      (expect (irc-connection-get proc :nick-alternatives)
              :to-equal
              '("alt2")))

    (it "should try an alternative nick if the initial nick unavailable"
      (irc-event-emit proc "437" "irc.server" "*" "unavail"
                      "Nickname is unavailable.")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "NICK alt1")
      (expect (irc-connection-get proc :nick-alternatives)
              :to-equal
              '("alt2")))

    (it "should not try an alternative nick if we already registered"
      (irc-event-emit proc "432" "irc.server" "mynick" "bogus"
                      "Erroneous Nickname")
      (irc-event-emit proc "433" "irc.server" "mynick" "inuse"
                      "Nickname is already in use.")
      (irc-event-emit proc "437" "irc.server" "mynick" "unavail"
                      "Nickname is unavailable.")

      (expect 'irc-send-raw :not :to-have-been-called))

    (it "should try a random nick if no alternatives available"
      (irc-connection-put proc :nick-alternatives nil)
      (spy-on 'irc-generate-nick :and-return-value "randomnick")
      (irc-event-emit proc "433" "irc.server" "*" "inuse"
                      "Nickname is already in use.")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "NICK randomnick"))))

(describe "The `irc-generate-nick' function"
  (it "should return a random, valid nick"
    (expect (stringp (irc-generate-nick)))))

;;;;;;;;;;;;;;;;;
;;; Handler: CTCP

(describe "The CTCP handler"
  (let (proc table last-message last-ctcp last-notice last-ctcpreply)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table)
            last-message nil
            last-ctcp nil
            last-notice nil
            last-ctcpreply nil)
      (irc-connection-put proc :handler-table table)
      (irc-handle-ctcp table)

      (irc-handler-add table "irc.message"
                       (lambda (proc &rest event)
                         (setq last-message event)))
      (irc-handler-add table "irc.notice"
                       (lambda (proc &rest event)
                         (setq last-notice event)))
      (irc-handler-add table "irc.ctcp"
                       (lambda (proc &rest event)
                         (setq last-ctcp event)))
      (irc-handler-add table "irc.ctcpreply"
                       (lambda (proc &rest event)
                         (setq last-ctcpreply event))))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should send irc.message on a normal PRIVMSG"
      (irc-event-emit proc "PRIVMSG" "alice" "bob" "Hi")

      (expect last-message
              :to-equal
              (list "irc.message" "alice" "bob" "Hi")))

    (it "should send irc.ctcp on a CTCP request with no arguments"
      (irc-event-emit proc "PRIVMSG" "alice" "bob" "\x01VERSION\x01")

      (expect last-message :to-be nil)
      (expect last-ctcp
              :to-equal
              (list "irc.ctcp" "alice" "bob" "VERSION" nil)))

    (it "should send irc.ctcp on a CTCP request with arguments"
      (irc-event-emit proc "PRIVMSG" "alice" "bob" "\x01PING foo\x01")

      (expect last-message :to-be nil)
      (expect last-ctcp
              :to-equal
              (list "irc.ctcp" "alice" "bob" "PING" "foo")))

    (it "should send irc.notice on a normal NOTICE"
      (irc-event-emit proc "NOTICE" "alice" "bob" "Hi")

      (expect last-notice
              :to-equal
              (list "irc.notice" "alice" "bob" "Hi")))

    (it "should send irc.ctcpreply on a CTCP reply with no arguments"
      (irc-event-emit proc "NOTICE" "alice" "bob" "\x01VERSION\x01")

      (expect last-notice :to-be nil)
      (expect last-ctcpreply
              :to-equal
              (list "irc.ctcpreply" "alice" "bob" "VERSION" nil)))

    (it "should send irc.ctcpreply on a CTCP reply with arguments"
      (irc-event-emit proc "NOTICE" "alice" "bob" "\x01PING foo\x01")

      (expect last-notice :to-be nil)
      (expect last-ctcpreply
              :to-equal
              (list "irc.ctcpreply" "alice" "bob" "PING" "foo")))

    (it "should send irc.ctcp.VERB for a CTCP request without argument"
      (let ((last-event nil))
        (irc-handler-add table "irc.ctcp.PING"
                         (lambda (proc &rest event)
                           (setq last-event event)))
        (irc-event-emit proc "PRIVMSG" "alice" "bob" "\x01PING\x01")

        (expect last-event
                :to-equal
                (list "irc.ctcp.PING" "alice" "bob" nil))))

    (it "should send irc.ctcp.VERB for a CTCP request with argument"
      (let ((last-event nil))
        (irc-handler-add table "irc.ctcp.PING"
                         (lambda (proc &rest event)
                           (setq last-event event)))
        (irc-event-emit proc "PRIVMSG" "alice" "bob" "\x01PING foo\x01")

        (expect last-event
                :to-equal
                (list "irc.ctcp.PING" "alice" "bob" "foo"))))

    (it "should send irc.ctcpreply.VERB for a CTCP reply without argument"
      (let ((last-event nil))
        (irc-handler-add table "irc.ctcpreply.PING"
                         (lambda (proc &rest event)
                           (setq last-event event)))
        (irc-event-emit proc "NOTICE" "alice" "bob" "\x01PING\x01")

        (expect last-event
                :to-equal
                (list "irc.ctcpreply.PING" "alice" "bob" nil))))

    (it "should send irc.ctcpreply.VERB for a CTCP reply with argument"
      (let ((last-event nil))
        (irc-handler-add table "irc.ctcpreply.PING"
                         (lambda (proc &rest event)
                           (setq last-event event)))
        (irc-event-emit proc "NOTICE" "alice" "bob" "\x01PING foo\x01")

        (expect last-event
                :to-equal
                (list "irc.ctcpreply.PING" "alice" "bob" "foo"))))

    (describe "`irc-send-ctcp' function"
      (before-each
        (spy-on 'irc-send-raw))

      (it "should send a CTCP request"
        (irc-send-ctcp proc "alice" "VERSION" "test version 1.0")

        (expect 'irc-send-raw
                :to-have-been-called-with
                proc
                "PRIVMSG alice :\x01VERSION test version 1.0\x01")))

    (describe "`irc-send-ctcpreply' function"
      (before-each
        (spy-on 'irc-send-raw))

      (it "should send a CTCP reply that is dropped on flooding"
        (irc-send-ctcpreply proc "alice" "VERSION" "test version 1.0")

        (expect 'irc-send-raw
                :to-have-been-called-with
                proc
                "NOTICE alice :\x01VERSION test version 1.0\x01"
                :drop)))

    (describe "default CTCP handlers"
      (before-each
        (spy-on 'irc-send-ctcpreply))

      (it "should respond with :ctcp-version to CTCP VERSION"
        (irc-connection-put proc :ctcp-version "test version 1.0")
        (irc-event-emit proc "irc.ctcp.VERSION" "alice" "bob" nil)

        (expect 'irc-send-ctcpreply
                :to-have-been-called-with
                proc "alice" "VERSION" "test version 1.0"))

      (it "should respond with :ctcp-clientinfo to CTCP CLIENTINFO"
        (irc-connection-put proc :ctcp-clientinfo "FOO BAR BAZ")
        (irc-event-emit proc "irc.ctcp.CLIENTINFO" "alice" "bob" nil)

        (expect 'irc-send-ctcpreply
                :to-have-been-called-with
                proc "alice" "CLIENTINFO" "FOO BAR BAZ"))

      (it "should respond with :ctcp-source to CTCP SOURCE"
        (irc-connection-put proc :ctcp-source "https://website/")
        (irc-event-emit proc "irc.ctcp.SOURCE" "alice" "bob" nil)

        (expect 'irc-send-ctcpreply
                :to-have-been-called-with
                proc "alice" "SOURCE" "https://website/"))

      (it "should respond with the argument to CTCP PING"
        (irc-event-emit proc "irc.ctcp.PING" "alice" "bob" "12345")

        (expect 'irc-send-ctcpreply
                :to-have-been-called-with
                proc "alice" "PING" "12345"))

      (it "should respond with the current time to CTCP TIME"
        (spy-on 'current-time-string :and-return-value "Test current time")
        (irc-event-emit proc "irc.ctcp.TIME" "alice" "bob" nil)

        (expect 'irc-send-ctcpreply
                :to-have-been-called-with
                proc "alice" "TIME" "Test current time"))

      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: State Tracking

(describe "The connection channels and users"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table)))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should create channels correctly"
      (let ((channel (irc-channel-from-name proc "#CHANNEL")))
        (expect (irc-channel-connection channel)
                :to-equal proc)
        (expect (irc-channel-name channel)
                :to-equal "#CHANNEL")
        (expect (irc-channel-folded-name channel)
                :to-equal "#channel")))

    (it "should not know channels not added yet"
      (expect (irc-connection-channel proc "#channel")
              :to-be nil))

    (it "should return a channel after it was added"
      (irc-connection-add-channel proc "#CHANNEL")

      (expect (irc-channel-name (irc-connection-channel proc "#channel"))
              :to-equal "#CHANNEL"))

    (it "should create users correctly"
      (let ((user (irc-user-from-userstring proc "SOMENICK!foo@bar")))
        (expect (irc-user-connection user)
                :to-equal proc)
        (expect (irc-user-nick user)
                :to-equal "SOMENICK")
        (expect (irc-user-folded-nick user)
                :to-equal "somenick")
        (expect (irc-user-userhost user)
                :to-equal "foo@bar")))

    (it "should return no user if not added yet"
      (let ((channel (irc-channel-from-name proc "#CHANNEL")))
        (expect (irc-channel-user channel "somenick")
                :to-be nil)))

    (it "should return the user object that was added before"
      (let ((channel (irc-channel-from-name proc "#CHANNEL")))
        (irc-channel-add-user channel "SOMENICK!user@host")

        (expect (irc-user-nick (irc-channel-user channel "somenick"))
                :to-equal "SOMENICK")))

    (it "should remove a channel"
      (irc-connection-add-channel proc "#channel")

      (irc-connection-remove-channel proc "#channel")

      (expect (irc-connection-channel proc "#channel")
              :to-be nil))

    (it "should remove a user"
      (let ((channel (irc-channel-from-name proc "#CHANNEL")))
        (irc-channel-add-user channel "SOMENICK!user@host")

        (irc-channel-remove-user channel "somenick")

        (expect (irc-channel-user channel "somenick")
                :to-be nil)))

    (it "should track all channels"
      (irc-connection-add-channel proc "#chan1")
      (irc-connection-add-channel proc "#chan2")
      (irc-connection-add-channel proc "#chan3")

      (expect (sort (mapcar #'irc-channel-name
                            (irc-connection-channel-list proc))
                    #'string<)
              :to-equal
              '("#chan1" "#chan2" "#chan3")))

    (it "should rember activity times for a rejoining user"
      (let ((channel (irc-channel-from-name proc "#channel"))
            user)
        (irc-channel-add-user channel "nick!user@host")
        (setq user (irc-channel-user channel "nick"))
        (setf (irc-user-last-activity-time user) 235)
        (irc-channel-remove-user channel "nick")
        (irc-channel-add-user channel "nick!user@host")

        (expect (irc-user-last-activity-time
                 (irc-channel-user channel "nick"))
                :to-equal 235)))

    (it "should rember activity times for a user regaining their nick"
      (let ((channel (irc-channel-from-name proc "#channel"))
            user)
        (irc-channel-add-user channel "nick!user@host")
        (setq user (irc-channel-user channel "nick"))
        (setf (irc-user-last-activity-time user) 235)
        (irc-channel-remove-user channel "nick")
        (irc-channel-add-user channel "nick2!user@host")

        (irc-channel-rename-user channel "nick2" "nick")

        (expect (irc-user-last-activity-time
                 (irc-channel-user channel "nick"))
                :to-equal 235)))))

(describe "The State Tracking handler"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)
      (irc-connection-put proc :current-nick "mynick")
      (irc-handle-state-tracking table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (describe "for the current nick"
      (it "should set the nick on 001 RPL_WELCOME"
        (irc-event-emit proc "001" "irc.server" "new-nick" "Welcome to IRC")

        (expect (irc-current-nick proc)
                :to-equal
                "new-nick")
        (expect (irc-current-nick-p proc "new-nick")
                :to-equal
                t))

      (it "should not fail when there are spurious arguments to 001"
        (irc-event-emit proc "001" "irc.server" "My_Nick"
                        "Some" "broken" "arguments"))

      (it "should change the nick on NICK"
        (irc-event-emit proc "001" "irc.server" "initial-nick" "Welcome to IRC")
        (irc-event-emit proc "NICK" "initial-nick!user@host" "new-nick")

        (expect (irc-current-nick proc)
                :to-equal
                "new-nick")
        (expect (irc-current-nick-p proc "new-nick")
                :to-equal
                t)))

    (describe "for joining"
      (it "should update the channel list if we join"
        (expect (irc-connection-channel proc "#channel")
                :to-be nil)

        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel")

        (expect (irc-connection-channel proc "#channel")
                :not :to-be nil))

      (it "should treat channels case-insensitively"
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel")

        (let ((channel (irc-connection-channel proc "#CHANNEL")))
          (expect (irc-channel-name channel)
                  :not :to-be nil)))

      (it "should update users in a channel if someone else joins"
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel")

        (let ((channel (irc-connection-channel proc "#channel")))
          (expect (irc-channel-user channel "otheruser")
                  :to-be nil)

          (irc-event-emit proc "JOIN" "otheruser!user@host" "#channel")

          (expect (irc-channel-user channel "otheruser")
                  :not :to-be nil)))

      (it "should not update users in a channel we are not there"
        (irc-event-emit proc "JOIN" "otheruser!user@host" "#channel")

        (expect (irc-connection-channel proc "#channel")
                :to-be nil))

      (it "should not fail on extended JOIN"
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel"
                        "account" "The real name")
        (irc-event-emit proc "JOIN" "otheruser!user@host" "#channel"
                        "account" "The real name"))

      (it "should set the join time"
        (spy-on 'float-time :and-return-value 23)
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel")

        (irc-event-emit proc "JOIN" "somenick!user@host" "#channel")

        (expect (irc-user-join-time
                 (irc-channel-user
                  (irc-connection-channel proc "#channel")
                  "somenick"))
                :to-equal 23)))

    (describe "for parting"
      (before-each
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel")
        (irc-event-emit proc "JOIN" "othernick!user@host" "#channel"))

      (it "should remove a channel if we part"
        (irc-event-emit proc "PART" "mynick!user@host" "#channel")

        (expect (irc-connection-channel proc "#channel")
                :to-be nil))

      (it "should remove a channel if we get kicked"
        (irc-event-emit proc "KICK" "somenick!user@host" "#channel" "mynick"
                        "You are out")

        (expect (irc-connection-channel proc "#channel")
                :to-be nil))

      (it "should remove all channels if we quit"
        (irc-event-emit proc "QUIT" "mynick!user@host" "I am out")

        (expect (irc-connection-channel proc "#channel")
                :to-be nil))

      (it "should remove a user if they part"
        (irc-event-emit proc "PART" "othernick!user@host" "#channel")

        (expect (irc-channel-user
                 (irc-connection-channel proc "#channel")
                 "othernick")
                :to-be nil))

      (it "should remove a channel from other users if we get kicked"
        (irc-event-emit proc "KICK" "mynick!user@host" "#channel" "othernick"
                        "You are out")

        (expect (irc-channel-user
                 (irc-connection-channel proc "#channel")
                 "othernick")
                :to-be nil))

      (it "should remove a user from a channel if they quit"
        (irc-event-emit proc "QUIT" "othernick!user@host" "I am out")

        (expect (irc-channel-user
                 (irc-connection-channel proc "#channel")
                 "othernick")
                :to-be nil))

      (it "should emit a signal for each channel a user was on if they quit"
        (let ((events nil))
          (irc-handler-add table "channel.quit"
                           (lambda (proc event sender channel message)
                             (push (list sender channel message) events)))

          (irc-event-emit proc "JOIN" "mynick!user@host" "#channel1")
          (irc-event-emit proc "JOIN" "othernick!user@host" "#channel1")
          (irc-event-emit proc "JOIN" "mynick!user@host" "#channel2")
          (irc-event-emit proc "JOIN" "othernick!user@host" "#channel2")
          (irc-event-emit proc "JOIN" "mynick!user@host" "#channel3")
          (irc-event-emit proc "QUIT" "othernick!user@host" "I am out")

          (expect events
                  :to-contain
                  '("othernick!user@host" "#channel1" "I am out"))
          (expect events
                  :to-contain
                  '("othernick!user@host" "#channel2" "I am out"))
          (expect events
                  :not :to-contain
                  '("othernick!user@host" "#channel3" "I am out"))
          )))

    (describe "for nick changes"
      (before-each
        (irc-event-emit proc "JOIN" "mynick!user@host" "#chan1")
        (irc-event-emit proc "JOIN" "mynick!user@host" "#chan2")
        (irc-event-emit proc "JOIN" "mynick!user@host" "#chan3")

        (irc-event-emit proc "JOIN" "othernick!user@host" "#chan1")
        (irc-event-emit proc "JOIN" "othernick!user@host" "#chan2"))

      (it "should update the user on all channels"
        (irc-event-emit proc "NICK" "othernick!user@host" "newnick")

        (expect (irc-channel-user
                 (irc-connection-channel proc "#chan1")
                 "othernick")
                :to-be nil)
        (expect (irc-channel-user
                 (irc-connection-channel proc "#chan1")
                 "newnick")
                :not :to-be nil)
        (expect (irc-channel-user
                 (irc-connection-channel proc "#chan2")
                 "othernick")
                :to-be nil)
        (expect (irc-channel-user
                 (irc-connection-channel proc "#chan2")
                 "newnick")
                :not :to-be nil)))

    (describe "for activity"
      (it "should set the last activity timestamp on PRIVMSG"
        (spy-on 'float-time :and-return-value 23)
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel")
        (irc-event-emit proc "JOIN" "othernick!user@host" "#channel")

        (irc-event-emit proc "PRIVMSG" "othernick!user@host" "#channel" "Hi!")

        (expect (irc-user-last-activity-time
                 (irc-channel-user
                  (irc-connection-channel proc "#channel")
                  "othernick"))
                :to-equal
                23)))

    (describe "for NAMES"
      (before-each
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel"))

      (it "should add nicks"
        (irc-event-emit proc "353" "irc.server" "mynick" "=" "#channel"
                        "nick1 @nick2")
        (irc-event-emit proc "353" "irc.server" "mynick" "=" "#channel"
                        "nick3")
        (irc-event-emit proc "366" "irc.server" "mynick" "#channel"
                        "End of /NAMES list")

        (let ((nicks nil))
          (maphash (lambda (nick-folded user)
                     (push (irc-user-nick user) nicks))
                   (irc-channel-users
                    (irc-connection-channel proc "#channel")))
          (setq nicks (sort nicks #'string<))

          (expect nicks :to-equal '("nick1" "nick2" "nick3"))))

      (it "should add nicks with a join time of nil"
        (irc-event-emit proc "353" "irc.server" "mynick" "=" "#channel"
                        "nick1")
        (irc-event-emit proc "366" "irc.server" "mynick" "#channel"
                        "End of /NAMES list")

        (expect (irc-user-join-time
                 (irc-channel-user
                  (irc-connection-channel proc "#channel")
                  "nick1"))
                :to-be nil))

      (it "should not touch existing nicks"
        (irc-event-emit proc "JOIN" "somenick!user@host" "#channel")
        (irc-event-emit proc "353" "irc.server" "mynick" "=" "#channel"
                        "SOMENICK")
        (irc-event-emit proc "366" "irc.server" "mynick" "#channel"
                        "End of /NAMES list")

        (expect (irc-user-nick
                 (irc-channel-user
                  (irc-connection-channel proc "#channel")
                  "SOMENICK"))
                :to-equal
                "somenick"))

      (it "should not fail for unknown channels"
        (irc-event-emit proc "353" "irc.server" "mynick" "=" "#unknown"
                        "SOMENICK")
        (irc-event-emit proc "366" "irc.server" "mynick" "#unknown"
                        "End of /NAMES list")))

    (describe "for recent channel users"
      (before-each
        (irc-event-emit proc "JOIN" "mynick!user@host" "#channel"))

      (it "should not know a recent user that was not there"
        (irc-event-emit proc "JOIN" "somenick!user@host" "#channel")

        (expect (irc-channel-recent-user
                 (irc-connection-channel proc "#channel")
                 "somenick")
                :to-be nil))

      (it "should add a user to recent users when they leave"
        (irc-event-emit proc "JOIN" "somenick!user@host" "#channel")
        (irc-event-emit proc "PART" "somenick!user@host" "#channel")

        (expect (irc-channel-recent-user
                 (irc-connection-channel proc "#channel")
                 "somenick")
                :not :to-be nil))

      (it "should set the part time"
        (irc-event-emit proc "JOIN" "somenick!user@host" "#channel")
        (let ((user (irc-channel-user
                     (irc-connection-channel proc "#channel")
                     "somenick")))
          (expect (irc-user-part-time user)
                  :to-be nil)

          (irc-event-emit proc "PART" "somenick!user@host" "#channel")

          (expect (irc-user-part-time user)
                  :not :to-be nil)))

      (it "should remove users who left over an hour ago"
        (spy-on 'float-time :and-return-value 10000)
        (irc-event-emit proc "JOIN" "nick1!user@host" "#channel")
        (irc-event-emit proc "JOIN" "nick2!user@host" "#channel")
        (irc-event-emit proc "PART" "nick1!user@host" "#channel")
        (spy-on 'float-time :and-return-value 13605)
        (irc-event-emit proc "PART" "nick2!user@host" "#channel")

        (expect (irc-channel-recent-user
                 (irc-connection-channel proc "#channel")
                 "nick1")
                :to-be nil)))

    (describe "for channel topics"
      (let (channel)
        (before-each
          (irc-connection-add-channel proc "#channel")
          (setq channel (irc-connection-channel proc "#channel")))

        (it "should leave the initial topic empty"
          (expect (irc-channel-topic channel)
                  :to-be nil)

          (irc-event-emit proc "331" "irc.server" "mynick" "#channel"
                          "No topic is set")

          (expect (irc-channel-topic channel)
                  :to-be nil))

        (it "should set the initial topic"
          (expect (irc-channel-topic channel)
                  :to-be nil)

          (irc-event-emit proc "332" "irc.server" "mynick" "#channel"
                          "The initial topic")

          (expect (irc-channel-topic channel)
                  :to-equal "The initial topic"))

        (it "should change topics"
          (irc-event-emit proc "TOPIC" "nick!user@host" "#channel" "New topic")

          (expect (irc-channel-topic channel)
                  :to-equal "New topic"))

        (it "should remember the old topic"
          (irc-event-emit proc "TOPIC" "nick!user@host" "#channel" "Old topic")
          (irc-event-emit proc "TOPIC" "nick!user@host" "#channel" "New topic")

          (expect (irc-channel-last-topic channel)
                  :to-equal "Old topic"))
        ))))

;;;;;;;;;;;;;;;;;;;;;
;;; Handler: NickServ

(describe "The nickserv handler"
  (let (proc table identified-args ghosted-args regained-args)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)

      (spy-on 'irc-send-raw)

      (dolist (elt
               '((:nickserv-nick "mynick")
                 (:nickserv-password "top-secret")
                 (:nickserv-mask "\\`NickServ!n@s\\'")
                 (:nickserv-identify-challenge "Please identify")
                 (:nickserv-identify-command
                  "PRIVMSG NickServ :IDENTIFY {nick} {password}")
                 (:nickserv-identify-confirmation "You are identified")
                 (:nickserv-ghost-command
                  "PRIVMSG NickServ :GHOST {nick} {password}")
                 (:nickserv-ghost-confirmation "has been ghosted")))
        (irc-connection-put proc (car elt) (cadr elt)))

      (irc-handle-nickserv table)

      (setq identified-args nil)
      (irc-handler-add table "nickserv.identified"
                       (lambda (&rest args)
                         (setq identified-args args)))
      (setq ghosted-args nil)
      (irc-handler-add table "nickserv.ghosted"
                       (lambda (&rest args)
                         (setq ghosted-args args)))
      (setq regained-args nil)
      (irc-handler-add table "nickserv.regained"
                       (lambda (&rest args)
                         (setq regained-args args))))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (describe "identification"
      (it "should register on the identify challenge"
        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "mynick"
                        "Please identify")

        (expect 'irc-send-raw
                :to-have-been-called-with
                proc "PRIVMSG NickServ :IDENTIFY mynick top-secret"))

      (it "should register with a password function"
        (irc-connection-put proc :nickserv-password
                            (lambda (conn)
                              "bottom-secret"))

        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "mynick"
                        "Please identify")

        (expect 'irc-send-raw
                :to-have-been-called-with
                proc "PRIVMSG NickServ :IDENTIFY mynick bottom-secret"))

      (it "should not respond to a fake challenge"
        (irc-event-emit proc "PRIVMSG" "NickServ!fake@host" "mynick"
                        "Please identify")

        (expect 'irc-send-raw
                :not :to-have-been-called))

      (it "should emit nickserv.identified for the identification confirmation"
        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "mynick"
                        "You are identified")

        (expect identified-args
                :to-equal
                (list proc "nickserv.identified")))

      (it "should not fail if no nickserv mask is given"
        (irc-connection-put proc :nickserv-mask nil)

        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "mynick"
                        "Please identify"))

      (it "should not fail if no password is given"
        (irc-connection-put proc :nickserv-password nil)

        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "mynick"
                        "Please identify")))

    (describe "ghosting"
      (it "should ghost if we do not have our nick"
        (irc-event-emit proc "irc.registered" "othernick")

        (expect 'irc-send-raw
                :to-have-been-called-with
                proc "PRIVMSG NickServ :GHOST mynick top-secret"))

      (it "should not ghost if we do have our nick"
        (irc-event-emit proc "irc.registered" "mynick")

        (expect 'irc-send-raw
                :not :to-have-been-called))

      (it "should emit nickserv.ghosted after successful ghosting"
        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "othernick"
                        "That person has been ghosted")

        (expect ghosted-args
                :to-equal
                (list proc "nickserv.ghosted")))

      (it "should regain the original nick"
        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "othernick"
                        "That person has been ghosted")

        (expect 'irc-send-raw
                :to-have-been-called-with
                proc "NICK mynick"))

      (it "should emit nickserv.regained when the nick is regained"
        (irc-event-emit proc "irc.registered" "othernick")
        (irc-event-emit proc "PRIVMSG" "NickServ!n@s" "othernick"
                        "That person has been ghosted")
        (irc-event-emit proc "NICK" "othernick!user@host" "mynick")

        (expect regained-args
                :to-equal
                (list proc "nickserv.regained")))

      (it "should not fail if no password is given"
        (irc-connection-put proc :nickserv-password nil)

        (irc-event-emit proc "irc.registered" "othernick")))))

(describe "The `irc-format' function"
  (it "should format simple strings"
    (expect (irc-format "{greeting}, {world}!"
                        'greeting "Hello"
                        'world "World")
            :to-equal
            "Hello, World!"))

  (it "should use string formatting for objects"
    (expect (irc-format "{obj}" 'obj (list 1 2 3))
            :to-equal
            "(1 2 3)")))

;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Auto join

(describe "The auto join handler"
  (let (proc table)
    (before-each
      (setq proc (start-process "test" nil "cat")
            table (irc-handler-table))
      (irc-connection-put proc :handler-table table)
      (irc-connection-put proc :nick "mynick")
      (irc-connection-put proc :nickserv-nick "mynick")
      (irc-connection-put
       proc :auto-join-after-registration '("#after-registration"))
      (irc-connection-put
       proc :auto-join-after-host-hiding '("#after-host-hiding"))
      (irc-connection-put
       proc :auto-join-after-nick-acquisition '("#after-nick-acquisition"))
      (irc-connection-put
       proc :auto-join-after-nickserv-identification
       '("#after-nickserv-identification"))
      (irc-connection-put
       proc :auto-join-after-sasl-login
       '("#after-sasl-login"))

      (spy-on 'irc-send-raw)

      (irc-handle-auto-join table))

    (after-each
      (ignore-errors
        (delete-process proc)))

    (it "should join channels after registration"
      (irc-event-emit proc "irc.registered" "mynick")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "JOIN #after-registration"))

    (it "should join channels after host hiding"
      (irc-event-emit proc "396" "server" "mynick" "host" "is now your host")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "JOIN #after-host-hiding"))

    (it "should join channels after nick regain"
      (irc-event-emit proc "nickserv.regained")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "JOIN #after-nick-acquisition"))

    (it "should join channels after nickserv identification"
      (irc-event-emit proc "nickserv.identified")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "JOIN #after-nickserv-identification"))

    (it "should join channels after sasl login"
      (irc-event-emit proc "sasl.login" "mynick!user@host" "account")

      (expect 'irc-send-raw
              :to-have-been-called-with
              proc "JOIN #after-sasl-login"))))
