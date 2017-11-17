;;; irc.el --- Library to handle IRC connections -*- lexical-binding: t -*-

;; Copyright (C) 2015  Jorgen Schaefer <contact@jorgenschaefer.de>

;; Author: Jorgen Schaefer <contact@jorgenschaefer.de>
;; URL: https://github.com/jorgenschaefer/circe

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; The main entry function is `irc-connect'. This creates a new
;; connection to an IRC server, and also takes an event handler table
;; which is used to run various event handlers. Handlers receive a
;; connection object which can be used for other API calls.

;; IRC connection objects also accept connection options. These can be
;; queried using `irc-connection-get', and are set by `irc-connect' or
;; later using `irc-connection-put'.

;; Event handler tables are simple maps of names to functions. See
;; `irc-handler-table', `irc-handler-add' and `irc-handler-run' for
;; the API.

;; To send commands to the server, use `irc-send-raw' or
;; `irc-send-command'.

;; The rest of the library are handler packs that add support for
;; various IRC features.

;;; Code:

(require 'cl-lib)
(require 'make-tls-process)

(defvar irc-debug-log nil
  "Emit protocol debug info if this is non-nil.")

;;;;;;;;;;;;;;;;;;;;;;;
;;; Connection function

(defun irc-connect (&rest keywords)
  "Connect to an IRC server.

Supported keyword arguments:

:name NAME -- The name for the process
:host HOST -- The host to connect to
:service SERVICE -- The service or port to connect to
:tls BOOL -- Whether to use TLS
:family IP-FAMILY -- Force using of ipv4 or ipv6
:handler-table HANDLER -- The event handler table to send events to.

The following events are supported:

conn.connected conn -- The connection was established
conn.failed conn -- The connection could not be established
conn.disconnected conn -- A previously established connection was lost

NNN conn sender args... -- A numeric reply from IRC was received
COMMAND conn sender args... -- An IRC command message was received"
  (let ((proc (funcall (if (plist-get keywords :tls)
                           #'make-tls-process
                         #'make-network-process)
                       :name (or (plist-get keywords :name)
                                 (plist-get keywords :host))
                       :host (or (plist-get keywords :host)
                                 (error "Must specify a :host to connect to"))
                       :service (or (plist-get keywords :service)
                                    (error "Must specify a :service to connect to"))
                       :family (plist-get keywords :family)
                       :coding 'no-conversion
                       :nowait (featurep 'make-network-process '(:nowait t))
                       :noquery t
                       :filter #'irc--filter
                       :sentinel #'irc--sentinel
                       :plist keywords
                       :keepalive t)))
    ;; When we used `make-network-process' without :nowait, the
    ;; sentinel is not called with the open event, so we do this
    ;; manually.
    (when (eq (process-status proc) 'open)
      (irc--sentinel proc "open manually"))
    proc))

(defun irc-connection-get (conn propname)
  "Return the value of CONN's PROPNAME property."
  (process-get conn propname))

(defun irc-connection-put (conn propname value)
  "Change CONN's PROPNAME property to VALUE."
  (process-put conn propname value))

(defun irc--sentinel (proc event)
  (cond
   ((string-match "\\`failed" event)
    (irc-event-emit proc "conn.failed"))
   ((string-match "\\`open" event)
    (irc-event-emit proc "conn.connected"))
   ((string-match "\\`\\(connection broken\\|finished\\|exited abnormally\\)"
                  event)
    (irc-event-emit proc "conn.disconnected"))
   ((string-match "\\`\\(deleted\\|killed\\)" event)
    nil)
   (t
    (error "Unknown event in IRC sentinel: %S" event))))

(defvar irc--filter-running-p nil
  "Non-nil when we're currently processing a message.

Yep, this is a mutex. Why would one need a mutex in Emacs, a
single-threaded application, you ask? Easy!

When, during the execution of a process filter, any piece of code
waits for process output - e.g. because they started a some
external program - Emacs will process any input from external
processes. Including the one for the filter that is currently
running.

If that process does emit output, the filter is run again, while
it is already running. If the filter is not careful, this can
cause data to arrive out of order, or get lost.")

(defun irc--filter (proc data)
  "Handle data from the process."
  (irc-connection-put proc :conn-data
                      (concat (or (irc-connection-get proc :conn-data)
                                  "")
                              data))
  (when (not irc--filter-running-p)
    (let ((irc--filter-running-p t)
          (data (irc-connection-get proc :conn-data)))
      (while (string-match "\r?\n" data)
        (let ((line (substring data 0 (match-beginning 0))))
          (setq data (substring data (match-end 0)))
          (irc-connection-put proc :conn-data data)
          (irc--handle-line proc line)
          (setq data (irc-connection-get proc :conn-data)))))))

(defun irc--handle-line (proc line)
  "Handle a single line from the IRC server.

The command is simply passed to the event handler of the IRC
connection."
  (irc-debug-out proc "S: %s" line)
  (let* ((parsed (irc--parse line))
         (sender (car parsed))
         (command (cadr parsed))
         (args (cddr parsed)))
    (apply #'irc-event-emit proc command sender args)))

(defun irc--parse (line)
  "Parse a line from IRC.

Returns a list: (sender command args...)

A line from IRC is a space-separated list of arguments. If the
first word starts with a colon, that's the sender. The first or
second word is the command. All further words are arguments. The
first word to start with a colon ends the argument list.

Examples:

COMMAND
COMMAND arg
COMMAND arg1 arg2
COMMAND arg1 arg2 :arg3 still arg3
:sender COMMAND arg1 arg2 :arg3 still arg3"
  (with-temp-buffer
    (insert line)
    (goto-char (point-min))
    (let ((sender nil)
          (args nil))
      ;; Optional sender.
      (when (looking-at ":\\([^ ]+\\) ")
        (setq sender (decode-coding-string
                      (match-string 1)
                      'undecided))
        (goto-char (match-end 0)))

      ;; COMMAND.
      (unless (looking-at "\\([^ ]+\\)")
        (error "Invalid message: %s" line))
      (push (decode-coding-string (match-string 1) 'undecided)
            args)
      (goto-char (match-end 0))

      ;; Arguments.
      (while (re-search-forward " :\\(.*\\)\\| \\([^ ]*\\)" nil t)
        (push (decode-coding-string
               (or (match-string 1)
                   (match-string 2))
               'undecided)
              args))

      (cons sender (nreverse args)))))

(defun irc-userstring-nick (userstring)
  "Return the nick in a given USERSTRING.

USERSTRING is a typical nick!user@host prefix as used by IRC."
  (if (string-match "\\`\\([^!]+\\)!\\([^@]+\\)@\\(.*\\)\\'" userstring)
      (match-string 1 userstring)
    userstring))

(defun irc-userstring-userhost (userstring)
  "Return the nick in a given USERSTRING.

USERSTRING is a typical nick!user@host prefix as used by IRC."
  (if (string-match "\\`\\([^!]+\\)!\\([^@]+@.*\\)\\'" userstring)
      (match-string 2 userstring)
    nil))

(defun irc-event-emit (conn event &rest args)
  "Run the event handlers for EVENT in CONN with ARGS."
  (irc-debug-out conn
                 "E: %S %s"
                 event
                 (mapconcat (lambda (elt) (format "%S" elt))
                            args
                            " "))
  (let ((handler-table (irc-connection-get conn :handler-table)))
    (when handler-table
      (apply #'irc-handler-run handler-table event conn event args)
      (apply #'irc-handler-run handler-table nil conn event args))))

;;;;;;;;;;;;;;;;;;;;;;;
;;; Event handler table

(defun irc-handler-table ()
  "Return a new event handler table."
  (make-hash-table :test 'equal))

(defun irc-handler-add (table event handler)
  "Add HANDLER for EVENT to the event handler table TABLE."
  (puthash event
           (append (gethash event table)
                   (list handler))
           table))

(defun irc-handler-remove (table event handler)
  "Remove HANDLER for EVENT to the event handler table TABLE."
  (puthash event
           (delete handler
                   (gethash event table))
           table))

(defun irc-handler-run (table event &rest args)
  "Run the handlers for EVENT in TABLE, passing ARGS to each."
  (dolist (handler (gethash event table))
    (if debug-on-error
        (apply handler args)
      (condition-case err
          (apply handler args)
        (error
         (message "Error running event %S handler %S: %S (args were %S)"
                  event handler err args))))))

;;;;;;;;;;;
;;; Sending

(defun irc-send-raw (conn line &optional flood-handling)
  "Send a line LINE to the IRC connection CONN.

LINE should not include the trailing newline.

FLOOD-HANDLING defines how to handle the situation when we are
sending too  much data. It can have three values:

nil -- Add the message to a queue and send it later
:nowait -- Send the message immediately, circumventing flood protection
:drop -- Send the message only if we are not flooding, and drop it if
   we have queued up messages.

The flood protection algorithm works like the one detailed in RFC
2813, section 5.8 \"Flood control of clients\".

  * If `flood-last-message' is less than the current
    time, set it equal.
  * While `flood-last-message' is less than `flood-margin'
    seconds ahead of the current time, send a message, and
    increase `flood-last-message' by `flood-penalty'."
  (cond
   ((null flood-handling)
    (irc-connection-put conn
                        :flood-queue
                        (append (irc-connection-get conn :flood-queue)
                                (list line)))
    (irc-send--queue conn))
   ((eq flood-handling :nowait)
    (irc-send--internal conn line))
   ((eq flood-handling :drop)
    (let ((queue (irc-connection-get conn :flood-queue)))
      (when (not queue)
        (irc-connection-put conn :flood-queue (list line))
        (irc-send--queue conn))))))

(defun irc-send--queue (conn)
  "Send messages from the flood queue in CONN.

See `irc-send-raw' for the algorithm."
  (let ((queue (irc-connection-get conn :flood-queue))
        (last-message (or (irc-connection-get conn :flood-last-message)
                          0))
        (margin (or (irc-connection-get conn :flood-margin)
                    10))
        (penalty (or (irc-connection-get conn :flood-penalty)
                     3))
        (now (float-time)))
    (when (< last-message now)
      (setq last-message now))
    (while (and queue
                (< last-message (+ now margin)))
      (irc-send--internal conn (car queue))
      (setq queue (cdr queue)
            last-message (+ last-message penalty)))
    (irc-connection-put conn :flood-queue queue)
    (irc-connection-put conn :flood-last-message last-message)
    (let ((timer (irc-connection-get conn :flood-timer)))
      (when timer
        (cancel-timer timer)
        (irc-connection-put conn :flood-timer nil))
      (when queue
        (irc-connection-put conn
                            :flood-timer
                            (run-at-time 1 nil #'irc-send--queue conn))))))

(defun irc-send--internal (conn line)
  "Send LINE to CONN."
  (irc-debug-out conn "C: %s" line)
  (process-send-string conn
                       (concat (encode-coding-string line 'utf-8)
                               "\r\n")))

(defun irc-send-command (conn command &rest args)
  "Send COMMAND with ARGS to IRC connection CONN."
  (irc-send-raw conn (apply #'irc--format-command command args)))

(defun irc--format-command (command &rest args)
  "Format COMMAND and ARGS for IRC.

The last value in ARGS will be escaped with a leading colon if it
contains a space. All other arguments are checked to make sure
they do not contain a space."
  (dolist (arg (cons command args))
    (when (not (stringp arg))
      (error "Argument must be a string")))
  (let* ((prefix (cons command (butlast args)))
         (last (last args)))
    (dolist (arg prefix)
      (when (string-match " " arg)
        (error "IRC protocol error: Argument %S must not contain space"
               arg)))
    (when (and last (or (string-match " " (car last))
                        (string-match "^:" (car last))
                        (equal "" (car last))))
      (setcar last (concat ":" (car last))))
    (mapconcat #'identity
               (append prefix last)
               " ")))

(defun irc-send-AUTHENTICATE (conn arg)
  "Send an AUTHENTICATE message with ARG.

See https://github.com/atheme/charybdis/blob/master/doc/sasl.txt
for details."
  (irc-send-command conn "AUTHENTICATE" arg))

(defun irc-send-AWAY (conn &optional reason)
  "Mark yourself as AWAY with reason REASON, or back if reason is nil."
  (if reason
      (irc-send-command conn "AWAY" reason)
    (irc-send-command conn "AWAY")))

(defun irc-send-CAP (conn &rest args)
  "Send a CAP message.

See https://tools.ietf.org/html/draft-mitchell-irc-capabilities-01
for details."
  (apply #'irc-send-command conn "CAP" args))

(defun irc-send-INVITE (conn nick channel)
  "Invite NICK to CHANNEL."
  (irc-send-command conn "INVITE" nick channel))

(defun irc-send-JOIN (conn channel &optional key)
  "Join CHANNEL.

If KEY is given, use it to join the password-protected channel."
  (if key
      (irc-send-command conn "JOIN" channel key)
    (irc-send-command conn "JOIN" channel)))

(defun irc-send-NAMES (conn &optional channel)
  "Retrieve user names from the server, optionally limited to CHANNEL."
  (if channel
      (irc-send-command conn "NAMES" channel)
    (irc-send-command conn "NAMES")))

(defun irc-send-NICK (conn nick)
  "Change your own nick to NICK."
  (irc-send-command conn "NICK" nick))

(defun irc-send-NOTICE (conn msgtarget text-to-be-sent)
  "Send a private notice containing TEXT-TO-BE-SENT to MSGTARGET.

MSGTARGET can be either a nick or a channel."
  (irc-send-command conn "NOTICE" msgtarget text-to-be-sent))

(defun irc-send-PART (conn channel reason)
  "Leave CHANNEL with reason REASON."
  (irc-send-command conn "PART" channel reason))

(defun irc-send-PASS (conn password)
  "Authenticate to the server using PASSWORD."
  (irc-send-command conn "PASS" password))

(defun irc-send-PONG (conn server)
  "Respond to a PING message."
  (irc-send-raw conn
                (irc--format-command "PONG" server)
                :nowait))

(defun irc-send-PRIVMSG (conn msgtarget text-to-be-sent)
  "Send a private message containing TEXT-TO-BE-SENT to MSGTARGET.

MSGTARGET can be either a nick or a channel."
  (irc-send-command conn "PRIVMSG" msgtarget text-to-be-sent))

(defun irc-send-QUIT (conn reason)
  "Leave IRC with reason REASON."
  (irc-send-command conn "QUIT" reason))

(defun irc-send-TOPIC (conn channel &optional new-topic)
  "Retrieve or set the topic of CHANNEL

If NEW-TOPIC is given, set this as the new topic. If it is
omitted, retrieve the current topic."
  (if new-topic
      (irc-send-command conn "TOPIC" channel new-topic)
    (irc-send-command conn "TOPIC" channel)))

(defun irc-send-USER (conn user mode realname)
  "Send a USER message for registration.

MODE should be an integer as per RFC 2812"
  (irc-send-command conn "USER" user (format "%s" mode) "*" realname))

(defun irc-send-WHOIS (conn target &optional server-or-name)
  "Retrieve current whois information on TARGET."
  (if server-or-name
      (irc-send-command conn "WHOIS" target server-or-name)
    (irc-send-command conn "WHOIS" target)))

(defun irc-send-WHOWAS (conn target)
  "Retrieve past whois information on TARGET."
  (irc-send-command conn "WHOWAS" target))

;;;;;;;;;;;;;;;
;;; Debug stuff

(defun irc-debug-out (conn fmt &rest args)
  (when irc-debug-log
    (let ((name (format "*IRC Protocol %s:%s*"
                        (irc-connection-get conn :host)
                        (irc-connection-get conn :service))))
      (with-current-buffer (get-buffer-create name)
        (save-excursion
          (goto-char (point-max))
          (insert (apply #'format fmt args) "\n"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Registration

(defun irc-handle-registration (table)
  "Add command handlers to TABLE to handle registration.

This will send the usual startup messages after we are connected.

Events emitted:

\"irc.registered\" current-nick -- We have successfully
  registered with the IRC server. Most commands can be used now.
  In particular, joining channels is only possible now.

\"sasl.login\" nick!user@host account -- SASL log in was
  successful.

Connection options used:

:nick -- The nick to use to register with the server
:user -- The user name to use
:mode -- The initial mode to use; an integer. See RFC 2812 for
   the meaning.
:realname -- The realname to use for the registration
:pass -- The server password to send
:cap-req -- CAP protocol capabilities to request, if available
:sasl-username -- The SASL username to send, if sasl is available
:sasl-password -- The SASL password to send, if sasl is available

Connection options set:

:connection-state -- One of nil, connected, registered, disconnected
  See `irc-connection-state' for an interface to this.
:cap-supported-p -- Non-nil if the server supports the CAP protocol
:cap-ack -- The list of active capabilities negotiated with the server"
  (irc-handler-add table "conn.connected"
                   #'irc-handle-registration--connected)
  (irc-handler-add table "conn.disconnected"
                   #'irc-handle-registration--disconnected)
  (irc-handler-add table "001" ;; RPL_WELCOME
                   #'irc-handle-registration--rpl-welcome)
  (irc-handler-add table "CAP"
                   #'irc-handle-registration--cap)
  (irc-handler-add table "AUTHENTICATE"
                   #'irc-handle-registration--authenticate)
  (irc-handler-add table "900" ;; RPL_LOGGEDIN
                   #'irc-handle-registration--logged-in))

(defun irc-handle-registration--connected (conn _event)
  (irc-connection-put conn :connection-state 'connected)
  (when (irc-connection-get conn :cap-req)
    (irc-send-CAP conn "LS"))
  (let ((password (irc-connection-get conn :pass)))
    (when password
      (irc-send-PASS conn password)))
  (irc-send-NICK conn (irc-connection-get conn :nick))
  (irc-send-USER conn
                 (irc-connection-get conn :user)
                 (irc-connection-get conn :mode)
                 (irc-connection-get conn :realname)))

(defun irc-handle-registration--disconnected (conn _event)
  (irc-connection-put conn :connection-state 'disconnected))

(defun irc-handle-registration--rpl-welcome (conn _event _sender target
                                                  &rest ignored)
  (irc-connection-put conn :connection-state 'registered)
  (irc-event-emit conn "irc.registered" target))

(defun irc-handle-registration--cap (conn _event _sender _target
                                          subcommand arg)
  (cond
   ((equal subcommand "LS")
    (let ((supported (split-string arg))
          (wanted nil))
      (dolist (cap (irc-connection-get conn :cap-req))
        (when (member cap supported)
          (setq wanted (append wanted (list cap)))))
      (if wanted
          (irc-send-CAP conn "REQ" (mapconcat #'identity wanted " "))
        (irc-send-CAP conn "END"))))
   ((equal subcommand "ACK")
    (let ((acked (split-string arg)))
      (irc-connection-put conn :cap-ack acked)
      (if (and (member "sasl" acked)
               (irc-connection-get conn :sasl-username)
               (irc-connection-get conn :sasl-password))
          (irc-send-AUTHENTICATE conn "PLAIN")
        (irc-send-CAP conn "END"))))
   (t
    (message "Unknown CAP response from server: %s %s" subcommand arg))))

(defun irc-handle-registration--authenticate (conn _event _sender arg)
  (if (equal arg "+")
      (let ((username (irc-connection-get conn :sasl-username))
            (password (irc-connection-get conn :sasl-password)))
        (irc-send-AUTHENTICATE conn (base64-encode-string
                                     (format "%s\x00%s\x00%s"
                                             username username password)))
        (irc-send-CAP conn "END"))
    (message "Unknown AUTHENTICATE response from server: %s" arg)))

(defun irc-handle-registration--logged-in (conn _event _sender _target
                                                userhost account _message)
  (irc-event-emit conn "sasl.login" userhost account))

(defun irc-connection-state (conn)
  "connecting connected registered disconnected"
  (let ((state (irc-connection-get conn :connection-state)))
    (if (null state)
        'connecting
      state)))

;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Ping-Pong

(defun irc-handle-ping-pong (table)
  "Add command handlers to respond to PING requests."
  (irc-handler-add table "PING" #'irc-handle-ping-pong--ping))

(defun irc-handle-ping-pong--ping (conn _event _sender argument)
  (irc-send-PONG conn argument))

;;;;;;;;;;;;;;;;;;;;;
;;; Handler: ISUPPORT

(defun irc-handle-isupport (table)
  "Add command handlers to track 005 RPL_ISUPPORT capabilities."
  (irc-handler-add table "005" #'irc-handle-isupport--005))

(defun irc-handle-isupport--005 (conn _event _sender _target &rest args)
  (irc-connection-put
   conn :isupport
   (append (irc-connection-get conn :isupport)
           (irc-handle-isupport--capabilities-to-alist args))))

(defun irc-handle-isupport--capabilities-to-alist (capabilities)
  (mapcar (lambda (cap)
            (if (string-match "\\`\\([^=]+\\)=\\(.*\\)\\'" cap)
                (cons (match-string 1 cap)
                      (match-string 2 cap))
              (cons cap t)))
          capabilities))

(defun irc-isupport (conn capability)
  "Return the value of CAPABILITY of CONN.

These capabilities are set when the server sends a 005
RPL_ISUPPORT message. The return value is either the value of the
capability, or t if it is a boolean capability that is present.
If the capability is not present, the return value is nil."
  (cdr (assoc capability
              (irc-connection-get conn :isupport))))

(defun irc-string-equal-p (conn s1 s2)
  "Compare S1 to S2 case-insensitively.

What case means is defined by the server of CONN."
  (equal (irc-isupport--case-fold conn s1)
         (irc-isupport--case-fold conn s2)))

(defvar irc-isupport--ascii-table
  (let ((table (make-string 128 0))
        (char 0))
    (while (<= char 127)
      (if (and (<= ?A char)
               (<= char ?Z))
          (aset table char (+ char (- ?a ?A)))
        (aset table char char))
      (setq char (1+ char)))
    table)
  "A case mapping table for the ascii CASEMAPPING.")

(defvar irc-isupport--rfc1459-table
  (let ((table (concat irc-isupport--ascii-table)))  ; copy string
    (aset table ?\[ ?\{)
    (aset table ?\] ?\})
    (aset table ?\\ ?\|)
    (aset table ?^ ?\~)
    table)
  "A case mapping table for the rfc1459 CASEMAPPING.")

(defvar irc-isupport--rfc1459-strict-table
  (let ((table (concat irc-isupport--ascii-table)))  ; copy string
    (aset table ?\[ ?\{)
    (aset table ?\] ?\})
    (aset table ?\\ ?\|)
    table)
  "A case mapping table for the rfc1459-strict CASEMAPPING.")

(defun irc-isupport--case-fold (conn s)
  "Translate S to be a lower-case.

This uses the case mapping defined by the IRC server for CONN."
  (with-temp-buffer
    (insert s)
    (let ((mapping (or (irc-isupport conn "CASEMAPPING")
                       "rfc1459")))
      (cond
       ((equal mapping "rfc1459")
        (translate-region (point-min)
                          (point-max)
                          irc-isupport--rfc1459-table))
       ((equal mapping "ascii")
        (translate-region (point-min)
                          (point-max)
                          irc-isupport--ascii-table))
       ((equal mapping "rfc1459-strict")
        (translate-region (point-min)
                          (point-max)
                          irc-isupport--rfc1459-strict-table))))
    (buffer-string)))

(defun irc-channel-name-p (conn string)
  "True iff STRING is a valid channel name for CONN.

This depends on the CHANTYPES setting set by the server of CONN."
  (let ((chantypes (string-to-list
                    (or (irc-isupport conn "CHANTYPES")
                        "#"))))
    (if (and (> (length string) 0)
             (member (aref string 0) chantypes))
        t
      nil)))

(defun irc-nick-without-prefix (conn nick)
  "Return NICK without any mode prefixes.

For example, a user with op status might be shown as @Nick. This
function would return Nick without the prefix. This uses the 005
RPL_ISUPPORT setting of PREFIX set by the IRC server for CONN."
  (let ((prefixes (irc-connection-get conn :nick-prefixes)))
    (when (not prefixes)
      (let ((prefix-string (or (irc-isupport conn "PREFIX")
                               "(qaohv)~&@%+")))
        (setq prefixes (string-to-list
                        (if (string-match "(.*)\\(.*\\)" prefix-string)
                            (match-string 1 prefix-string)
                          "~&@%+")))
        (irc-connection-put conn :nick-prefixes prefixes)))
    (while (and (> (length nick) 0)
                (member (aref nick 0) prefixes))
      (setq nick (substring nick 1)))
    nick))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Initial nick acquisition

(defun irc-handle-initial-nick-acquisition (table)
  "Track the current nick of the user.

Connection options used:

:nick-alternatives -- A list of nicks to try if the first attempt
  does not succeed."
  (irc-handler-add table "432" ;; ERR_ERRONEUSNICKNAME
                   #'irc-handle-initial-nick-acquisition--get-initial-nick)
  (irc-handler-add table "433" ;; ERR_NICKNAMEINUSE
                   #'irc-handle-initial-nick-acquisition--get-initial-nick)
  (irc-handler-add table "437" ;; ERR_UNAVAILRESOURCE
                   #'irc-handle-initial-nick-acquisition--get-initial-nick))

(defun irc-handle-initial-nick-acquisition--get-initial-nick
    (conn _event _sender current-nick _attempted-nick _reason)
  (when (equal current-nick "*")
    (let ((alternatives (irc-connection-get conn :nick-alternatives)))
      (if (not alternatives)
          (irc-send-NICK conn (irc-generate-nick))
        (irc-connection-put conn :nick-alternatives (cdr alternatives))
        (irc-send-NICK conn (car alternatives))))))

(defun irc-generate-nick ()
  "Return a random, valid IRC nick name.

Valid nick names are at least (RFC 1459):

<nick>       ::= <letter> { <letter> | <number> | <special> }
<special>    ::= '-' | '[' | ']' | '\' | '`' | '^' | '{' | '}'"
  (let ((chars "abcdefghijklmnopqrstuvwxyz"))
    (mapconcat (lambda (_)
                 (make-string 1 (aref chars (random (length chars)))))
               (make-string 9 0)
               "")))

;;;;;;;;;;;;;;;;;
;;; Handler: CTCP

(defun irc-handle-ctcp (table)
  "Add command handlers to TABLE to handle the CTCP protocol.

Connection options used:

:ctcp-version -- The response to a CTCP VERSION request.
:ctcp-clientinfo -- The response to a CTCP CLIENTINFO request.
:ctcp-source -- The response to a CTCP SOURCE request.

Events emitted:

\"irc.message\" sender target body -- A non-CTCP PRIVMSG
\"irc.notice\" sender target body -- A non-CTCP NOTICE
\"irc.ctcp\" sender target verb argument -- A CTCP request. ARGUMENT
  can be nil if there was no argument, or the empty string if the
  argument was empty.
\"irc.ctcpreply\" sender target verb argument -- A CTCP reply.
  ARGUMENT is similar to above.
\"irc.ctcp.VERB\" sender target argument -- A CTCP request of
  this specific type.
\"irc.ctcpreply.VERB\" sender target argument -- A CTCP reply of
  this specific type."
  (irc-handler-add table "PRIVMSG"
                   #'irc-handle-ctcp--privmsg)
  (irc-handler-add table "irc.ctcp"
                   #'irc-handle-ctcp--ctcp)
  (irc-handler-add table "NOTICE"
                   #'irc-handle-ctcp--notice)
  (irc-handler-add table "irc.ctcpreply"
                   #'irc-handle-ctcp--ctcpreply)
  (irc-handler-add table "irc.ctcp.VERSION"
                   #'irc-handle-ctcp--ctcp-version)
  (irc-handler-add table "irc.ctcp.CLIENTINFO"
                   #'irc-handle-ctcp--ctcp-clientinfo)
  (irc-handler-add table "irc.ctcp.SOURCE"
                   #'irc-handle-ctcp--ctcp-source)
  (irc-handler-add table "irc.ctcp.PING"
                   #'irc-handle-ctcp--ctcp-ping)
  (irc-handler-add table "irc.ctcp.TIME"
                   #'irc-handle-ctcp--ctcp-time)
  )

(defun irc-handle-ctcp--privmsg (conn _event sender target body)
  (if (string-match "\\`\x01\\([^ ]+\\)\\(?: \\(.*\\)\\)?\x01\\'"
                    body)
      (irc-event-emit conn "irc.ctcp" sender target
                      (match-string 1 body)
                      (match-string 2 body))
    (irc-event-emit conn "irc.message" sender target body)))

(defun irc-handle-ctcp--ctcp (conn _event sender target verb argument)
  (irc-event-emit conn
                  (format "irc.ctcp.%s" (upcase verb))
                  sender
                  target
                  argument))

(defun irc-handle-ctcp--notice (conn _event sender target body)
  (if (string-match "\\`\x01\\([^ ]+\\)\\(?: \\(.*\\)\\)?\x01\\'"
                    body)
      (irc-event-emit conn "irc.ctcpreply" sender target
                      (match-string 1 body)
                      (match-string 2 body))
    (irc-event-emit conn "irc.notice" sender target body)))

(defun irc-handle-ctcp--ctcpreply (conn _event sender target verb argument)
  (irc-event-emit conn
                  (format "irc.ctcpreply.%s" (upcase verb))
                  sender
                  target
                  argument))

(defun irc-handle-ctcp--ctcp-version (conn _event sender _target _argument)
  (let ((version (irc-connection-get conn :ctcp-version)))
    (when version
      (irc-send-ctcpreply conn
                          (irc-userstring-nick sender)
                          "VERSION"
                          version))))

(defun irc-handle-ctcp--ctcp-clientinfo (conn _event sender _target _argument)
  (let ((clientinfo (irc-connection-get conn :ctcp-clientinfo)))
    (when clientinfo
      (irc-send-ctcpreply conn
                          (irc-userstring-nick sender)
                          "CLIENTINFO"
                          clientinfo))))

(defun irc-handle-ctcp--ctcp-source (conn _event sender _target _argument)
  (let ((source (irc-connection-get conn :ctcp-source)))
    (when source
      (irc-send-ctcpreply conn
                          (irc-userstring-nick sender)
                          "SOURCE"
                          source))))

(defun irc-handle-ctcp--ctcp-ping (conn _event sender _target argument)
  (when argument
    (irc-send-ctcpreply conn
                        (irc-userstring-nick sender)
                        "PING"
                        argument)))

(defun irc-handle-ctcp--ctcp-time (conn _event sender _target _argument)
  (irc-send-ctcpreply conn
                      (irc-userstring-nick sender)
                      "TIME"
                      (current-time-string)))

(defun irc-send-ctcp (conn target verb &optional argument)
  "Send a CTCP VERB request to TARGET, optionally with ARGUMENT."
  (irc-send-PRIVMSG conn
                    target
                    (format "\x01%s%s\x01"
                            verb
                            (if argument
                                (concat " " argument)
                              ""))))

(defun irc-send-ctcpreply (conn target verb &optional argument)
  "Send a CTCP VERB reply to TARGET, optionally with ARGUMENT."
  (irc-send-raw conn
                (irc--format-command "NOTICE"
                                     target
                                     (format "\x01%s%s\x01"
                                             verb
                                             (if argument
                                                 (concat " " argument)
                                               "")))
                :drop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: State tracking

(defun irc-handle-state-tracking (table)
  "Add command handlers to TABLE to track the IRC state.

Connection options used:

:current-nick -- The current nick, or nil if not known/set yet.

Use helper functions to access the information tracked by this
handler:

- `irc-current-nick'
- `irc-current-nick-p'

Events emitted:

\"channel.quit\" sender channel reason -- A user quit IRC and
    left this channel that way."
  (irc-handler-add table "001" ;; RPL_WELCOME
                   #'irc-handle-state-tracking--rpl-welcome)
  (irc-handler-add table "JOIN"
                   #'irc-handle-state-tracking--JOIN)
  (irc-handler-add table "PART"
                   #'irc-handle-state-tracking--PART)
  (irc-handler-add table "KICK"
                   #'irc-handle-state-tracking--KICK)
  (irc-handler-add table "QUIT"
                   #'irc-handle-state-tracking--QUIT)
  (irc-handler-add table "NICK"
                   #'irc-handle-state-tracking--NICK)
  (irc-handler-add table "PRIVMSG"
                   #'irc-handle-state-tracking--PRIVMSG)
  (irc-handler-add table "353" ;; RPL_NAMREPLY
                   #'irc-handle-state-tracking--rpl-namreply)
  (irc-handler-add table "366" ;; RPL_ENDOFNAMES
                   #'irc-handle-state-tracking--rpl-endofnames)

  (irc-handler-add table "TOPIC"
                   #'irc-handle-state-tracking--TOPIC)
  (irc-handler-add table "331" ;; RPL_NOTOPIC
                   #'irc-handle-state-tracking--rpl-notopic)
  (irc-handler-add table "332" ;; RPL_TOPIC
                   #'irc-handle-state-tracking--rpl-topic)
  )

(cl-defstruct irc-channel
  name
  topic
  last-topic
  folded-name
  users
  recent-users
  receiving-names
  connection)

(defun irc-channel-from-name (conn name)
  "Create a new IRC channel object on CONN, named NAME."
  (make-irc-channel :name name
                    :folded-name (irc-isupport--case-fold conn name)
                    :users (make-hash-table :test 'equal)
                    :recent-users (make-hash-table :test 'equal)
                    :connection conn))

(defun irc-connection-channel (conn channel-name)
  "Return the channel object for CHANNEL-NAME on CONN."
  (let ((channel-table (irc--connection-channel-table conn))
        (folded-name (irc-isupport--case-fold conn channel-name)))
    (gethash folded-name channel-table)))

(defun irc-connection-channel-list (conn)
  "Return the list of channel object on CONN."
  (let ((channel-list nil))
    (maphash (lambda (_folded-name channel)
               (push channel channel-list))
             (irc--connection-channel-table conn))
    channel-list))

(defun irc-connection-add-channel (conn channel-name)
  "Add CHANNEL-NAME to the channel table of CONN."
  (let* ((channel-table (irc--connection-channel-table conn))
         (channel (irc-channel-from-name conn channel-name))
         (folded-name (irc-channel-folded-name channel)))
    (when (not (gethash folded-name channel-table))
      (puthash folded-name channel channel-table))))

(defun irc-connection-remove-channel (conn channel-name)
  "Remove CHANNEL-NAME from the channel table of CONN."
  (let* ((channel-table (irc--connection-channel-table conn))
         (folded-name (irc-isupport--case-fold conn channel-name)))
    (remhash folded-name channel-table)))

(defun irc-current-nick (conn)
  "Return the current nick on IRC connection CONN, or nil if not set yet."
  (irc-connection-get conn :current-nick))

(defun irc-current-nick-p (conn nick)
  "Return t if NICK is our current nick on IRC connection CONN."
  (let ((current-nick (irc-current-nick conn)))
    (if (and (stringp nick)
             (stringp current-nick))
        (irc-string-equal-p conn current-nick nick)
      nil)))

(defun irc--connection-channel-table (conn)
  (let ((table (irc-connection-get conn :channel-table)))
    (when (not table)
      (setq table (make-hash-table :test 'equal))
      (irc-connection-put conn :channel-table table))
    table))

(cl-defstruct irc-user
  nick
  folded-nick
  userhost
  join-time
  last-activity-time
  part-time
  connection)

(defun irc-user-from-userstring (conn userstring)
  "Create an irc-user struct on CONN from USERSTRING.

USERSTRING should be a s tring of the form \"nick!user@host\"."
  (let ((nick (irc-userstring-nick userstring)))
    (make-irc-user :nick nick
                   :folded-nick (irc-isupport--case-fold conn nick)
                   :userhost (let ((nick-len (length nick)))
                               (if (>= nick-len (length userstring))
                                   nil
                                 (substring userstring (1+ nick-len))))
                   :connection conn)))

(defun irc-channel-user (channel nick)
  "Return a user named NICK on channel CHANNEL."
  (let ((user-table (irc-channel-users channel))
        (folded-nick (irc-isupport--case-fold (irc-channel-connection channel)
                                              nick)))
    (gethash folded-nick user-table)))

(defun irc-channel-recent-user (channel nick)
  "Return a recent user named NICK on channel CHANNEL."
  (let ((user-table (irc-channel-recent-users channel))
        (folded-nick (irc-isupport--case-fold (irc-channel-connection channel)
                                              nick)))
    (gethash folded-nick user-table)))

(defun irc-channel-add-user (channel userstring)
  "Add USER to CHANNEL."
  (let* ((user-table (irc-channel-users channel))
         (user (irc-user-from-userstring (irc-channel-connection channel)
                                         userstring))
         (folded-nick (irc-user-folded-nick user))
         (recent-user (irc-channel-recent-user channel (irc-user-nick user))))
    (when (not (gethash folded-nick user-table))
      (when (and recent-user
                 (equal (irc-user-userhost recent-user)
                        (irc-user-userhost user)))
        (setf (irc-user-last-activity-time user)
              (irc-user-last-activity-time recent-user)))
      (puthash folded-nick user user-table)
      user)))

(defun irc-channel-remove-user (channel nick)
  "Remove NICK from CHANNEL."
  (let* ((user-table (irc-channel-users channel))
         (recent-user-table (irc-channel-recent-users channel))
         (folded-nick (irc-isupport--case-fold (irc-channel-connection channel)
                                               nick))
         (user (gethash folded-nick user-table)))
    (remhash folded-nick user-table)
    (when user
      (setf (irc-user-part-time user) (float-time))
      (puthash folded-nick user recent-user-table)
      (maphash (lambda (folded-nick user)
                 (when (< (irc-user-part-time user)
                          (- (float-time)
                             (* 60 60)))
                   (remhash folded-nick recent-user-table)))
               recent-user-table))))

(defun irc-channel-rename-user (channel oldnick newnick)
  "Update CHANNEL so that the user with nick OLDNICK now has nick NEWNICK."
  (let ((user-table (irc-channel-users channel))
        (user (irc-channel-user channel oldnick))
        (newnick-folded (irc-isupport--case-fold
                         (irc-channel-connection channel)
                         newnick))
        (recent-user (irc-channel-recent-user channel newnick)))
    (when user
      (when (and recent-user
                 (equal (irc-user-userhost recent-user)
                        (irc-user-userhost user)))
        (setf (irc-user-last-activity-time user)
              (irc-user-last-activity-time recent-user)))
      (remhash (irc-user-folded-nick user) user-table)
      (setf (irc-user-nick user) newnick)
      (setf (irc-user-folded-nick user) newnick-folded)
      (puthash (irc-user-folded-nick user) user user-table))))

(defun irc-handle-state-tracking--rpl-welcome (conn _event _sender target
                                                    &rest ignored)
  (irc-connection-put conn :current-nick target))

(defun irc-handle-state-tracking--JOIN (conn _event sender target
                                             &optional _account _realname)
  (let ((nick (irc-userstring-nick sender)))
    (cond
     ((irc-current-nick-p conn nick)
      (irc-connection-add-channel conn target))
     (t
      (let ((channel (irc-connection-channel conn target)))
        (when channel
          (let ((user (irc-channel-add-user channel sender)))
            (when user
              (setf (irc-user-join-time user) (float-time))))))))))

(defun irc-handle-state-tracking--PART (conn _event sender target
                                             &optional _reason)
  (let ((nick (irc-userstring-nick sender)))
    (cond
     ((irc-current-nick-p conn nick)
      (irc-connection-remove-channel conn target))
     (t
      (let ((channel (irc-connection-channel conn target)))
        (when channel
          (irc-channel-remove-user channel nick)))))))

(defun irc-handle-state-tracking--KICK (conn _event _sender target nick
                                             &optional _reason)
  (cond
   ((irc-current-nick-p conn nick)
    (irc-connection-remove-channel conn target))
   (t
    (let ((channel (irc-connection-channel conn target)))
      (when channel
        (irc-channel-remove-user channel nick))))))

(defun irc-handle-state-tracking--QUIT (conn _event sender
                                             &optional reason)
  (let ((nick (irc-userstring-nick sender)))
    (if (irc-current-nick-p conn nick)
        (dolist (channel (irc-connection-channel-list conn))
          (irc-connection-remove-channel conn
                                         (irc-channel-folded-name channel)))
      (dolist (channel (irc-connection-channel-list conn))
        (when (irc-channel-user channel nick)
          (irc-event-emit conn "channel.quit"
                          sender
                          (irc-channel-name channel)
                          reason))
        (irc-channel-remove-user channel nick)))))

(defun irc-handle-state-tracking--NICK (conn _event sender new-nick)
  ;; Update channels
  (let ((nick (irc-userstring-nick sender)))
    (dolist (channel (irc-connection-channel-list conn))
      (irc-channel-rename-user channel nick new-nick)))
  ;; Update our own nick
  (when (irc-current-nick-p conn (irc-userstring-nick sender))
    (irc-connection-put conn :current-nick new-nick)))

(defun irc-handle-state-tracking--PRIVMSG (conn _event sender target _message)
  (let ((channel (irc-connection-channel conn target))
        (nick (irc-userstring-nick sender)))
    (when channel
      (let ((user (irc-channel-user channel nick)))
        (when user
          (setf (irc-user-last-activity-time user) (float-time)))))))

(defun irc-handle-state-tracking--rpl-namreply
    (conn _event _sender _current-nick _channel-type channel-name nicks)
  (let ((channel (irc-connection-channel conn channel-name)))
    (when channel
      (setf (irc-channel-receiving-names channel)
            (append (irc-channel-receiving-names channel)
                    (mapcar (lambda (nick)
                              (irc-nick-without-prefix
                               conn
                               (string-trim nick)))
                            (split-string nicks)))))))

(defun irc-handle-state-tracking--rpl-endofnames
    (conn _event _sender _current-nick channel-name _description)
  (let ((channel (irc-connection-channel conn channel-name)))
    (when channel
      (irc-channel--synchronize-nicks channel
                                      (irc-channel-receiving-names channel))
      (setf (irc-channel-receiving-names channel) nil))))

(defun irc-channel--synchronize-nicks (channel nicks)
  "Update the user list of CHANNEL to match NICKS."
  (let ((have (irc-channel-users channel))
        (want (make-hash-table :test 'equal)))
    (dolist (nick nicks)
      (puthash (irc-isupport--case-fold (irc-channel-connection channel)
                                        nick)
               nick
               want))
    (maphash (lambda (nick-folded user)
               (when (not (gethash nick-folded want))
                 (irc-channel-remove-user channel
                                          (irc-user-nick user))))
             have)
    (maphash (lambda (_nick-folded nick)
               (irc-channel-add-user channel nick))
             want)))

(defun irc-handle-state-tracking--TOPIC (conn _event _sender channel new-topic)
  (let ((channel (irc-connection-channel conn channel)))
    (when channel
      (setf (irc-channel-last-topic channel)
            (irc-channel-topic channel))
      (setf (irc-channel-topic channel) new-topic))))

(defun irc-handle-state-tracking--rpl-notopic (conn _event _sender
                                                    _current-nick channel
                                                    _no-topic-desc)
  (let ((channel (irc-connection-channel conn channel)))
    (when channel
      (setf (irc-channel-topic channel) nil))))

(defun irc-handle-state-tracking--rpl-topic (conn _event _sender _current-nick
                                                  channel topic)
  (let ((channel (irc-connection-channel conn channel)))
    (when channel
      (setf (irc-channel-topic channel) topic))))

;;;;;;;;;;;;;;,;;;;;;
;;; Handler: NickServ

(defun irc-handle-nickserv (table)
  "Add command handlers to TABLE to deal with NickServ.

Connection options used:

:nickserv-nick -- The nick to register as

:nickserv-password -- The password for nickserv; can be a function and
  is then called with the IRC connection as its sole argument

:nickserv-mask -- A regular expression matching the correct NickServ's
  nick!user@host string to avoid fakes

:nickserv-identify-challenge -- A regular expression matching the
  challenge sent by NickServ to request identification

:nickserv-identify-command -- The raw IRC command to send to identify;
  expands {nick} and {password} when present

:nickserv-identify-confirmation -- A regular expression matching the
  confirmation message from NickServ after successful identification

:nickserv-ghost-command -- The raw IRC comment to ghost your
  original nick; expands {nick} and {password}. Set this to nil
  to disable ghosting and nick regaining.

:nickserv-ghost-confirmation -- A regular expression matching the
  confirmation message that the nick was ghosted

Events emitted:

\"nickserv.identified\" -- We have successfully identified with nickserv.

\"nickserv.ghosted\" -- We have ghosted a nick."
  (irc-handler-add table "irc.registered" #'irc-handle-nickserv--registered)
  (irc-handler-add table "NOTICE" #'irc-handle-nickserv--NOTICE)
  (irc-handler-add table "PRIVMSG" #'irc-handle-nickserv--NOTICE)
  (irc-handler-add table "NICK" #'irc-handle-nickserv--NICK))

(defun irc-handle-nickserv--password (conn)
  (let ((password (irc-connection-get conn :nickserv-password)))
    (if (functionp password)
        (funcall password conn)
      password)))

(defun irc-handle-nickserv--registered (conn _event current-nick)
  (let ((ghost-command (irc-connection-get conn :nickserv-ghost-command))
        (wanted-nick (irc-connection-get conn :nickserv-nick))
        (password (irc-handle-nickserv--password conn)))
    (when (and ghost-command
               wanted-nick
               password
               (not (irc-string-equal-p conn current-nick wanted-nick)))
      (irc-send-raw conn
                    (irc-format ghost-command
                                'nick wanted-nick
                                'password password)))))

(defun irc-handle-nickserv--NOTICE (conn _event sender _target message)
  (let ((nickserv-mask (irc-connection-get conn :nickserv-mask))
        identify-challenge identify-command identify-confirmation
        ghost-confirmation
        nickserv-nick nickserv-password)
    (when (and nickserv-mask (string-match nickserv-mask sender))
      (setq identify-challenge
            (irc-connection-get conn :nickserv-identify-challenge))
      (setq identify-command
            (irc-connection-get conn :nickserv-identify-command))
      (setq identify-confirmation
            (irc-connection-get conn :nickserv-identify-confirmation))
      (setq ghost-confirmation
            (irc-connection-get conn :nickserv-ghost-confirmation))
      (setq nickserv-nick (irc-connection-get conn :nickserv-nick))
      (setq nickserv-password (irc-handle-nickserv--password conn))
      (cond
       ;; Identify
       ((and identify-challenge
             identify-command
             nickserv-nick
             nickserv-password
             (string-match identify-challenge message))
        (irc-send-raw conn
                      (irc-format identify-command
                                  'nick nickserv-nick
                                  'password nickserv-password)))
       ;; Identification confirmed
       ((and identify-confirmation
             (string-match identify-confirmation message))
        (irc-event-emit conn "nickserv.identified"))
       ;; Ghosting confirmed
       ((and ghost-confirmation
             (string-match ghost-confirmation message))
        (irc-event-emit conn "nickserv.ghosted")
        (irc-connection-put conn :nickserv-regaining-nick t)
        (when nickserv-nick
          (irc-send-NICK conn nickserv-nick)))))))

(defun irc-handle-nickserv--NICK (conn _event _sender new-nick)
  (when (and (irc-connection-get conn :nickserv-regaining-nick)
             (irc-string-equal-p conn new-nick
                                 (irc-connection-get conn :nickserv-nick)))
    (irc-connection-put conn :nickserv-regaining-nick nil)
    (irc-event-emit conn "nickserv.regained")))

(defun irc-format (format &rest args)
  "Return a formatted version of FORMAT, using substitutions from ARGS.

The substitutions are identified by braces ('{' and '}')."
  (with-temp-buffer
    (insert format)
    (goto-char (point-min))
    (while (re-search-forward "{\\([^}]*\\)}" nil t)
      (replace-match (format "%s" (plist-get args (intern (match-string 1))))
                     t t))
    (buffer-string)))

;;;;;;;;;;;;;;;;;;;;;;
;;; Handler: Auto-Join

(defun irc-handle-auto-join (table)
  "Add command handlers to TABLE to deal with NickServ.

Connection options used:

:auto-join-after-registration -- List of channels to join
  immediately after registration with the server

:auto-join-after-host-hiding -- List of channels to join
  after our host was hidden

:auto-join-after-nick-acquisition -- List of channels to join
  after we gained our desired nick

:auto-join-after-nickserv-identification -- List of channels
  to join after we identified successfully with NickServ"
  (irc-handler-add table "irc.registered" #'irc-handle-auto-join--registered)
  (irc-handler-add table "396" ;; RPL_HOSTHIDDEN
                   #'irc-handle-auto-join--rpl-hosthidden)
  (irc-handler-add table "nickserv.regained"
                   #'irc-handle-auto-join--nickserv-regained)
  (irc-handler-add table "nickserv.identified"
                   #'irc-handle-auto-join--nickserv-identified)
  (irc-handler-add table "sasl.login"
                   #'irc-handle-auto-join--sasl-login))

(defun irc-handle-auto-join--registered (conn _event _current-nick)
  (dolist (channel (irc-connection-get conn :auto-join-after-registration))
    (irc-send-JOIN conn channel)))

(defun irc-handle-auto-join--rpl-hosthidden (conn _event _sender _target _host
                                                  _description)
  (dolist (channel (irc-connection-get conn :auto-join-after-host-hiding))
    (irc-send-JOIN conn channel)))

(defun irc-handle-auto-join--nickserv-regained (conn _event)
  (dolist (channel (irc-connection-get
                    conn :auto-join-after-nick-acquisition))
    (irc-send-JOIN conn channel)))

(defun irc-handle-auto-join--nickserv-identified (conn event)
  (dolist (channel (irc-connection-get
                    conn :auto-join-after-nickserv-identification))
    (irc-send-JOIN conn channel))
  (if (irc-string-equal-p conn
                          (irc-connection-get conn :nick)
                          (irc-connection-get conn :nickserv-nick))
      (irc-handle-auto-join--nickserv-regained conn event)))

(defun irc-handle-auto-join--sasl-login (conn _event &rest ignored)
  (dolist (channel (irc-connection-get
                    conn :auto-join-after-sasl-login))
    (irc-send-JOIN conn channel)))

(provide 'irc)
;;; irc.el ends here
