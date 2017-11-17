;;; circe.el --- Client for IRC in Emacs -*- lexical-binding: t -*-

;; Copyright (C) 2005 - 2015  Jorgen Schaefer

;; Version: 2.6
;; Keywords: IRC, chat
;; Author: Jorgen Schaefer <forcer@forcix.cx>
;; URL: https://github.com/jorgenschaefer/circe

;; This file is part of Circe.

;; This program is free software: you can redistribute it and/or modify
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

;; Circe is a Client for IRC in Emacs. It integrates well with the rest
;; of the editor, using standard Emacs key bindings and indicating
;; activity in channels in the status bar so it stays out of your way
;; unless you want to use it.

;;; Code:

(defvar circe-version "2.6"
  "Circe version string.")

(require 'circe-compat)

(require 'ring)
(require 'timer)
(require 'lui)
(require 'lui-format)
(require 'lcs)
(require 'irc)

;; Used to be optional. But sorry, we're in the 21st century already.
(require 'lui-irc-colors)

;; necessary for inheriting from diff-added and diff-removed faces
(require 'diff-mode)

(defgroup circe nil
  "Yet Another Emacs IRC Client."
  :prefix "circe-"
  :group 'applications)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Customization Options ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;
;;;; Faces ;;;;
;;;;;;;;;;;;;;;

(defface circe-prompt-face
  '((t (:weight bold :foreground "Black" :background "LightSeaGreen")))
  "The face for the Circe prompt."
  :group 'circe)

(defface circe-server-face
  '((((type tty)) (:foreground "blue" :weight bold))
    (((background dark)) (:foreground "#5095cf"))
    (((background light)) (:foreground "#3840b0"))
    (t (:foreground "SteelBlue")))
  "The face used to highlight server messages."
  :group 'circe)

(defface circe-highlight-nick-face
  '((default (:weight bold))
    (((type tty)) (:foreground "cyan"))
    (((background dark)) (:foreground "#82e2ed"))
    (((background light)) (:foreground "#0445b7"))
    (t (:foreground "CadetBlue3")))
  "The face used to highlight messages directed to us."
  :group 'circe)

(defface circe-my-message-face '((t))
  "The face used to highlight our own messages."
  :group 'circe)

(defface circe-originator-face '((t))
  "The face used to highlight the originator of a message."
  :group 'circe)

(defface circe-topic-diff-new-face '((t (:inherit diff-added)))
  "The face used for text added to a topic.
See the {topic-diff} parameter to `circe-format-server-topic'."
  :group 'circe)

(defface circe-topic-diff-removed-face '((t (:inherit diff-removed)))
  "The face used for text removed from a topic.
See the {topic-diff} parameter to `circe-format-server-topic'."
  :group 'circe)

(defface circe-fool-face
  '((((type tty)) (:foreground "grey40" :bold t))
    (t (:foreground "grey40")))
  "The face used for fools.
See `circe-fool-list'."
  :group 'circe)

;;;;;;;;;;;;;;;;;;;
;;;; Variables ;;;;
;;;;;;;;;;;;;;;;;;;

(defcustom circe-default-nick (user-login-name)
  "The default nick for circe."
  :type 'string
  :group 'circe)

(defcustom circe-default-user circe-default-nick
  "The default user name for circe."
  :type 'string
  :group 'circe)

(defcustom circe-default-realname (if (string= (user-full-name) "")
                                      circe-default-nick
                                    (user-full-name))
  "The default real name for circe."
  :type 'string
  :group 'circe)

(defcustom circe-default-ip-family nil
  "Default IP family to use.

  'nil  - Use either IPv4 or IPv6.

  'ipv4 - Use IPv4

  'ipv6 - Use IPv6"
  :type '(choice (const :tag "Both" nil)
                 (const :tag "IPv4" ipv4)
                 (const :tag "IPv6" ipv6))
  :group 'circe)

(defcustom circe-default-directory "~/"
  "The value of `default-directory' for Circe buffers."
  :type 'string
  :group 'circe)

(defcustom circe-network-options nil
  "Network options.

This alist maps network names to respective options.

Common options:

  :pass - The IRC server password to use for this network, or a
          function to fetch it.
  :nick - The nick name to use (defaults to `circe-default-nick')
  :user - The user name to use (defaults to `circe-default-user')
  :realname - The real name to use (defaults to `circe-default-realname')

  :channels - A plist of channels to join (see `circe-channels').
  :server-buffer-name - Format to be used for the server buffer name
                        (see `circe-server-buffer-name')

  :host - The host name of the server to connect to.
  :port - The port or service name for the server.
  :use-tls - A boolean indicating as to whether to use TLS or
             not (defaults to nil). If you set this, you'll likely
             have to set :port as well.
  :ip-family - Option to enforce a specific IP version
               (defaults to `circe-default-ip-family')

  :nickserv-nick - The nick to authenticate with to nickserv, if configured.
                   (defaults to the value of :nick)
  :nickserv-password - The password to use for nickserv
                       authentication or a function to fetch it.

  :sasl-username - The username for SASL authentication.
  :sasl-password - The password for SASL authentication."
  :type '(alist :key-type string :value-type plist)
  :group 'circe)

(defvar circe-network-defaults
  '(("Freenode" :host "irc.freenode.net" :port (6667 . 6697)
     :tls t
     :nickserv-mask "^NickServ!NickServ@services\\.$"
     :nickserv-identify-challenge "\C-b/msg\\s-NickServ\\s-identify\\s-<password>\C-b"
     :nickserv-identify-command "PRIVMSG NickServ :IDENTIFY {nick} {password}"
     :nickserv-identify-confirmation "^You are now identified for .*\\.$"
     :nickserv-ghost-command "PRIVMSG NickServ :GHOST {nick} {password}"
     :nickserv-ghost-confirmation "has been ghosted\\.$\\|is not online\\.$"
     )
    ("Coldfront" :host "irc.coldfront.net" :port 6667
     :nickserv-mask "^NickServ!services@coldfront\\.net$"
     :nickserv-identify-challenge "/msg\\s-NickServ\\s-IDENTIFY\\s-\C-_password\C-_"
     :nickserv-identify-command "PRIVMSG NickServ :IDENTIFY {password}"
     )
    ("Bitlbee" :host "localhost" :port 6667
     :nickserv-mask "\\(bitlbee\\|root\\)!\\(bitlbee\\|root\\)@"
     :nickserv-identify-challenge "use the \x02identify\x02 command to identify yourself"
     :nickserv-identify-command "PRIVMSG &bitlbee :identify {password}"
     :nickserv-identify-confirmation "Password accepted, settings and accounts loaded"
     :lagmon-disabled t
     )
    ("OFTC" :host "irc.oftc.net" :port (6667 . 6697)
     :nickserv-mask "^NickServ!services@services\\.oftc\\.net$"
     :nickserv-identify-challenge "This nickname is registered and protected."
     :nickserv-identify-command "PRIVMSG NickServ :IDENTIFY {password} {nick}"
     :nickserv-identify-confirmation "^You are successfully identified as .*\\.$"
     )
    )
  "Alist of networks and connection settings.

See the `circe' command for details of this variable.")

(defcustom circe-default-quit-message "Using Circe, the loveliest of all IRC clients"
  "The default quit message when no other is given.

This is sent when the server buffer is killed or when /QUIT is
given with no argument."
  :type 'string
  :group 'circe)

(defcustom circe-default-part-message "Using Circe, the loveliest of all IRC clients"
  "How to part when a channel buffer is killed, or when no
argument is given to /PART."
  :type 'string
  :group 'circe)

(defcustom circe-auto-query-max 23
  "The maximum number of queries which are opened automatically.
If more messages arrive - typically in a flood situation - they
are displayed in the server buffer."
  :type 'integer
  :group 'circe)

(defcustom circe-use-cycle-completion nil
  "Whether Circe should use cycle completion.

If this is not nil, Circe will set `completion-cycle-threshold'
to t locally in Circe buffers, enabling cycle completion for
nicks no matter what completion style you use in the rest of
Emacs. If you set this to nil, Circe will not touch your default
completion style."
  :type 'boolean
  :group 'circe)

(defcustom circe-reduce-lurker-spam nil
  "If enabled, Circe will stop showing some messages.

This means that JOIN, PART, QUIT and NICK messages are not shown
for users on channels that have not spoken yet (\"lurker\"), or
haven't spoken in `circe-active-users-timeout' seconds. When they
speak for the first time, Circe displays their join time."
  :type 'boolean
  :group 'circe)

(defcustom circe-active-users-timeout nil
  "When non-nil, should be the number of seconds after which
active users are regarded as inactive again after speaking."
  :type 'integer
  :group 'circe)

(defcustom circe-prompt-string (concat (propertize ">"
                                                   'face 'circe-prompt-face)
                                       " ")
  "The string to initialize the prompt with.
To change the prompt dynamically or just in specific buffers, use
`lui-set-prompt' in the appropriate hooks."
  :type 'string
  :group 'circe)

(defcustom circe-extra-nicks nil
  "List of other nicks than your current one to highlight."
  :type '(repeat string)
  :group 'circe)

(defcustom circe-highlight-nick-type 'sender
  "How to highlight occurrences of our own nick.

  'sender     - Highlight the nick of the sender
                (messages without a sender and your
                own are highlighted with the occurrence
                type instead)
  'occurrence - Highlight the occurrences of the nick
  'message    - Highlight the message without the sender
  'all        - Highlight the whole line"
  :type '(choice (const :tag "Sender" sender)
                 (const :tag "Occurrences" occurrence)
                 (const :tag "Message" message)
                 (const :tag "Whole line" all))
  :group 'circe)

(defcustom circe-inhibit-nick-highlight-function nil
  "Function for inhibiting nick highlighting.
If non-nil, its value is called with the respective buffer
selected and point in the line that's about to get highlighted.
A non-nil return value inhibits any highlighting."
  :type '(choice (const :tag "None" nil)
                 function)
  :group 'circe)

(defcustom circe-completion-suffix ": "
  "A suffix for completed nicks at the beginning of a line."
  :type '(choice (const :tag "The standard suffix" ": "))
  :group 'circe)

(defcustom circe-ignore-list nil
  "List of regular expressions to ignore.

Each regular expression is matched against nick!user@host."
  :type '(repeat regexp)
  :group 'circe)

(defcustom circe-fool-list nil
  "List of regular expressions for fools.

Each regular expression is matched against nick!user@host.

Messages from such people are still inserted, but not shown. They
can be displayed using \\[lui-toggle-ignored]."
  :type '(repeat regexp)
  :group 'circe)

(defcustom circe-ignore-functions nil
  "A list of functions to check whether we should ignore a message.

These functions get three arguments: NICK, USERHOST, and BODY. If
one of them returns a non-nil value, the message is ignored."
  :type 'hook
  :group 'circe)

(defcustom circe-split-line-length 440
  "The maximum length of a single message.
If a message exceeds this size, it is broken into multiple ones.

IRC allows for lines up to 512 bytes. Two of them are CR LF.
And a typical message looks like this:

  :nicky!uhuser@host212223.dialin.fnordisp.net PRIVMSG #lazybastards :Hello!

You can limit here the maximum length of the \"Hello!\" part.
Good luck."
  :type 'integer
  :group 'circe)

(defcustom circe-server-max-reconnect-attempts 5
  "How often Circe should attempt to reconnect to the server.
If this is 0, Circe will not reconnect at all. If this is nil,
it will try to reconnect forever (not recommended)."
  :type '(choice integer
                 (const :tag "Forever" nil))
  :group 'circe)

(defcustom circe-netsplit-delay 60
  "The number of seconds a netsplit may be dormant.
If anything happens with a netsplit after this amount of time,
the user is re-notified."
  :type 'number
  :group 'circe)

(defcustom circe-server-killed-confirmation 'ask-and-kill-all
  "How to ask for confirmation when a server buffer is killed.
This can be one of the following values:
  ask - Ask the user for confirmation
  ask-and-kill-all - Ask the user, and kill all associated buffers
  kill-all - Don't ask the user, and kill all associated buffers
  nil - Kill first, ask never"
  :type '(choice (const :tag "Ask before killing" ask)
                 (const :tag "Ask, then kill all associated buffers"
                        ask-and-kill-all)
                 (const :tag "Don't ask, then kill all associated buffers"
                        kill-all)
                 (const :tag "Don't ask" nil))
  :group 'circe)

(defcustom circe-channel-killed-confirmation 'ask
  "How to ask for confirmation when a channel buffer is killed.
This can be one of the following values:
  ask - Ask the user for confirmation
  nil - Don't ask, just kill"
  :type '(choice (const :tag "Ask before killing" ask)
                 (const :tag "Don't ask" nil))
  :group 'circe)

(defcustom circe-track-faces-priorities '(circe-highlight-nick-face
                                          lui-highlight-face
                                          circe-my-message-face
                                          circe-server-face)
  "A list of faces which should show up in the tracking.
The first face is kept if the new message has only lower faces,
or faces that don't show up at all."
  :type '(repeat face)
  :group 'circe)

(defcustom circe-server-send-unknown-command-p nil
  "Non-nil when Circe should just pass on commands it doesn't know.
E.g. /fnord foo bar would then just send \"fnord foo bar\" to the
server."
  :type 'boolean
  :group 'circe)

(defcustom circe-server-connected-hook nil
  "Hook run when we successfully connected to a server.
This is run from a 001 (RPL_WELCOME) message handler."
  :type 'hook
  :group 'circe)

(defcustom circe-server-auto-join-default-type :immediate
  "The default auto-join type to use.

Possible options:

:immediate - Immediately after registering on the server
:after-auth - After nickserv authentication succeeded
:after-cloak - After we have acquired a cloaked host name
:after-nick - After we regained our preferred nick, or after
              nickserv authentication if we don't need to regain
              it. See `circe-nickserv-ghost-style'.

See `circe-channels' for more details."
  :type '(choice (const :tag "Immediately" :immediate)
                 (const :tag "After Authentication" :after-auth)
                 (const :tag "After Cloaking" :after-cloak)
                 (const :tag "After Nick Regain" :after-nick))
  :group 'circe)

;;;;;;;;;;;;;;;;;
;;;; Formats ;;;;
;;;;;;;;;;;;;;;;;

(defgroup circe-format nil
  "Format strings for Circe.
All these formats always allow the {mynick} and {chattarget} format
strings."
  :prefix "circe-format-"
  :group 'circe)

(defcustom circe-format-not-tracked
  '(circe-format-server-message
    circe-format-server-notice
    circe--irc-format-server-numeric
    circe-format-server-topic
    circe-format-server-rejoin
    circe-format-server-lurker-activity
    circe-format-server-topic-time
    circe-format-server-topic-time-for-channel
    circe-format-server-netmerge
    circe-format-server-join
    circe-format-server-join-in-channel
    circe-format-server-mode-change
    circe-format-server-nick-change-self
    circe-format-server-nick-change
    circe-format-server-nick-regain
    circe-format-server-part
    circe-format-server-netsplit
    circe-format-server-quit-channel
    circe-format-server-quit)
  "A list of formats that should not trigger tracking."
  :type '(repeat symbol)
  :group 'circe-format)

(defcustom circe-format-server-message "*** {body}"
  "The format for generic server messages.
{body} - The body of the message."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-self-say "> {body}"
  "The format for messages to queries or channels.
{nick} - Your nick.
{body} - The body of the message."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-self-action "* {nick} {body}"
  "The format for actions to queries or channels.
{nick} - Your nick.
{body} - The body of the action."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-self-message "-> *{chattarget}* {body}"
  "The format for messages sent to other people outside of queries.
{chattarget} - The target nick.
{body} - The body of the message."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-action "* {nick} {body}"
  "The format for actions in queries or channels.
{nick} - The nick doing the action.
{body} - The body of the action."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-message-action "* *{nick}* {body}"
  "The format for actions in messages outside of queries.
{nick} - The nick doing the action.
{body} - The body of the action."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-say "<{nick}> {body}"
  "The format for normal channel or query talk.
{nick} - The nick talking.
{body} - The message."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-message "*{nick}* {body}"
  "The format for a message outside of a query.
{nick} - The originator.
{body} - The message."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-notice "-{nick}- {body}"
  "The format for a notice.
{nick} - The originator.
{body} - The notice."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-notice "-Server Notice- {body}"
  "The format for a server notice.
{body} - The notice."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-topic "*** Topic change by {nick} ({userhost}): {new-topic}"
  "The format for topic changes.

The following format arguments are available:

  nick       - The nick of the user who changed the topic
  userhost   - The user@host string of that user
  channel    - Where the topic change happened
  new-topic  - The new topic
  old-topic  - The previous topic
  topic-diff - A colorized diff of the topics"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-lurker-activity
  "*** First activity: {nick} joined {joindelta} ago."
  "The format for the first-activity notice of a user.
{nick} - The originator.
{jointime} - The join time of the user (in seconds).
{joindelta} - The duration from joining until now."
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-rejoin
  "*** Re-join: {nick} ({userinfo}), left {departuredelta} ago"
  "The format for the re-join notice of a user.

The following format arguments are available:

  nick           - The nick of the user who joined
  userhost       - The user@host string of the user who joined
  accountname    - The account name, if the server supports this
  realname       - The real name, if the server supports this
  userinfo       - A combination of userhost, accountname, and realname
  channel        - A date string describing this time
  departuretime  - Time in seconds when the originator had left.
  departuredelta - Description of the time delta since the originator left."
  :type 'string
  :group 'circe-format)

(defcustom circe-server-buffer-name "{host}:{port}"
  "The format for the server buffer name.

The following format arguments are available:

  network  - The name of the network
  host     - The host name of the server
  port     - The port number or service name
  service  - Alias for port"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-whois-idle-with-signon "*** {whois-nick} is {idle-duration} idle (signon on {signon-date}, {signon-ago} ago)"
  "Format for RPL_WHOISIDLE messages.

The following format arguments are available:

  whois-nick      - The nick this is about
  idle-seconds    - The number of seconds this nick has been idle
  idle-duration   - A textual description of the duration of the idle time
  signon-time     - The time (in seconds since the epoch) when this user
                    signed on
  signon-date     - A date string describing this time
  signon-ago      - A textual description of the duraction since signon"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-whois-idle "*** {whois-nick} is {idle-duration} idle"
  "Format for RPL_WHOISIDLE messages.

The following format arguments are available:

  whois-nick      - The nick this is about
  idle-seconds    - The number of seconds this nick has been idle
  idle-duration   - A textual description of the duration of the idle time"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-topic-time "*** Topic set by {setter} on {topic-date}, {topic-ago} ago"
  "Format for RPL_TOPICWHOTIME messages for the current channel.

The following format arguments are available:

  channel         - The channel the topic is for
  setter          - The nick of the person who set the topic
  setter-userhost - The user@host string of the person who set the topic
  topic-time      - The time the topic was set, in seconds since the epoch
  topic-date      - A date string describing this time
  topic-ago       - A textual description of the duration since the topic
                    was set"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-topic-time-for-channel "*** Topic for {channel} set by {setter} on {topic-date}, {topic-ago} ago"
  "Format for RPL_TOPICWHOTIME messages for a channel we are not on.

The following format arguments are available:

  channel         - The channel the topic is for
  setter          - The nick of the person who set the topic
  setter-userhost - The user@host string of the person who set the topic
  topic-time      - The time the topic was set, in seconds since the epoch
  topic-date      - A date string describing this time
  topic-ago       - A textual description of the duration since the topic
                    was set"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-channel-creation-time "*** Channel {channel} created on {date}, {ago} ago"
  "Format for RPL_CREATIONTIME messages for the current channel.

The following format arguments are available:

  channel  - The channel the topic is for
  date     - A date string describing this time
  ago      - A textual description of the duration since the channel
             was created"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-ctcp-ping "*** CTCP PING request from {nick} ({userhost}) to {target}: {body} ({ago} ago)"
  "Format for CTCP PING requests.

The following format arguments are available:

  nick      - The nick of the user who sent this PING request
  userhost  - The user@host string of the user who sent this request
  target    - The target of the message, usually us, but can be a channel
  body      - The argument of the PING request, usually a number
  ago       - A textual description of the duration since the request
              was sent, if parseable"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-ctcp-ping-reply "*** CTCP PING reply from {nick} ({userhost}) to {target}: {ago} ago ({body})"
  "Format for CTCP PING replies.

The following format arguments are available:

  nick      - The nick of the user who sent this PING request
  userhost  - The user@host string of the user who sent this request
  target    - The target of the message, usually us, but can be a channel
  body      - The argument of the PING request, usually a number
  ago       - A textual description of the duration since the request
              was sent, if parseable"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-ctcp "*** CTCP {command} request from {nick} ({userhost}) to {target}: {body}"
  "Format for CTCP requests.

The following format arguments are available:

  nick      - The nick of the user who sent this PING request
  userhost  - The user@host string of the user who sent this request
  target    - The target of the message, usually us, but can be a channel
  command   - The CTCP command used
  body      - The argument of the PING request, usually a number"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-netsplit "*** Netsplit: {split} (Use /WL to see who left)"
  "Format for netsplit notifications.

The following format arguments are available:

  split   - The name of the split, usually describing the servers involved"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-netmerge "*** Netmerge: {split}, split {ago} ago (Use /WL to see who's still missing)"
  "Format for netmerge notifications.

The following format arguments are available:

  split   - The name of the split, usually describing the servers involved
  time    - The time when this split happened, in seconds
  date    - A date string describing this time
  ago     - A textual description of the duration since the split happened"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-join "*** Join: {nick} ({userinfo})"
  "Format for join messages in a channel buffer.

The following format arguments are available:

  nick         - The nick of the user joining
  userhost     - The user@host string for the user
  accountname  - The account name, if the server supports this
  realname     - The real name, if the server supports this
  userinfo     - A combination of userhost, accountname, and realname
  channel      - The channel this user is joining"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-join-in-channel "*** Join: {nick} ({userinfo}) joined {channel}"
  "Format for join messages in query buffers of the joining user.

The following format arguments are available:

  nick         - The nick of the user joining
  userhost     - The user@host string for the user
  accountname  - The account name, if the server supports this
  realname     - The real name, if the server supports this
  userinfo     - A combination of userhost, accountname, and realname
  channel      - The channel this user is joining"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-mode-change "*** Mode change: {change} on {target} by {setter} ({userhost})"
  "Format for mode changes.

The following format arguments are available:

  setter       - The name of the split, usually describing the servers involved
  userhost     - The user@host string for the user
  target       - The target of this mode change
  change       - The actual changed modes"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-nick-change-self "*** Nick change: You are now known as {new-nick}"
  "Format for nick changes of the current user.

The following format arguments are available:

  old-nick - The old nick this change was from
  new-nick - The new nick this change was to
  userhost - The user@host string for the user"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-nick-change "*** Nick change: {old-nick} ({userhost}) is now known as {new-nick}"
  "Format for nick changes of the current user.

The following format arguments are available:

  old-nick - The old nick this change was from
  new-nick - The new nick this change was to
  userhost - The user@host string for the user"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-nick-regain "*** Nick regain: {old-nick} ({userhost}) is now known as {new-nick}"
  "Format for nick changes of the current user.

The following format arguments are available:

  old-nick - The old nick this change was from
  new-nick - The new nick this change was to
  userhost - The user@host string for the user"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-part "*** Part: {nick} ({userhost}) left {channel}: {reason}"
  "Format for users parting a channel.

The following format arguments are available:

  nick     - The nick of the user who left
  userhost - The user@host string for this user
  channel  - The channel they left
  reason   - The reason they gave for leaving"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-quit-channel "*** Quit: {nick} ({userhost}) left {channel}: {reason}"
  "Format for users quitting from a channel.

The following format arguments are available:

  nick     - The nick of the user who left
  userhost - The user@host string for this user
  channel  - The channel they left
  reason   - The reason they gave for leaving"
  :type 'string
  :group 'circe-format)

(defcustom circe-format-server-quit "*** Quit: {nick} ({userhost}) left IRC: {reason}"
  "Format for users quitting.

The following format arguments are available:

  nick     - The nick of the user who left
  userhost - The user@host string for this user
  reason   - The reason they gave for leaving"
  :type 'string
  :group 'circe-format)

;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Private variables ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar circe-source-url "https://github.com/jorgenschaefer/circe"
  "URL to Circe's source repository")

(defvar circe-host nil
  "The name of the server we're currently connected to.")
(make-variable-buffer-local 'circe-host)

(defvar circe-port nil
  "The port number or service name of the server.")
(make-variable-buffer-local 'circe-host)

(defvar circe-network nil
  "The network name of the server we're currently connected to.")
(make-variable-buffer-local 'circe-network)

(defvar circe-ip-family nil
  "The IP family in use.
See `make-network-process' and :family for valid values.")
(make-variable-buffer-local 'circe-ip-family)

(defvar circe-nick nil
  "Our current nick.")
(make-variable-buffer-local 'circe-nick)

(defvar circe-user nil
  "The current user name.")
(make-variable-buffer-local 'circe-user)

(defvar circe-realname nil
  "The current real name.")
(make-variable-buffer-local 'circe-realname)

(defvar circe-pass nil
  "The password for the current server or a function to recall it.

If a function is set it will be called with the value of `circe-host'.")
(make-variable-buffer-local 'circe-pass)

(defvar circe-sasl-username nil
  "The username for SASL authentication.")
(make-variable-buffer-local 'circe-sasl-username)

(defvar circe-sasl-password nil
  "The password for SASL authentication.

If a function is set it will be called with the value of
`circe-host'.")
(make-variable-buffer-local 'circe-sasl-password)

(defvar circe-use-tls nil
  "If non-nil, use `open-tls-stream' to connect to the server.")
(make-variable-buffer-local 'circe-use-tls)

(defvar circe-server-process nil
  "The process of the server connection.")
(make-variable-buffer-local 'circe-server-process)

(defvar circe-server-last-active-buffer nil
  "The last active circe buffer.")
(make-variable-buffer-local 'circe-server-last-active-buffer)

(defvar circe-display-table nil
  "A hash table mapping commands to their display functions.")

(defvar circe-server-inhibit-auto-reconnect-p nil
  "Non-nil when Circe should not reconnect.

This can be set from commands to avoid reconnecting when the
server disconnects.")
(make-variable-buffer-local 'circe-server-inhibit-auto-reconnect-p)

(defvar circe-chat-calling-server-buffer-and-target nil
  "Internal variable to pass the server buffer and target to chat modes.")

(defvar circe-chat-target nil
  "The current target for the buffer.
This is either a channel or a nick name.")
(make-variable-buffer-local 'circe-chat-target)

(defvar circe-nick-syntax-table
  (let ((table (make-syntax-table text-mode-syntax-table))
        (special (string-to-list "[]\`_^{}|-")))
    (dolist (char special)
      (modify-syntax-entry char "w" table))
    table)
  "Syntax table to treat nicks as words.
This is not entirely accurate, as exact chars constituting a nick
can vary between networks.")

(defvar circe-nickserv-mask nil
  "The regular expression to identify the nickserv on this network.

Matched against nick!user@host.")
(make-variable-buffer-local 'circe-nickserv-mask)

(defvar circe-nickserv-identify-challenge nil
  "A regular expression matching the nickserv challenge to identify.")
(make-variable-buffer-local 'circe-nickserv-identify-challenge)

(defvar circe-nickserv-identify-command nil
  "The IRC command to send to identify with nickserv.

This must be a full IRC command. It accepts the following
formatting options:

 {nick} - The nick to identify as
 {password} - The configured nickserv password")
(make-variable-buffer-local 'circe-nickserv-identify-command)

(defvar circe-nickserv-identify-confirmation nil
  "A regular expression matching a confirmation of authentication.")
(make-variable-buffer-local 'circe-nickserv-identify-confirmation)

(defvar circe-nickserv-ghost-command nil
  "The IRC command to send to regain/ghost your nick.

This must be a full IRC command. It accepts the following
formatting options:

  {nick} - The nick to ghost
  {password} - The configured nickserv password")
(make-variable-buffer-local 'circe-nickserv-ghost-command)

(defvar circe-nickserv-ghost-confirmation nil
  "A regular expression matching a confirmation for the GHOST command.

This is used to know when we can set our nick to the regained one
Leave nil if regaining automatically sets your nick")
(make-variable-buffer-local 'circe-nickserv-ghost-confirmation)

(defvar circe-nickserv-nick nil
  "The nick we are registered with for nickserv.

Do not set this variable directly. Use `circe-network-options' or
pass an argument to the `circe' function for this.")
(make-variable-buffer-local 'circe-nickserv-nick)

(defvar circe-nickserv-password nil
  "The password we use for nickserv on this network.

Can be either a string or a unary function of the nick returning
a string.

Do not set this variable directly. Use `circe-network-options' or
pass an argument to the `circe' function for this.")
(make-variable-buffer-local 'circe-nickserv-password)

(defvar circe-channels nil
  "The default channels to join on this server.

Don't set this variable by hand, use `circe-network-options'.

The value should be a list of channels to join, with optional
keywords to configure the behavior of the following channels.

Best explained in an example:

\(\"#emacs\" :after-auth \"#channel\" \"#channel2\")

Possible keyword options are:

:immediate - Immediately after registering on the server
:after-auth - After nickserv authentication succeeded
:after-cloak - After we have acquired a cloaked host name
:after-nick - After we regained our preferred nick, or after
              nickserv authentication if we don't need to regain
              it. See `circe-nickserv-ghost-style'.

The default is set in `circe-server-auto-join-default-type'.

A keyword in the first position of the channels list overrides
`circe-server-auto-join-default-type' for re-joining manually
joined channels.")
(make-variable-buffer-local 'circe-channels)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Server Buffer Management ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every Circe buffer has an associated server buffer (which might be
;; the buffer itself). Circe buffers should set the
;; `circe-server-buffer' variable to the associated server buffer.

(defun circe-server-buffer ()
  "Return the server buffer for the current buffer."
  (let ((buf (if (eq major-mode 'circe-server-mode)
                 (current-buffer)
               circe-server-buffer)))
    (cond
     ((not buf)
      (error "Not in a Circe buffer"))
     ((not (buffer-live-p buf))
      (error "The server buffer died, functionality is limited"))
     (t
      buf))))

(defmacro with-circe-server-buffer (&rest body)
  "Run BODY with the current buffer being the current server buffer."
  (declare (indent 0))
  `(with-current-buffer (circe-server-buffer)
     ,@body))

;;;;;;;;;;;;;;;;;;;;;;;
;;; Editor Commands ;;;
;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defun circe-version ()
  "Display Circe's version."
  (interactive)
  (message "Circe %s" (circe--version)))

(defun circe--version ()
  "Return Circe's version"
  (let ((circe-git-version (circe--git-version)))
    (if circe-git-version
        (format "%s-%s" circe-version circe-git-version)
      (format "%s" circe-version))))

(defun circe--git-version ()
  (let ((current-file-path (or load-file-name buffer-file-name)))
    (when (or (not current-file-path)
              (not (equal (file-name-nondirectory current-file-path)
                          "circe.el")))
      (setq current-file-path (locate-library "circe.el")))
    (let ((vcs-path (locate-dominating-file current-file-path ".git")))
      (when vcs-path
        (let ((default-directory vcs-path))
          ;; chop off the trailing newline
          (substring (shell-command-to-string "git rev-parse --short HEAD")
                     0 -1))))))

;;;###autoload
(defun circe (network-or-server &rest server-options)
  "Connect to IRC.

Connect to the given network specified by NETWORK-OR-SERVER.

When this function is called, it collects options from the
SERVER-OPTIONS argument, the user variable
`circe-network-options', and the defaults found in
`circe-network-defaults', in this order.

If NETWORK-OR-SERVER is not found in any of these variables, the
argument is assumed to be the host name for the server, and all
relevant settings must be passed via SERVER-OPTIONS.

All SERVER-OPTIONS are treated as variables by getting the string
\"circe-\" prepended to their name. This variable is then set
locally in the server buffer.

See `circe-network-options' for a list of common options."
  (interactive (circe--read-network-and-options))
  (let* ((options (circe--server-get-network-options network-or-server
                                                     server-options))
         (buffer (circe--server-generate-buffer options)))
    (with-current-buffer buffer
      (circe-server-mode)
      (circe--server-set-variables options)
      (circe-reconnect))
    (pop-to-buffer-same-window buffer)))

(defun circe--read-network-and-options ()
  "Read a host or network name with completion.

If it's not a network, also read some extra options.

This uses `circe-network-defaults' and `circe-network-options' for
network names."
  (let ((default-network (if (null circe-network-options)
                             (caar circe-network-defaults)
                           (caar circe-network-options)))
        (networks nil)
        (completion-ignore-case t)
        network-or-host)
    (dolist (network-spec (append circe-network-options
                                  circe-network-defaults))
      (when (not (member (car network-spec) networks))
        (push (car network-spec) networks)))
    (setq networks (sort networks 'string-lessp))
    (setq network-or-host (completing-read "Network or host: "
                                           networks
                                           nil nil nil nil
                                           default-network))
    (dolist (network-name networks)
      (when (equal (downcase network-or-host)
                   (downcase network-name))
        (setq network-or-host network-name)))
    (if (member network-or-host networks)
        (list network-or-host)
      (list network-or-host
            :host network-or-host
            :port (read-number "Port: " 6667)))))

(defun circe--server-get-network-options (network server-options)
  "Combine server and network options with network defaults.

See `circe-network-options' and `circe-network-defaults'."
  (let ((options (mapcar 'circe--translate-option-names
                         (append server-options
                                 (cdr (assoc network circe-network-options))
                                 (cdr (assoc network circe-network-defaults))
                                 (list :network network)))))
    (when (not (plist-get options :host))
      (plist-put options :host network))
    (let ((port (plist-get options :port))
          (use-tls (plist-get options :use-tls)))
      (when (consp port)
        (if use-tls
            (plist-put options :port (cdr port))
          (plist-put options :port (car port)))))
    (dolist (required-option '(:host :port))
      (when (not (plist-get options required-option))
        (error (format "Network option %s not specified" required-option))))
    options))

(defun circe--translate-option-names (option)
  "Translate option names to make them unique.

Some options have multiple names, mainly for historical reasons.
Unify them here."
  (cond
   ((eq option :service) :port)
   ((eq option :tls) :use-tls)
   ((eq option :family) :ip-family)
   (t option)))

(defun circe--server-generate-buffer (options)
  "Return the server buffer for the connection described in OPTIONS."
  (let* ((network (plist-get options :network))
         (host (plist-get options :host))
         (port (plist-get options :port))
         (buffer-name (lui-format (or (plist-get options :server-buffer-name)
                                      circe-server-buffer-name)
                                  :network network
                                  :host host
                                  :port port
                                  :service port)))
    (generate-new-buffer buffer-name)))

(defun circe--server-set-variables (options)
  "Set buffer-local variables described in OPTIONS.

OPTIONS is a plist as passed to `circe'. All options therein are
set as buffer-local variables. Only the first occurrence of each
variable is set."
  (setq circe-nick circe-default-nick
        circe-user circe-default-user
        circe-realname circe-default-realname
        circe-ip-family circe-default-ip-family)
  (let ((done nil)
        (todo options))
    (while todo
      (when (not (memq (car todo) done))
        (push (car todo) done)
        (let ((var (intern (format "circe-%s"
                                   (substring (symbol-name (car todo)) 1))))
              (val (cadr todo)))
          (if (boundp var)
              (set (make-local-variable var) val)
            (warn "Unknown option %s, ignored" (car todo)))))
      (setq todo (cddr todo)))))

(defvar circe-server-reconnect-attempts 0
  "The number of reconnect attempts that Circe has done so far.
See `circe-server-max-reconnect-attempts'.")
(make-variable-buffer-local 'circe-server-reconnect-attempts)

(defun circe-reconnect ()
  "Reconnect the current server."
  (interactive)
  (with-circe-server-buffer
    (when (or (called-interactively-p 'any)
              (circe--reconnect-p))
      (setq circe-server-inhibit-auto-reconnect-p t
            circe-server-reconnect-attempts (+ circe-server-reconnect-attempts
                                               1))
      (unwind-protect
          (circe-reconnect--internal)
        (setq circe-server-inhibit-auto-reconnect-p nil)))))

(defun circe--reconnect-p ()
  (cond
   (circe-server-inhibit-auto-reconnect-p
    nil)
   ((not circe-server-max-reconnect-attempts)
    t)
   ((<= circe-server-reconnect-attempts
        circe-server-max-reconnect-attempts)
    t)
   (t
    nil)))

(defun circe-reconnect--internal ()
  "The internal function called for reconnecting unconditionally.

Do not use this directly, use `circe-reconnect'"
  (when (and circe-server-process
             (process-live-p circe-server-process))
    (delete-process circe-server-process))
  (circe-display-server-message "Connecting...")
  (dolist (buf (circe-server-chat-buffers))
    (with-current-buffer buf
      (circe-display-server-message "Connecting...")))
  (setq circe-server-process
        (irc-connect
         :host circe-host
         :service circe-port
         :tls circe-use-tls
         :ip-family circe-ip-family
         :handler-table (circe-irc-handler-table)
         :server-buffer (current-buffer)
         :nick circe-nick
         :nick-alternatives (list (circe--nick-next circe-nick)
                                  (circe--nick-next
                                   (circe--nick-next circe-nick)))
         :user circe-user
         :mode 8
         :realname circe-realname
         :pass (if (functionp circe-pass)
                   (funcall circe-pass circe-host)
                 circe-pass)
         :cap-req (append (when (and circe-sasl-username
                                     circe-sasl-password)
                            '("sasl"))
                          '("extended-join"))
         :nickserv-nick (or circe-nickserv-nick
                            circe-nick)
         :nickserv-password (if (functionp circe-nickserv-password)
                                (funcall circe-nickserv-password circe-host)
                              circe-nickserv-password)
         :nickserv-mask circe-nickserv-mask
         :nickserv-identify-challenge circe-nickserv-identify-challenge
         :nickserv-identify-command circe-nickserv-identify-command
         :nickserv-identify-confirmation
         circe-nickserv-identify-confirmation
         :nickserv-ghost-command circe-nickserv-ghost-command
         :nickserv-ghost-confirmation circe-nickserv-ghost-confirmation
         :sasl-username circe-sasl-username
         :sasl-password (if (functionp circe-sasl-password)
                            (funcall circe-sasl-password
                                     circe-host)
                          circe-sasl-password)
         :ctcp-version (format "Circe: Client for IRC in Emacs, version %s"
                               circe-version)
         :ctcp-source circe-source-url
         :ctcp-clientinfo "CLIENTINFO PING SOURCE TIME VERSION"
         :auto-join-after-registration
         (append (circe--auto-join-channel-buffers)
                 (circe--auto-join-list :immediate))
         :auto-join-after-host-hiding
         (circe--auto-join-list :after-cloak)
         :auto-join-after-nick-acquisition
         (circe--auto-join-list :after-nick)
         :auto-join-after-nickserv-identification
         (circe--auto-join-list :after-auth)
         :auto-join-after-sasl-login
         (circe--auto-join-list :after-auth))))

(defun circe-reconnect-all ()
  "Reconnect all Circe connections."
  (interactive)
  (dolist (buf (circe-server-buffers))
    (with-current-buffer buf
      (if (called-interactively-p 'any)
          (call-interactively 'circe-reconnect)
        (circe-reconnect)))))

(defun circe--auto-join-list (type)
  "Return the list of channels to join for type TYPE."
  (let ((result nil)
        (current-type circe-server-auto-join-default-type))
    (dolist (channel circe-channels)
      (cond
       ((keywordp channel)
        (setq current-type channel))
       ((eq current-type type)
        (push channel result))))
    (nreverse result)))

(defun circe--auto-join-channel-buffers ()
  "Return a list of channels to join based on channel buffers.

This includes all channel buffers of the current server, but
excludes and channel that is already listed in
`circe-channels'."
  (let ((channels nil))
    (dolist (buf (circe-server-chat-buffers))
      (let ((name (with-current-buffer buf
                    (when (derived-mode-p 'circe-channel-mode)
                      circe-chat-target))))
        (when (and name
                   (not (member name circe-channels)))
          (push name channels))))
    channels))

;;;;;;;;;;;;;;;;;
;;; Base Mode ;;;
;;;;;;;;;;;;;;;;;

(defvar circe-mode-hook nil
  "Hook run for any Circe mode.")

(defvar circe-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-j") 'circe-command-JOIN)
    (define-key map (kbd "C-c C-r") 'circe-reconnect)
    map)
  "The base keymap for all Circe modes (server, channel, query)")

(defvar circe-server-buffer nil
  "The buffer of the server associated with the current chat buffer.")
(make-variable-buffer-local 'circe-server-buffer)

(define-derived-mode circe-mode lui-mode "Circe"
  "Base mode for all Circe buffers.

A buffer should never be in this mode directly, but rather in
modes that derive from this.

The mode inheritance hierarchy looks like this:

lui-mode
`-circe-mode
  `-circe-server-mode
  `-circe-chat-mode
    `-circe-channel-mode
    `-circe-query-mode"
  (add-hook 'lui-pre-output-hook 'lui-irc-colors
            t t)
  (add-hook 'lui-pre-output-hook 'circe--output-highlight-nick
            t t)
  (add-hook 'completion-at-point-functions 'circe--completion-at-point
            nil t)
  (lui-set-prompt circe-prompt-string)
  (goto-char (point-max))
  (setq lui-input-function 'circe--input
        default-directory (expand-file-name circe-default-directory)
        circe-server-last-active-buffer (current-buffer)
        flyspell-generic-check-word-p 'circe--flyspell-check-word-p)
  (when circe-use-cycle-completion
    (set (make-local-variable 'completion-cycle-threshold)
         t))
  ;; Tab completion should be case-insensitive
  (set (make-local-variable 'completion-ignore-case)
       t)
  (set (make-local-variable 'tracking-faces-priorities)
       circe-track-faces-priorities))

;;;;;;;;;;;;;;;;;;;;
;;;; Displaying ;;;;
;;;;;;;;;;;;;;;;;;;;

(defun circe-display (format &rest keywords)
  "Display FORMAT formatted with KEYWORDS in the current Circe buffer.
See `lui-format' for a description of the format.

If FORMAT contains the word server, the resulting string receives
a `circe-server-face'. If FORMAT contains the word self, the
whole string receives a `circe-my-message-face'. If FORMAT is in
`circe-format-not-tracked', a message of this type is never
tracked by Lui.

Keywords with the name :nick receive a `circe-originator-face'.

It is always possible to use the mynick or target formats."
  (when (not (circe--display-ignored-p format keywords))
    (let* ((name (symbol-name format))
           (face (cond
                  ((string-match "\\<server\\>" name)
                   'circe-server-face)
                  ((string-match "\\<self\\>" name)
                   'circe-my-message-face)))
           (keywords (append `(:mynick ,(circe-nick)
                                       :chattarget ,circe-chat-target)
                             (circe--display-add-nick-property
                              (if (and (not (null keywords))
                                       (null (cdr keywords)))
                                  (car keywords)
                                keywords))))
           (text (lui-format format keywords)))
      (when (circe--display-fool-p format keywords)
        (add-face-text-property 0 (length text)
                                'circe-fool-face t text)
        (put-text-property 0 (length text)
                           'lui-fool t
                           text))
      (when face
        (add-face-text-property 0 (length text)
                                face t text))
      (lui-insert text
                  (memq format circe-format-not-tracked)))))

(defun circe-display-server-message (message)
  "Display MESSAGE as a server message."
  (circe-display 'circe-format-server-message
                 :body message))

(defun circe--display-add-nick-property (keywords)
  "Add a face to the value of the :nick property in KEYWORDS."
  (let ((keyword nil))
    (mapcar (lambda (entry)
              (cond
               ((or (eq keyword :nick)
                    (eq keyword 'nick))
                (setq keyword nil)
                (propertize entry 'face 'circe-originator-face))
               (t
                (setq keyword entry)
                entry)))
            keywords)))

(defun circe--display-ignored-p (_format keywords)
  (let ((nick (plist-get keywords :nick))
        (userhost (plist-get keywords :userhost))
        (body (plist-get keywords :body)))
    (circe--ignored-p nick userhost body)))

(defun circe--display-fool-p (_format keywords)
  (let ((nick (plist-get keywords :nick))
        (userhost (plist-get keywords :userhost))
        (body (plist-get keywords :body)))
    (circe--fool-p nick userhost body)))

(defun circe--ignored-p (nick userhost body)
  "True if this user or message is being ignored.

See `circe-ignore-functions' and `circe-ignore-list'.

NICK, USER and HOST should be the sender of a the command
COMMAND, which had the arguments ARGS."
  (or (run-hook-with-args-until-success 'circe-ignore-functions
                                        nick userhost body)
      (circe--ignore-matches-p nick userhost body circe-ignore-list)))

(defun circe--fool-p (nick userhost body)
  "True if this user or message is a fool.

See `circe-fool-list'.

NICK, USER and HOST should be the sender of a the command
COMMAND, which had the arguments ARGS."
  (circe--ignore-matches-p nick userhost body circe-fool-list))

(defun circe--ignore-matches-p (nick userhost body patterns)
  "Check if a given command does match an ignore pattern.

A pattern matches if it either matches the user NICK!USER@HOST,
or if it matches the first word in BODY.

PATTERNS should be the list of regular expressions."
  (let ((string (format "%s!%s" nick userhost))
        (target (when (and body
                           (string-match "^\\([^ ]*\\)[:,]" body))
                  (match-string 1 body))))
    (catch 'return
      (dolist (regex patterns)
        (when (string-match regex string)
          (throw 'return t))
        (when (and (stringp target)
                   (string-match regex target))
          (throw 'return t)))
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Nick Highlighting ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun circe--output-highlight-nick ()
  "Highlight the nick of the user in the buffer.

This is used in `lui-pre-output-hook'."
  (goto-char (or (text-property-any (point-min) (point-max)
                                    'lui-format-argument 'body)
                 (point-min)))
  (when (or (not circe-inhibit-nick-highlight-function)
            (not (funcall circe-inhibit-nick-highlight-function)))
    (let* ((nick (circe-nick))
           (nicks (append (and nick (list nick))
                          circe-extra-nicks)))
      (when nicks
        ;; Can't use \<...\> because that won't match for \<forcer-\> We
        ;; might eventually use \_< ... \_> if we define symbols to be
        ;; nicks \\= is necessary, because it might be found right where we
        ;; are, and that might not be the beginning of a line... (We start
        ;; searching from the beginning of the body)
        (let ((nick-regex (concat "\\(?:^\\|\\W\\|\\=\\)"
                                  "\\(" (regexp-opt nicks) "\\)"
                                  "\\(?:$\\|\\W\\)")))
          (cond
           ((eq circe-highlight-nick-type 'sender)
            (if (text-property-any (point-min)
                                   (point-max)
                                   'face 'circe-originator-face)
                (when (re-search-forward nick-regex nil t)
                  (circe--extend-text-having-face
                   (point-min) (point-max)
                   'circe-originator-face
                   'circe-highlight-nick-face))
              (let ((circe-highlight-nick-type 'occurrence))
                (circe--output-highlight-nick))))
           ((eq circe-highlight-nick-type 'occurrence)
            (while (re-search-forward nick-regex nil t)
              (add-face-text-property (match-beginning 1)
                                      (match-end 1)
                                      'circe-highlight-nick-face)))
           ((eq circe-highlight-nick-type 'message)
            (when (re-search-forward nick-regex nil t)
              (let* ((start (text-property-any (point-min)
                                               (point-max)
                                               'lui-format-argument 'body))
                     (end (when start
                            (next-single-property-change start
                                                         'lui-format-argument))))
                (when (and start end)
                  (add-face-text-property start end
                                          'circe-highlight-nick-face)))))
           ((eq circe-highlight-nick-type 'all)
            (when (re-search-forward nick-regex nil t)
              (add-face-text-property (point-min) (point-max)
                                      'circe-highlight-nick-face)))))))))

(defun circe--extend-text-having-face (from to existing new)
  "Extend property values.

In the text between FROM and TO, find any text that has its face
property set to EXISTING, and prepend NEW to the value of its
face property, when necessary by turning it into a list."
  (let ((beg (text-property-any from to 'face existing)))
    (while beg
      (let ((end (next-single-property-change beg 'face)))
        (add-face-text-property beg end new)
        (setq beg (text-property-any end to 'face existing))))))

;;;;;;;;;;;;;;;
;;;; Input ;;;;
;;;;;;;;;;;;;;;

(defun circe--input (str)
  "Process STR as input.

This detects commands and interprets them, or sends the input
using the /SAY command."
  (set-text-properties 0 (length str) nil str)
  (cond
   ((string= str "")
    nil)
   ;; Ignore commands in multiline input
   ((and (not (string-match "\n" str))
         (string-match "\\`/\\([^/ ][^ ]*\\|[^/ ]*\\) ?\\([^\n]*\\)\\'" str))
    (let* ((command (match-string 1 str))
           (args (match-string 2 str))
           (handler (intern-soft (format "circe-command-%s"
                                         (upcase command)))))
      (cond
       ((string= command "")
        (circe-command-SAY args))
       (handler
        (funcall handler args))
       (circe-server-send-unknown-command-p
        (irc-send-raw (circe-server-process)
                      (format "%s %s"
                              (upcase command)
                              args)))
       (t
        (circe-display-server-message (format "Unknown command: %s"
                                      command))))))
   (t
    (mapc #'circe-command-SAY
          (circe--list-drop-right (split-string str "\n")
                                  "^ *$")))))

;;;;;;;;;;;;;;;;;;
;;;; Flyspell ;;;;
;;;;;;;;;;;;;;;;;;

(defun circe--flyspell-check-word-p ()
  "Return a true value if flyspell check the word before point.

This is a suitable value for `flyspell-generic-check-word-p'. It
will also call `lui-flyspell-check-word-p'."
  (cond
   ((not (lui-flyspell-check-word-p))
    nil)
   ((circe-channel-user-p (circe--flyspell-nick-before-point))
    nil)
   (t
    t)))

(defun circe--flyspell-nick-before-point ()
  "Return the IRC nick before point"
  (with-syntax-table circe-nick-syntax-table
    (let (beg end)
      (save-excursion
        (forward-word -1)
        (setq beg (point))
        (forward-word 1)
        (setq end (point)))
      (buffer-substring beg end))))

;;;;;;;;;;;;;;;;;;;;
;;;; Completion ;;;;
;;;;;;;;;;;;;;;;;;;;

(defun circe--completion-at-point ()
  "Return a list of possible completions for the current buffer.

This is used in `completion-at-point-functions'."
  ;; Use markers so they move when input happens
  (let ((start (make-marker))
        (end (make-marker)))
    (set-marker end (point))
    (set-marker start
                (save-excursion
                  (when (or (looking-back (regexp-quote
                                           circe-completion-suffix)
                                          (length circe-completion-suffix))
                            (looking-back " " 1))
                    (goto-char (match-beginning 0)))
                  (cond
                   ((<= (point) lui-input-marker)
                    lui-input-marker)
                   ((re-search-backward "\\s-" lui-input-marker t)
                    (1+ (point)))
                   (t
                    lui-input-marker))))
    (list start end 'circe--completion-table)))

(defun circe--completion-table (string pred action)
  "Completion table to use for Circe buffers.

See `minibuffer-completion-table' for details."
  (cond
   ;; Best completion of STRING
   ((eq action nil)
    (try-completion string
                    (circe--completion-candidates
                     (if (= (- (point) (length string))
                            lui-input-marker)
                         circe-completion-suffix
                       " "))
                    pred))
   ;; A list of possible completions of STRING
   ((eq action t)
    (all-completions string
                     (circe--completion-candidates
                      (if (= (- (point) (length string))
                             lui-input-marker)
                          circe-completion-suffix
                        " "))
                     pred))
   ;; t iff STRING is a valid completion as it stands
   ((eq action 'lambda)
    (test-completion string
                     (circe--completion-candidates
                      (if (= (- (point) (length string))
                             lui-input-marker)
                          circe-completion-suffix
                        " "))
                     pred))
   ;; Boundaries
   ((eq (car-safe action) 'boundaries)
    `(boundaries 0 . ,(length (cdr action))))
   ;; Metadata
   ((eq action 'metadata)
    '(metadata (cycle-sort-function . circe--completion-sort)))))

(defun circe--completion-clean-nick (string)
  (with-temp-buffer
    (insert string)
    (goto-char (point-max))
    (when (or (looking-back circe-completion-suffix nil)
              (looking-back " " nil))
      (replace-match ""))
    (buffer-string)))

(defun circe--completion-sort (collection)
  "Sort the COLLECTION by channel activity for nicks."
  (let* ((proc (circe-server-process))
         (channel (when (and circe-chat-target proc)
                    (irc-connection-channel proc circe-chat-target)))
         (decorated (mapcar (lambda (entry)
                              (let* ((nick (circe--completion-clean-nick
                                            entry))
                                     (user (when channel
                                             (irc-channel-user channel nick))))
                                (list (when user
                                        (irc-user-last-activity-time user))
                                      (length entry)
                                      entry)))
                            collection))
         (sorted (sort decorated
                       (lambda (a b)
                         (cond
                          ((and (car a)
                                (car b))
                           (> (car a)
                              (car b)))
                          ((and (not (car a))
                                (not (car b)))
                           (< (cadr a)
                              (cadr b)))
                          ((car a)
                           t)
                          (t
                           nil))))))
    (mapcar (lambda (entry)
              (nth 2 entry))
            sorted)))

;; FIXME: I do not know why this is here.
(defvar circe--completion-old-completion-all-sorted-completions nil
  "Variable to know if we can return a cached result.")
(make-variable-buffer-local
 'circe--completion-old-completion-all-sorted-completions)
(defvar circe--completion-cache nil
  "The results we can cache.")
(make-variable-buffer-local 'circe--completion-cache)

(defun circe--completion-candidates (nick-suffix)
  (if (and circe--completion-old-completion-all-sorted-completions
           (eq completion-all-sorted-completions
               circe--completion-old-completion-all-sorted-completions))
      circe--completion-cache
    (let ((completions (append (circe--commands-list)
                               (mapcar (lambda (buf)
                                         (with-current-buffer buf
                                           circe-chat-target))
                                       (circe-server-channel-buffers)))))
      (cond
       ;; In a server buffer, complete all nicks in all channels
       ((eq major-mode 'circe-server-mode)
        (dolist (buf (circe-server-channel-buffers))
          (with-current-buffer buf
            (dolist (nick (circe-channel-nicks))
              (setq completions (cons (concat nick nick-suffix)
                                      completions))))))
       ;; In a channel buffer, only complete nicks in this channel
       ((eq major-mode 'circe-channel-mode)
        (setq completions (append (delete (concat (circe-nick)
                                                  nick-suffix)
                                          (mapcar (lambda (nick)
                                                    (concat nick nick-suffix))
                                                  (circe-channel-nicks)))
                                  completions)))
       ;; In a query buffer, only complete this query partner
       ((eq major-mode 'circe-query-mode)
        (setq completions (cons (concat circe-chat-target nick-suffix)
                                completions)))
       ;; Else, we're doing something wrong
       (t
        (error "`circe-possible-completions' called outside of Circe")))
      (setq circe--completion-old-completion-all-sorted-completions
            completion-all-sorted-completions
            circe--completion-cache completions)
      completions)))

(defun circe--commands-list ()
  "Return a list of possible Circe commands."
  (mapcar (lambda (symbol)
            (let ((str (symbol-name symbol)))
              (if (string-match "^circe-command-\\(.*\\)" str)
                  (concat "/" (match-string 1 str) " ")
                str)))
          (apropos-internal "^circe-command-")))

;;;;;;;;;;;;;;;;;;;
;;; Server Mode ;;;
;;;;;;;;;;;;;;;;;;;

(defvar circe-server-mode-hook nil
  "Hook run when a new Circe server buffer is created.")

(defvar circe-server-mode-map (make-sparse-keymap)
  "The key map for server mode buffers.")

(define-derived-mode circe-server-mode circe-mode "Circe Server"
  "The mode for circe server buffers.

This buffer represents a server connection. When you kill it, the
server connection is closed. This will make all associated
buffers unusable. Be sure to use \\[circe-reconnect] if you want
to reconnect to the server.

\\{circe-server-mode-map}"
  (add-hook 'kill-buffer-hook 'circe-server-killed nil t))

(defun circe-server-killed ()
  "Run when the server buffer got killed.

This will IRC, and ask the user whether to kill all of the
server's chat buffers."
  (when circe-server-killed-confirmation
    (when (not (y-or-n-p
                (if (eq circe-server-killed-confirmation 'ask-and-kill-all)
                    "Really kill all buffers of this server? (if not, try `circe-reconnect') "
                  "Really kill the IRC connection? (if not, try `circe-reconnect') ")))
      (error "Buffer not killed as per user request")))
  (setq circe-server-inhibit-auto-reconnect-p t)
  (ignore-errors
    (irc-send-QUIT circe-server-process circe-default-quit-message))
  (ignore-errors
    (delete-process circe-server-process))
  (when (or (eq circe-server-killed-confirmation 'ask-and-kill-all)
            (eq circe-server-killed-confirmation 'kill-all))
    (dolist (buf (circe-server-chat-buffers))
      (let ((circe-channel-killed-confirmation nil))
        (kill-buffer buf)))))

(defun circe-server-buffers ()
  "Return a list of all server buffers in this Emacs instance."
  (let ((result nil))
    (dolist (buf (buffer-list))
      (with-current-buffer buf
        (when (eq major-mode 'circe-server-mode)
          (setq result (cons buf result)))))
    (nreverse result)))

(defun circe-server-process ()
  "Return the current server process."
  (with-circe-server-buffer
    circe-server-process))

(defun circe-server-my-nick-p (nick)
  "Return non-nil when NICK is our current nick."
  (let ((proc (circe-server-process)))
    (when proc
      (irc-current-nick-p proc nick))))

(defun circe-nick ()
  "Return our current nick."
  (let ((proc (circe-server-process)))
    (when proc
      (irc-current-nick proc))))

(defun circe-server-last-active-buffer ()
  "Return the last active buffer of this server."
  (with-circe-server-buffer
    (if (and circe-server-last-active-buffer
             (bufferp circe-server-last-active-buffer)
             (buffer-live-p circe-server-last-active-buffer))
        circe-server-last-active-buffer
      (current-buffer))))

;; There really ought to be a hook for this
(defadvice select-window (after circe-server-track-select-window
                                (window &optional norecord))
  "Remember the current buffer as the last active buffer.
This is used by Circe to know where to put spurious messages."
  (with-current-buffer (window-buffer window)
    (when (derived-mode-p 'circe-mode)
      (let ((buf (current-buffer)))
        (ignore-errors
          (with-circe-server-buffer
            (setq circe-server-last-active-buffer buf)))))))
(ad-activate 'select-window)

(defun circe-reduce-lurker-spam ()
  "Return the value of `circe-reduce-lurker-spam'.

This uses a buffer-local value first, then the one in the server
buffer.

Use this instead of accessing the variable directly to enable
setting the variable through network options."
  (if (local-variable-p 'circe-reduce-lurker-spam)
      circe-reduce-lurker-spam
    (with-circe-server-buffer
      circe-reduce-lurker-spam)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Chat Buffer Management ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Server buffers keep track of associated chat buffers. This enables
;; us to not rely on buffer names staying the same, as well as keeping
;; buffers from different servers and even server connections apart
;; cleanly.

(defvar circe-server-chat-buffer-table nil
  "A hash table of chat buffers associated with this server.")
(make-variable-buffer-local 'circe-server-chat-buffer-table)

(defun circe-server-get-chat-buffer (target)
  "Return the chat buffer addressing TARGET, or nil if none."
  (with-circe-server-buffer
    (when circe-server-chat-buffer-table
      (let* ((target-name (irc-isupport--case-fold (circe-server-process)
                                                   target))
             (buf (gethash target-name circe-server-chat-buffer-table)))
        (if (buffer-live-p buf)
            buf
          (remhash target-name circe-server-chat-buffer-table)
          nil)))))

(defun circe-server-create-chat-buffer (target chat-mode)
  "Return a new buffer addressing TARGET in CHAT-MODE."
  (with-circe-server-buffer
    (let* ((target-name (irc-isupport--case-fold (circe-server-process)
                                                 target))
           (chat-buffer (generate-new-buffer target))
           (server-buffer (current-buffer))
           (circe-chat-calling-server-buffer-and-target (cons server-buffer
                                                              target-name)))
      (when (not circe-server-chat-buffer-table)
        (setq circe-server-chat-buffer-table (make-hash-table :test 'equal)))
      (puthash target-name chat-buffer circe-server-chat-buffer-table)
      (with-current-buffer chat-buffer
        (funcall chat-mode))
      chat-buffer)))

(defun circe-server-get-or-create-chat-buffer (target chat-mode)
  "Return a buffer addressing TARGET; create one in CHAT-MODE if none exists."
  (let ((buf (circe-server-get-chat-buffer target)))
    (if buf
        buf
      (circe-server-create-chat-buffer target chat-mode))))

(defun circe-server-remove-chat-buffer (target-or-buffer)
  "Remove the buffer addressing TARGET-OR-BUFFER."
  (with-circe-server-buffer
    (let* ((target (if (bufferp target-or-buffer)
                       (circe-server-chat-buffer-target target-or-buffer)
                     target-or-buffer))
           (target-name  (irc-isupport--case-fold (circe-server-process)
                                                  target)))
      (remhash target-name circe-server-chat-buffer-table))))

(defun circe-server-rename-chat-buffer (old-name new-name)
  "Note that the chat buffer addressing OLD-NAME now addresses NEW-NAME."
  (with-circe-server-buffer
    (let* ((old-target-name (irc-isupport--case-fold (circe-server-process)
                                                     old-name))
           (new-target-name (irc-isupport--case-fold (circe-server-process)
                                                     new-name))
           (buf (gethash old-target-name circe-server-chat-buffer-table)))
      (when buf
        (remhash old-target-name circe-server-chat-buffer-table)
        (puthash new-target-name buf circe-server-chat-buffer-table)
        (with-current-buffer buf
          (setq circe-chat-target new-name)
          (rename-buffer new-name t))))))

(defun circe-server-chat-buffer-target (&optional buffer)
  "Return the chat target of BUFFER, or the current buffer if none."
  (if buffer
      (with-current-buffer buffer
        circe-chat-target)
    circe-chat-target))

(defun circe-server-chat-buffers ()
  "Return the list of chat buffers on this server."
  (with-circe-server-buffer
    (when circe-server-chat-buffer-table
      (let ((buffer-list nil))
        (maphash (lambda (target-name buffer)
                   (if (buffer-live-p buffer)
                       (push buffer buffer-list)
                     (remhash target-name circe-server-chat-buffer-table)))
                 circe-server-chat-buffer-table)
        buffer-list))))

(defun circe-server-channel-buffers ()
  "Return a list of all channel buffers of this server."
  (let ((result nil))
    (dolist (buf (circe-server-chat-buffers))
      (with-current-buffer buf
        (when (eq major-mode 'circe-channel-mode)
          (setq result (cons buf result)))))
    (nreverse result)))

;;;;;;;;;;;;;;;;;
;;; Chat Mode ;;;
;;;;;;;;;;;;;;;;;

(defvar circe-chat-mode-hook nil
  "Hook run when a new chat buffer (channel or query) is created.")

(defvar circe-chat-mode-map (make-sparse-keymap)
  "Base key map for all Circe chat buffers (channel, query).")

;; Defined here as we use it, but do not necessarily want to use the
;; full module.
(defvar lui-logging-format-arguments nil
  "A list of arguments to be passed to `lui-format'.
This can be used to extend the formatting possibilities of the
file name for lui applications.")
(make-variable-buffer-local 'lui-logging-format-arguments)

(define-derived-mode circe-chat-mode circe-mode "Circe Chat"
  "The circe chat major mode.

This is the common mode used for both queries and channels.
It should not be used directly.
TARGET is the default target to send data to.
SERVER-BUFFER is the server buffer of this chat buffer."
  (setq circe-server-buffer (car circe-chat-calling-server-buffer-and-target)
        circe-chat-target (cdr circe-chat-calling-server-buffer-and-target))
  (let ((network (with-circe-server-buffer
                   circe-network)))
    (make-local-variable 'mode-line-buffer-identification)
    (setq mode-line-buffer-identification
          (list (format "%%b@%-8s" network)))
    (setq lui-logging-format-arguments
          `(:target ,circe-chat-target :network ,network)))
  (when (equal circe-chat-target "#emacs-circe")
    (set (make-local-variable 'lui-button-issue-tracker)
         "https://github.com/jorgenschaefer/circe/issues/%s")))

(defun circe-chat-disconnected ()
  "The current buffer got disconnected."
  (circe-display-server-message "Disconnected"))

;;;;;;;;;;;;;;;;;;;;
;;; Channel Mode ;;;
;;;;;;;;;;;;;;;;;;;;

(defvar circe-channel-mode-hook nil
  "Hook run in a new channel buffer.")

(defvar circe-channel-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-n") 'circe-command-NAMES)
    (define-key map (kbd "C-c C-t") 'circe-command-CHTOPIC)
    map)
  "The key map for channel mode buffers.")

(define-derived-mode circe-channel-mode circe-chat-mode "Circe Channel"
  "The circe channel chat major mode.
This mode represents a channel you are talking in.

TARGET is the default target to send data to.
SERVER-BUFFER is the server buffer of this chat buffer.

\\{circe-channel-mode-map}"
  (add-hook 'kill-buffer-hook 'circe-channel-killed nil t))

(defun circe-channel-killed ()
  "Called when the channel buffer got killed.

If we are not on the channel being killed, do nothing. Otherwise,
if the server is live, and the user wants to kill the buffer,
send PART to the server and clean up the channel's remaining
state."
  (when (buffer-live-p circe-server-buffer)
    (when (and circe-channel-killed-confirmation
               (not (y-or-n-p "Really leave this channel? ")))
      (error "Channel not left."))
    (ignore-errors
      (irc-send-PART (circe-server-process)
                     circe-chat-target
                     circe-default-part-message))
    (ignore-errors
      (circe-server-remove-chat-buffer circe-chat-target))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Channel User Tracking ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Channel mode buffers provide some utility functions to check if a
;; given user is idle or not.

(defun circe-channel-user-nick-regain-p (_old new)
  "Return true if a nick change from OLD to NEW constitutes a nick regain.

A nick was regained if the NEW nick was also a recent user."
  (let ((channel (irc-connection-channel (circe-server-process)
                                         circe-chat-target)))
    (when channel
      (irc-channel-recent-user channel new))))

(defun circe-channel-user-p (nick)
  "Return non-nil when NICK belongs to a channel user."
  (cond
   ((eq major-mode 'circe-query-mode)
    (irc-string-equal-p (circe-server-process)
                        nick
                        circe-chat-target))
   ((eq major-mode 'circe-channel-mode)
    (let ((channel (irc-connection-channel (circe-server-process)
                                           circe-chat-target)))
      (when channel
        (if (irc-channel-user channel nick)
            t
          nil))))))

(defun circe-channel-nicks ()
  "Return a list of nicks in the current channel."
  (let* ((channel (irc-connection-channel (circe-server-process)
                                          circe-chat-target))
         (nicks nil))
    (when channel
      (maphash (lambda (_folded-nick user)
                 (push (irc-user-nick user) nicks))
               (irc-channel-users channel)))
    nicks))

(defun circe-user-channels (nick)
  "Return a list of channel buffers for the user named NICK."
  (let* ((result nil))
    (dolist (channel (irc-connection-channel-list (circe-server-process)))
      (when (irc-channel-user channel nick)
        (let* ((name (irc-channel-name channel))
               (buf (circe-server-get-chat-buffer name)))
          (when buf
            (push buf result)))))
    result))

(defun circe-lurker-p (nick)
  "Return a true value if this nick is regarded inactive."
  (let* ((channel (irc-connection-channel (circe-server-process)
                                          circe-chat-target))
         (user (when channel
                 (irc-channel-user channel nick)))
         (recent-user (when channel
                        (irc-channel-recent-user channel nick)))
         (last-active (cond
                       (user
                        (irc-user-last-activity-time user))
                       (recent-user
                        (irc-user-last-activity-time recent-user)))))
    (cond
     ;; If we do not track lurkers, no one is ever a lurker.
     ((not (circe-reduce-lurker-spam))
      nil)
     ;; We ourselves are never lurkers (in this sense).
     ((circe-server-my-nick-p nick)
      nil)
     ;; Someone who isn't even on the channel (e.g. NickServ) isn't a
     ;; lurker, either.
     ((and (not user)
           (not recent-user))
      nil)
     ;; If someone has never been active, they most definitely *are* a
     ;; lurker.
     ((not last-active)
      t)
     ;; But if someone has been active, and we mark active users
     ;; inactive again after a timeout ...
     (circe-active-users-timeout
      ;; They are still lurkers if their activity has been too long
      ;; ago.
      (> (- (float-time)
            last-active)
         circe-active-users-timeout))
     ;; Otherwise, they have been active and we don't mark active
     ;; users inactive again, so nope, not a lurker.
     (t
      nil))))

(defun circe-lurker-rejoin-p (nick channel)
  "Return true if NICK is rejoining CHANNEL.

A user is considered to be rejoining if they were on the channel
shortly before, and were active then."
  (let* ((channel (irc-connection-channel (circe-server-process)
                                          channel))
         (user (when channel
                 (irc-channel-recent-user channel nick))))
    (when user
      (irc-user-last-activity-time user))))

(defun circe-lurker-display-active (nick userhost)
  "Show that this user is active if they are a lurker."
  (let* ((channel (irc-connection-channel (circe-server-process)
                                          circe-chat-target))
         (user (when channel
                 (irc-channel-user channel nick)))
         (join-time (when user
                      (irc-user-join-time user))))
    (when (and (circe-lurker-p nick)
               ;; If we saw them when we joined the channel, no need to
               ;; say "they're suddenly active!!111one".
               join-time)
      (circe-display 'circe-format-server-lurker-activity
                     :nick nick
                     :userhost (or userhost "server")
                     :jointime join-time
                     :joindelta (circe-duration-string
                                 (- (float-time)
                                    join-time))))))

;;;;;;;;;;;;;;;;;;
;;; Query Mode ;;;
;;;;;;;;;;;;;;;;;;

(defvar circe-query-mode-hook nil
  "Hook run when query mode is activated.")

(defvar circe-query-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map circe-chat-mode-map)
    map)
  "The key map for query mode buffers.")

(define-derived-mode circe-query-mode circe-chat-mode "Circe Query"
  "The circe query chat major mode.
This mode represents a query you are talking in.

TARGET is the default target to send data to.
SERVER-BUFFER is the server buffer of this chat buffer.

\\{circe-query-mode-map}"
  (add-hook 'kill-buffer-hook 'circe-query-killed nil t))

(defun circe-query-killed ()
  "Called when the query buffer got killed."
  (ignore-errors
    (circe-server-remove-chat-buffer circe-chat-target)))

(defun circe-query-auto-query-buffer (who)
  "Return a buffer for a query with `WHO'.

This adheres to `circe-auto-query-max'."
  (or (circe-server-get-chat-buffer who)
      (when (< (circe--query-count)
               circe-auto-query-max)
        (circe-server-get-or-create-chat-buffer who 'circe-query-mode))))

(defun circe--query-count ()
  "Return the number of queries on the current server."
  (let ((num 0))
    (dolist (buf (circe-server-chat-buffers))
      (with-current-buffer buf
        (when (eq major-mode 'circe-query-mode)
          (setq num (+ num 1)))))
    num))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; IRC Protocol Handling ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar circe--irc-handler-table nil
  "The handler table for Circe's IRC connections.

Do not use this directly. Instead, call `circe-irc-handler-table'.")

(defun circe-irc-handler-table ()
  (when (not circe--irc-handler-table)
    (let ((table (irc-handler-table)))
      (irc-handler-add table "irc.registered" #'circe--irc-conn-registered)
      (irc-handler-add table "conn.disconnected" #'circe--irc-conn-disconnected)
      (irc-handler-add table nil #'circe--irc-display-event)
      (irc-handle-registration table)
      (irc-handle-ping-pong table)
      (irc-handle-isupport table)
      (irc-handle-initial-nick-acquisition table)
      (irc-handle-ctcp table)
      (irc-handle-state-tracking table)
      (irc-handle-nickserv table)
      (irc-handle-auto-join table)
      (setq circe--irc-handler-table table)))
  circe--irc-handler-table)

(defun circe--irc-conn-registered (conn _event _nick)
  (with-current-buffer (irc-connection-get conn :server-buffer)
    (setq circe-server-reconnect-attempts 0)
    (run-hooks 'circe-server-connected-hook)))

(defun circe--irc-conn-disconnected (conn _event)
  (with-current-buffer (irc-connection-get conn :server-buffer)
    (dolist (buf (circe-server-chat-buffers))
      (with-current-buffer buf
        (circe-chat-disconnected)))

    (circe-reconnect)))

(defun circe--irc-display-event (conn event &optional sender &rest args)
  "Display an IRC message.

NICK, USER and HOST specify the originator of COMMAND with ARGS
as arguments."
  (with-current-buffer (irc-connection-get conn :server-buffer)
    (let* ((display (circe-get-display-handler event))
           (nick (when sender
                   (irc-userstring-nick sender)))
           (userhost (when sender
                       (irc-userstring-userhost sender))))
      (cond
       ;; Functions get called
       ((functionp display)
        (apply display nick userhost event args))
       ;; Lists describe patterns
       ((consp display)
        (circe--irc-display-format (elt display 1)
                                     (elt display 0)
                                     nick userhost event args))
       ;; No configured display handler, show a default
       (t
        (circe--irc-display-default nick userhost event args))))))

(defvar circe--irc-format-server-numeric "*** %s"
  "The format to use for server messages. Do not set this.")

(defun circe--irc-display-format (format target nick userhost event args)
  (let* ((target+name (circe--irc-display-target target nick args))
         (target (car target+name))
         (name (cdr target+name))
         (origin (if userhost
                     (format "%s (%s)" nick userhost)
                   (format "%s" nick))))
    (with-current-buffer (or target
                             (circe-server-last-active-buffer))
      (let ((circe--irc-format-server-numeric
             (if target
                 (format "*** %s" format)
               (format "*** [%s] %s" name format))))
        (circe-display 'circe--irc-format-server-numeric
                       :nick (or nick "(unknown)")
                       :userhost (or userhost "server")
                       :origin origin
                       :event event
                       :command event
                       :target name
                       :indexed-args args)))))

(defun circe--irc-display-target (target nick args)
  "Return the target buffer and name.
The buffer might be nil if it is not alive.

See `circe-set-display-handler' for a description of target.

NICK and USERHOST are the originator of COMMAND which had ARGS as
arguments."
  (cond
   ((eq target 'nick)
    (cons (circe-server-get-chat-buffer nick)
          nick))
   ((numberp target)
    (let ((name (nth target
                     args)))
      (cons (circe-server-get-chat-buffer name)
            name)))
   ((eq target 'active)
    (let ((buf (circe-server-last-active-buffer)))
      (cons buf
            (buffer-name buf))))
   ((eq target 'server)
    (cons (current-buffer) (buffer-name)))
   (t
    (error "Bad target in format string: %s" target))))

(defun circe--irc-display-default (nick userhost event args)
  (with-current-buffer (circe-server-last-active-buffer)
    (let ((target (if (circe-server-my-nick-p (car args))
                      ""
                    (format " to %s" (car args)))))
      (cond
       ((string-match "\\`irc.ctcpreply.\\(.*\\)\\'" event)
        (circe-display-server-message
         (format "CTCP %s reply from %s (%s)%s: %s"
                 (match-string 1 event) nick userhost target (cadr args))))
       ((string-match "\\`irc.ctcp.\\(.*\\)\\'" event)
        (circe-display-server-message
         (format "Unknown CTCP request %s from %s (%s)%s: %s"
                 (match-string 1 event) nick userhost target (cadr args))))
       (t
        (circe-display-server-message
         (format "[%s from %s%s] %s"
                 event
                 nick
                 (if userhost
                     (format " (%s)" userhost)
                   "")
                 (mapconcat #'identity args " "))))))))

(defun circe-set-display-handler (command handler)
  "Set the display handler for COMMAND to HANDLER.

A handler is either a function or a list.

A function gets called in the server buffer with at least three
arguments, but possibly more. There's at least NICK and USERHOST
of the sender, which can be nil, and COMMAND, which is the event
which triggered this. Further arguments are arguments to the
event.

Alternatively, the handler can be a list of two elements:

  target   - The target of this message
  format   - The format for this string

The target can be any of:

  'active  - The last active buffer of this server
  'nick    - The nick who sent this message
  'server  - The server buffer for this server
  number   - The index of the argument of the target

The format is passed to `lui-format'. Possible format string
substitutions are {mynick}, {target}, {nick}, {userhost},
{origin}, {command}, {target}, and indexed arguments for the
arguments to the IRC message."
  (when (not circe-display-table)
    (setq circe-display-table (make-hash-table :test 'equal)))
  (puthash command handler circe-display-table))

(defun circe-get-display-handler (command)
  "Return the display handler for COMMAND.

See `circe-set-display-handler' for more information."
  (when circe-display-table
    (gethash command circe-display-table)))

;;;;;;;;;;;;;;;;
;;; Commands ;;;
;;;;;;;;;;;;;;;;

(defun circe-command-AWAY (reason)
  "Set yourself away with REASON."
  (interactive "sReason: ")
  (irc-send-AWAY (circe-server-process) reason))

(defun circe-command-BACK (&optional ignored)
  "Mark yourself not away anymore.

Arguments are IGNORED."
  (interactive)
  (irc-send-AWAY (circe-server-process)))

(defun circe-command-CHTOPIC (&optional ignored)
  "Insert the topic of the current channel.

Arguments are IGNORED."
  (interactive)
  (if (not circe-chat-target)
      (circe-display-server-message "No target for current buffer")
    (let* ((channel (irc-connection-channel (circe-server-process)
                                            circe-chat-target))
           (topic (when channel
                    (irc-channel-topic channel))))
      (lui-replace-input (format "/TOPIC %s %s"
                                 circe-chat-target (or topic ""))))
    (goto-char (point-max))))

(defun circe-command-CLEAR (&optional ignored)
  "Delete all buffer contents before the lui prompt."
  (let ((inhibit-read-only t))
    (delete-region (point-min) lui-output-marker)))

(defun circe-command-CTCP (who &optional command argument)
  "Send a CTCP message to WHO containing COMMAND with ARGUMENT.
If COMMAND is not given, WHO is parsed to contain all of who,
command and argument.
If ARGUMENT is nil, it is interpreted as no argument."
  (when (not command)
    (if (string-match "^\\([^ ]*\\) *\\([^ ]*\\) *\\(.*\\)" who)
        (setq command (upcase (match-string 2 who))
              argument (match-string 3 who)
              who (match-string 1 who))
      (circe-display-server-message "Usage: /CTCP <who> <what>")))
  (when (not (string= "" command))
    (irc-send-ctcp (circe-server-process)
                   who
                   command
                   (if (and argument (not (equal argument "")))
                       argument
                     nil))))

(defun circe-command-FOOL (line)
  "Add the regex on LINE to the `circe-fool-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (add-to-list 'circe-fool-list regex)
        (circe-display-server-message (format "Recognizing %s as a fool"
                                      regex))))
     ((not circe-fool-list)
      (circe-display-server-message "Your do not know any fools"))
     (t
      (circe-display-server-message "Your list of fools:")
      (dolist (regex circe-fool-list)
        (circe-display-server-message (format "- %s" regex)))))))

(defun circe-command-GAWAY (reason)
  "Set yourself away on all servers with reason REASON."
  (interactive "sReason: ")
  (dolist (buf (circe-server-buffers))
    (with-current-buffer buf
      (irc-send-AWAY circe-server-process reason))))

(defun circe-command-GQUIT (reason)
  "Quit all servers with reason REASON."
  (interactive "sReason: ")
  (dolist (buf (circe-server-buffers))
    (with-current-buffer buf
      (when (eq (process-status circe-server-process)
                'open)
        (irc-send-QUIT circe-server-process reason)))))

(defun circe-command-HELP (&optional ignored)
  "Display a list of recognized commands, nicely formatted."
  (circe-display-server-message
   (concat "Recognized commands are: "
	   (mapconcat (lambda (s) s) (circe--commands-list) ""))))

(defun circe-command-IGNORE (line)
  "Add the regex on LINE to the `circe-ignore-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (add-to-list 'circe-ignore-list regex)
        (circe-display-server-message (format "Ignore list, meet %s"
                                      regex))))
     ((not circe-ignore-list)
      (circe-display-server-message "Your ignore list is empty"))
     (t
      (circe-display-server-message "Your ignore list:")
      (dolist (regex circe-ignore-list)
        (circe-display-server-message (format "- %s" regex)))))))

(defun circe-command-INVITE (nick &optional channel)
  "Invite NICK to CHANNEL.
When CHANNEL is not given, NICK is assumed to be a string
consisting of two words, the nick and the channel."
  (interactive "sInvite who: \nsWhere: ")
  (when (not channel)
    (if (string-match "^\\([^ ]+\\) +\\([^ ]+\\)" nick)
        (setq channel (match-string 2 nick)
              nick (match-string 1 nick))
      (when (or (string= "" nick) (null nick))
        (circe-display-server-message "Usage: /INVITE <nick> <channel>"))))
  (irc-send-INVITE (circe-server-process)
                   nick
                   (if (and (null channel)
                            (not (null nick)))
                       circe-chat-target
                     channel)))

(defun circe-command-JOIN (channel)
  "Join CHANNEL. This can also contain a key."
  (interactive "sChannel: ")
  (let (channels keys)
    (when (string-match "^\\s-*\\([^ ]+\\)\\(:? \\([^ ]+\\)\\)?$" channel)
      (setq channels (match-string 1 channel)
            keys (match-string 3 channel))
      (dolist (channel (split-string channels ","))
        (pop-to-buffer
         (circe-server-get-or-create-chat-buffer channel
                                                 'circe-channel-mode)))
      (irc-send-JOIN (circe-server-process) channels keys))))

(defun circe-command-ME (line)
  "Send LINE to IRC as an action."
  (interactive "sAction: ")
  (if (not circe-chat-target)
      (circe-display-server-message "No target for current buffer")
    (circe-display 'circe-format-self-action
                   :body line
                   :nick (circe-nick))
    (irc-send-ctcp (circe-server-process)
                   circe-chat-target
                   "ACTION" line)))

(defun circe-command-MSG (who &optional what)
  "Send a message.

Send WHO a message containing WHAT.

If WHAT is not given, WHO should contain both the nick and the
message separated by a space."
  (when (not what)
    (if (string-match "^\\([^ ]*\\) \\(.*\\)" who)
        (setq what (match-string 2 who)
              who (match-string 1 who))
      (circe-display-server-message "Usage: /MSG <who> <what>")))
  (when what
    (let ((buf (circe-query-auto-query-buffer who)))
      (if buf
          (with-current-buffer buf
            (circe-command-SAY what)
            (lui-add-input what))
        (with-current-buffer (circe-server-last-active-buffer)
          (irc-send-PRIVMSG (circe-server-process)
                            who what)
          (circe-display 'circe-format-self-message
                         :target who
                         :body what))))))

(defun circe-command-NAMES (&optional channel)
  "List the names of the current channel or CHANNEL."
  (interactive)
  (let ((target (when channel
                  (string-trim channel))))
    (when (or (not target)
              (equal target ""))
      (setq target circe-chat-target))
    (if (not target)
        (circe-display-server-message "No target for current buffer")
      (irc-send-NAMES (circe-server-process)
                      target))))

(defun circe-command-NICK (newnick)
  "Change nick to NEWNICK."
  (interactive "sNew nick: ")
  (let ((newnick (string-trim newnick)))
    (irc-send-NICK (circe-server-process) newnick)))

(defun circe-command-PART (reason)
  "Part the current channel because of REASON."
  (interactive "sReason: ")
  (if (not circe-chat-target)
      (circe-display-server-message "No target for current buffer")
    (irc-send-PART (circe-server-process)
                   circe-chat-target
                   (if (equal "" reason)
                       circe-default-part-message
                     reason))))

(defun circe-command-PING (target)
  "Send a CTCP PING request to TARGET."
  (interactive "sWho: ")
  (let ((target (string-trim target)))
    (irc-send-ctcp (circe-server-process)
                   target
                   "PING" (format "%s" (float-time)))))

(defun circe-command-QUERY (arg)
  "Open a query with WHO."
  ;; Eventually, this should probably be just the same as
  ;; circe-command-MSG
  (interactive "sQuery with: ")
  (let* (who what)
    (if (string-match "\\`\\s-*\\(\\S-+\\)\\s-\\(\\s-*\\S-.*\\)\\'" arg)
        (setq who (match-string 1 arg)
              what (match-string 2 arg))
      (setq who (string-trim arg)))
    (when (string= who "")
      (circe-display-server-message "Usage: /query <nick> [something to say]"))
    (pop-to-buffer
     (circe-server-get-or-create-chat-buffer who 'circe-query-mode))
    (when what
      (circe-command-SAY what)
      (lui-add-input what))))

(defun circe-command-QUIT (reason)
  "Quit the current server giving REASON."
  (interactive "sReason: ")
  (with-circe-server-buffer
    (setq circe-server-inhibit-auto-reconnect-p t)
    (irc-send-QUIT (circe-server-process)
                   (if (equal "" reason)
                       circe-default-quit-message
                     reason))))

(defun circe-command-QUOTE (line)
  "Send LINE verbatim to the server."
  (interactive "Line: ")
  (irc-send-raw (circe-server-process) line)
  (with-current-buffer (circe-server-last-active-buffer)
    (circe-display-server-message (format "Sent to server: %s"
                                  line))))

(defun circe-command-SAY (line)
  "Say LINE to the current target."
  (interactive "sSay: ")
  (if (not circe-chat-target)
      (circe-display-server-message "No target for current buffer")
    (dolist (line (circe--split-line line))
      (circe-display 'circe-format-self-say
                     :body line
                     :nick (circe-nick))
      (irc-send-PRIVMSG (circe-server-process)
                        circe-chat-target
                        ;; Some IRC servers give an error if there is
                        ;; no text at all.
                        (if (string= line "")
                            " "
                          line)))))

(defun circe--split-line (longline)
  "Splits LONGLINE into smaller components.

IRC silently truncates long lines. This splits a long line into
parts that each are not longer than `circe-split-line-length'."
  (if (< (length longline)
         circe-split-line-length)
      (list longline)
    (with-temp-buffer
      (insert longline)
      (let ((fill-column circe-split-line-length))
        (fill-region (point-min) (point-max)
                     nil t))
      (split-string (buffer-string) "\n"))))

(defun circe-command-SV (&optional ignored)
  "Tell the current channel about your client and Emacs version.

Arguments are IGNORED."
  (interactive)
  (circe-command-SAY (format (concat "I'm using Circe version %s "
                                     "with %s %s (of %s)")
                             (circe--version)
                             "GNU Emacs"
                             emacs-version
                             (format-time-string "%Y-%m-%d"
                                                 emacs-build-time))))

(defun circe-command-TOPIC (channel &optional newtopic)
  "Change the topic of CHANNEL to NEWTOPIC."
  (interactive "sChannel: \nsNew topic: ")
  (when (string-match "^\\s-*$" channel)
    (setq channel nil))
  (when (and channel
             (not newtopic)
             (string-match "^\\s-*\\(\\S-+\\)\\( \\(.*\\)\\)?" channel))
    (setq newtopic (match-string 3 channel)
          channel (match-string 1 channel)))
  (cond
   ((and channel newtopic)
    (irc-send-TOPIC (circe-server-process) channel newtopic))
   (channel
    (irc-send-TOPIC (circe-server-process) channel))
   (circe-chat-target
    (irc-send-TOPIC (circe-server-process) circe-chat-target))
   (t
    (circe-display-server-message "No channel given, and no default target."))))

(defun circe-command-UNFOOL (line)
  "Remove the entry LINE from `circe-fool-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (setq circe-fool-list (delete regex circe-fool-list))
        (circe-display-server-message (format "Assuming %s is not a fool anymore"
                                      regex))))
     (t
      (circe-display-server-message
       "No one is not a fool anymore? UNFOOL requires one argument")))))

(defun circe-command-UNIGNORE (line)
  "Remove the entry LINE from `circe-ignore-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (setq circe-ignore-list (delete regex circe-ignore-list))
        (circe-display-server-message (format "Ignore list forgot about %s"
                                      regex))))
     (t
      (circe-display-server-message
       "Who do you want to unignore? UNIGNORE requires one argument")))))

(defun circe-command-WHOAMI (&optional ignored)
  "Request WHOIS information about yourself.

Arguments are IGNORED."
  (interactive)
  (irc-send-WHOIS (circe-server-process)
                  (circe-nick)))

(defun circe-command-WHOIS (whom)
  "Request WHOIS information about WHOM."
  (interactive "sWhois: ")
  (let* ((whom-server-name (split-string whom))
         (whom (car whom-server-name))
         (server-or-name (cadr whom-server-name)))
    (irc-send-WHOIS (circe-server-process) whom server-or-name)))

(defun circe-command-WHOWAS (whom)
  "Request WHOWAS information about WHOM."
  (interactive "sWhois: ")
  (let ((whom (string-trim whom)))
    (irc-send-WHOWAS (circe-server-process) whom)))

(defun circe-command-WL (&optional split)
  "Show the people who left in a netsplit.
Without any arguments, shows shows the current netsplits and how
many people are missing. With an argument SPLIT, which must be a
number, it shows the missing people due to that split."
  (let ((circe-netsplit-list (with-circe-server-buffer
                               circe-netsplit-list)))
    (if (or (not split)
            (and (stringp split)
                 (string= split "")))
        (if (null circe-netsplit-list)
            (circe-display-server-message "No net split at the moment")
          (let ((n 0))
            (dolist (entry circe-netsplit-list)
              (circe-display-server-message (format "(%d) Missing %d people due to %s"
                                            n
                                            (hash-table-count (nth 3 entry))
                                            (car entry)))
              (setq n (+ n 1)))))
      (let* ((index (if (numberp split)
                        split
                      (string-to-number split)))
             (entry (nth index circe-netsplit-list)))
        (if (not entry)
            (circe-display-server-message (format "No split number %s - use /WL to see a list"
                                          split))
          (let ((missing nil))
            (maphash (lambda (_key value)
                       (setq missing (cons value missing)))
                     (nth 3 entry))
            (circe-display-server-message
             (format "Missing people due to %s: %s"
                     (car entry)
                     (mapconcat 'identity
                                (sort missing
                                      (lambda (a b)
                                        (string< (downcase a)
                                                 (downcase b))))
                                ", ")))))))))

;;;;;;;;;;;;;;;;;;;;;;;;
;;; Display Handlers ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defun circe-display-ignore (_nick _userhost _command &rest _args)
  "Don't show a this message.

NICK and USERHOST are the originator of COMMAND which had ARGS as
arguments."
  'noop)

(circe-set-display-handler "317" 'circe-display-317)
(defun circe-display-317 (_sender ignored _numeric _target nick
                                  idletime &optional signon-time body)
  "Show a 317 numeric (RPL_WHOISIDLE).

Arguments are either of the two:

:<server> 317 <ournick> <nick> <idle> :seconds idle
:<server> 317 <ournick> <nick> <idle> <signon> :seconds idle, signon time"
  (with-current-buffer (circe-server-last-active-buffer)
    (let ((seconds-idle (string-to-number idletime))
          (signon-time (when body
                         (string-to-number signon-time))))
      (if signon-time
          (circe-display 'circe-format-server-whois-idle-with-signon
                         :whois-nick nick
                         :idle-seconds seconds-idle
                         :idle-duration (circe-duration-string seconds-idle)
                         :signon-time signon-time
                         :signon-date (current-time-string
                                       (seconds-to-time signon-time))
                         :signon-ago (circe-duration-string (- (float-time)
                                                               signon-time)))
        (circe-display 'circe-format-server-whois-idle
                       :whois-nick nick
                       :idle-seconds seconds-idle
                       :idle-duration (circe-duration-string seconds-idle))))))

(circe-set-display-handler "329" 'circe-display-329)
(defun circe-display-329 (_server ignored _numeric _target channel timestamp)
  "Show a 329 numeric (RPL_CREATIONTIME)."
  (with-current-buffer (or (circe-server-get-chat-buffer channel)
                           (circe-server-last-active-buffer))
    (let ((creation-time (string-to-number timestamp)))
      (circe-display 'circe-format-server-channel-creation-time
                     :channel channel
                     :date (current-time-string
                            (seconds-to-time creation-time))
                     :ago (circe-duration-string (- (float-time)
                                                    creation-time))))))

(circe-set-display-handler "333" 'circe-display-333)
(defun circe-display-333 (_server ignored _numeric target
                                  channel setter topic-time)
  "Show a 333 numeric (RPL_TOPICWHOTIME).

Arguments are either of the two:

:<server> 333 <target> <channel> <nick> 1434996762
:<server> 333 <target> <channel> <nick>!<user>@<host> 1434996803"
  (let ((channel-buffer (circe-server-get-chat-buffer channel))
        (topic-time (string-to-number topic-time)))
    (with-current-buffer (or channel-buffer
                             (circe-server-last-active-buffer))
      (circe-display (if channel-buffer
                         'circe-format-server-topic-time
                       'circe-format-server-topic-time-for-channel)
                     :nick target
                     :channel channel
                     :setter (irc-userstring-nick setter)
                     :setter-userhost (or (irc-userstring-userhost setter)
                                          "(unknown)")
                     :topic-time topic-time
                     :topic-date (current-time-string
                                  (seconds-to-time topic-time))
                     :topic-ago (circe-duration-string (- (float-time)
                                                          topic-time))))))

(circe-set-display-handler "AUTHENTICATE" 'circe-display-ignore)
(circe-set-display-handler "CAP" 'circe-display-ignore)
(circe-set-display-handler "conn.connected" 'circe-display-ignore)
(circe-set-display-handler "conn.disconnected" 'circe-display-ignore)

(circe-set-display-handler "irc.ctcp" 'circe-display-ignore)
(circe-set-display-handler "irc.ctcpreply" 'circe-display-ignore)

(circe-set-display-handler "irc.ctcp.ACTION" 'circe-display-ctcp-action)
(defun circe-display-ctcp-action (nick userhost _command target text)
  "Show an ACTION."
  (cond
   ;; Query
   ((circe-server-my-nick-p target)
    (let ((query-buffer (circe-query-auto-query-buffer nick)))
      (with-current-buffer (or query-buffer
                               (circe-server-last-active-buffer))
        (circe-display (if query-buffer
                           'circe-format-action
                         'circe-format-message-action)
                       :nick nick
                       :userhost (or userhost "server")
                       :body text))))
   ;; Channel
   (t
    (with-current-buffer (circe-server-get-or-create-chat-buffer
                          target 'circe-channel-mode)
      (circe-lurker-display-active nick userhost)
      (circe-display 'circe-format-action
                     :nick nick
                     :userhost (or userhost "server")
                     :body text)))))

(circe-set-display-handler "irc.ctcp.CLIENTINFO" 'circe-display-ctcp)

(circe-set-display-handler "irc.ctcp.PING" 'circe-display-ctcp-ping)
(defun circe-display-ctcp-ping (nick userhost _command target text)
  "Show a CTCP PING request."
  (with-current-buffer (circe-server-last-active-buffer)
    (circe-display 'circe-format-server-ctcp-ping
                   :nick nick
                   :userhost (or userhost "server")
                   :target target
                   :body (or text "")
                   :ago (let ((time (when text
				      (string-to-number text))))
                          (if time
                              (format "%.2f seconds" (- (float-time) time))
                            "unknown seconds")))))

(circe-set-display-handler "irc.ctcpreply.PING" 'circe-display-ctcp-ping-reply)
(defun circe-display-ctcp-ping-reply (nick userhost _command target text)
  "Show a CTCP PING reply."
  (with-current-buffer (circe-server-last-active-buffer)
    (circe-display 'circe-format-server-ctcp-ping-reply
                   :nick nick
                   :userhost (or userhost "server")
                   :target target
                   :body text
                   :ago (let ((time (string-to-number text)))
                          (if time
                              (format "%.2f seconds" (- (float-time) time))
                            "unknown seconds")))))

(circe-set-display-handler "irc.ctcp.SOURCE" 'circe-display-ctcp)
(circe-set-display-handler "irc.ctcp.TIME" 'circe-display-ctcp)
(circe-set-display-handler "irc.ctcp.VERSION" 'circe-display-ctcp)
(defun circe-display-ctcp (nick userhost command target text)
  "Show a CTCP request that does not require special handling."
  (with-current-buffer (circe-server-last-active-buffer)
    (circe-display 'circe-format-server-ctcp
                   :nick nick
                   :userhost (or userhost "server")
                   :target target
                   :command (substring command 9)
                   :body (or text ""))))

(circe-set-display-handler "irc.registered" 'circe-display-ignore)

(circe-set-display-handler "JOIN" 'circe-display-JOIN)
(defun circe-display-JOIN (nick userhost _command channel
                                &optional accountname realname)
  "Show a JOIN message.

The command receives an extra argument, the account name, on some
IRC servers."
  (let* ((accountname (if (equal accountname "*")
                          "(unauthenticated)"
                        accountname))
         (userinfo (if accountname
                       (format "%s, %s: %s" userhost accountname realname)
                     userhost))
         (split (circe--netsplit-join nick)))
    ;; First, update the channel
    (with-current-buffer (circe-server-get-or-create-chat-buffer
                          channel 'circe-channel-mode)
      (cond
       (split
        (let ((split-time (cadr split)))
          (when (< (+ split-time circe-netsplit-delay)
                   (float-time))
            (circe-display 'circe-format-server-netmerge
                           :split (car split)
                           :time (cadr split)
                           :date (current-time-string
                                  (seconds-to-time (cadr split)))
                           :ago (circe-duration-string
                                 (- (float-time) (cadr split)))))))
       ((and (circe-reduce-lurker-spam)
             (circe-lurker-rejoin-p nick circe-chat-target))
        (let* ((channel (irc-connection-channel (circe-server-process)
                                                circe-chat-target))
               (user (when channel
                       (irc-channel-recent-user channel nick)))
               (departed (when user
                           (irc-user-part-time user))))
          (circe-display 'circe-format-server-rejoin
                         :nick nick
                         :userhost (or userhost "server")
                         :accountname accountname
                         :realname realname
                         :userinfo userinfo
                         :departuretime departed
                         :departuredelta (circe-duration-string
                                          (- (float-time)
                                             departed)))))
       ((not (circe-reduce-lurker-spam))
        (circe-display 'circe-format-server-join
                       :nick nick
                       :userhost (or userhost "server")
                       :accountname accountname
                       :realname realname
                       :userinfo userinfo
                       :channel circe-chat-target))))
    ;; Next, a possible query buffer. We do this even when the message
    ;; should be ignored by a netsplit, since this can't flood.
    (let ((buf (circe-server-get-chat-buffer nick)))
      (when buf
        (with-current-buffer buf
          (circe-display 'circe-format-server-join-in-channel
                         :nick nick
                         :userhost (or userhost "server")
                         :accountname accountname
                         :realname realname
                         :userinfo userinfo
                         :channel circe-chat-target))))))

(circe-set-display-handler "MODE" 'circe-display-MODE)
(defun circe-display-MODE (setter userhost _command target &rest modes)
  "Show a MODE message."
  (with-current-buffer (or (circe-server-get-chat-buffer target)
                           (circe-server-last-active-buffer))
    (circe-display 'circe-format-server-mode-change
                   :setter setter
                   :userhost (or userhost "server")
                   :target target
                   :change (mapconcat #'identity modes " "))))

(circe-set-display-handler "NICK" 'circe-display-NICK)
(defun circe-display-NICK (old-nick userhost _command new-nick)
  "Show a nick change."
  (if (circe-server-my-nick-p new-nick)
      (dolist (buf (cons (or circe-server-buffer
                             (current-buffer))
                         (circe-server-chat-buffers)))
        (with-current-buffer buf
          (circe-display 'circe-format-server-nick-change-self
                         :old-nick old-nick
                         :userhost (or userhost "server")
                         :new-nick new-nick)))
    (let ((query-buffer (circe-server-get-chat-buffer old-nick)))
      (when query-buffer
        (with-current-buffer query-buffer
          (circe-server-rename-chat-buffer old-nick new-nick)
          (circe-display 'circe-format-server-nick-change
                         :old-nick old-nick
                         :new-nick new-nick
                         :userhost (or userhost "server")))))
    (dolist (buf (circe-user-channels new-nick))
      (with-current-buffer buf
        (cond
         ((and (circe-reduce-lurker-spam)
               (circe-lurker-p new-nick))
          nil)
         ((circe-channel-user-nick-regain-p old-nick new-nick)
          (circe-display 'circe-format-server-nick-regain
                         :old-nick old-nick
                         :new-nick new-nick
                         :userhost (or userhost "server")))
         (t
          (circe-display 'circe-format-server-nick-change
                         :old-nick old-nick
                         :new-nick new-nick
                         :userhost (or userhost "server"))))))))

(circe-set-display-handler "nickserv.identified" 'circe-display-ignore)

;; NOTICE is also used to encode CTCP replies. irc.el will send
;; irc.notice events for NOTICEs without CTCP replies, so we show
;; that, not the raw notice.
(circe-set-display-handler "NOTICE" 'circe-display-ignore)
(circe-set-display-handler "irc.notice" 'circe-display-NOTICE)
(defun circe-display-NOTICE (nick userhost _command target text)
  "Show a NOTICE message."
  (cond
   ((not userhost)
    (with-current-buffer (circe-server-last-active-buffer)
      (circe-display 'circe-format-server-notice
                     :server nick
                     :body text)))
   ((circe-server-my-nick-p target)
    (with-current-buffer (or (circe-server-get-chat-buffer nick)
                             (circe-server-last-active-buffer))
      (circe-display 'circe-format-notice
                     :nick nick
                     :userhost (or userhost "server")
                     :body text)))
   (t
    (with-current-buffer (or (circe-server-get-chat-buffer target)
                             (circe-server-last-active-buffer))
      (circe-display 'circe-format-notice
                     :nick nick
                     :userhost (or userhost "server")
                     :body text)))))

(circe-set-display-handler "PART" 'circe-display-PART)
(defun circe-display-PART (nick userhost _command channel &optional reason)
  "Show a PART message."
  (with-current-buffer (or (circe-server-get-chat-buffer channel)
                           (circe-server-last-active-buffer))
    (when (or (not circe-chat-target)
              (not (circe-lurker-p nick)))
      (circe-display 'circe-format-server-part
                     :nick nick
                     :userhost (or userhost "server")
                     :channel channel
                     :reason (or reason "[No reason given]")))))

(circe-set-display-handler "PING" 'circe-display-ignore)
(circe-set-display-handler "PONG" 'circe-display-ignore)

;; PRIVMSG is also used to encode CTCP requests. irc.el will send
;; irc.message events for PRIVMSGs without CTCP messages, so we show
;; that, not the raw message.
(circe-set-display-handler "PRIVMSG" 'circe-display-ignore)
(circe-set-display-handler "irc.message" 'circe-display-PRIVMSG)
(defun circe-display-PRIVMSG (nick userhost _command target text)
  "Show a PRIVMSG message."
  (cond
   ((circe-server-my-nick-p target)
    (let ((buf (circe-query-auto-query-buffer nick)))
      (if buf
          (with-current-buffer buf
            (circe-display 'circe-format-say
                           :nick nick
                           :userhost (or userhost "server")
                           :body text))
        (with-current-buffer (circe-server-last-active-buffer)
          (circe-display 'circe-format-message
                         :nick nick
                         :userhost (or userhost "server")
                         :body text)))))
   (t
    (with-current-buffer (circe-server-get-or-create-chat-buffer
                          target 'circe-channel-mode)
      (circe-lurker-display-active nick userhost)
      (circe-display 'circe-format-say
                     :nick nick
                     :userhost (or userhost "server")
                     :body text)))))

(circe-set-display-handler "TOPIC" 'circe-display-topic)
(defun circe-display-topic (nick userhost _command channel new-topic)
  "Show a TOPIC change."
  (with-current-buffer (circe-server-get-or-create-chat-buffer
                        channel 'circe-channel-mode)
    (let* ((channel-obj (irc-connection-channel (circe-server-process)
                                                channel))
           (old-topic (or (when channel
                            (irc-channel-last-topic channel-obj))
                          "")))
      (circe-display 'circe-format-server-topic
                     :nick nick
                     :userhost (or userhost "server")
                     :channel channel
                     :new-topic new-topic
                     :old-topic old-topic
                     :topic-diff (circe--topic-diff old-topic new-topic)))))

(defun circe--topic-diff (old new)
  "Return a colored topic diff between OLD and NEW."
  (mapconcat (lambda (elt)
               (cond
                ((eq '+ (car elt))
                 (let ((s (cadr elt)))
                   (add-face-text-property 0 (length s)
                                           'circe-topic-diff-new-face nil s)
                   s))
                ((eq '- (car elt))
                 (let ((s (cadr elt)))
                   (add-face-text-property 0 (length s)
                                           'circe-topic-diff-removed-face nil s)
                   s))
                (t
                 (cadr elt))))
             (lcs-unified-diff (circe--topic-diff-split old)
                               (circe--topic-diff-split new)
                               'string=)
             ""))

(defun circe--topic-diff-split (str)
  "Split STR into a list of components.
The list consists of words and spaces."
  (let ((lis nil))
    (with-temp-buffer
      (insert str)
      (goto-char (point-min))
      (while (< (point)
                (point-max))
        (if (or (looking-at "\\w+\\W*")
                (looking-at ".\\s-*"))
            (progn
              (setq lis (cons (match-string 0)
                              lis))
              (replace-match ""))
          (error "Can't happen"))))
    (nreverse lis)))

(circe-set-display-handler "channel.quit" 'circe-display-channel-quit)
(defun circe-display-channel-quit (nick userhost _command channel
                                        &optional reason)
  "Show a QUIT message."
  (let ((split (circe--netsplit-quit reason nick)))
    (with-current-buffer (circe-server-get-or-create-chat-buffer
                          channel 'circe-channel-mode)
      (cond
       (split
        (when (< (+ split circe-netsplit-delay)
                 (float-time))
          (circe-display 'circe-format-server-netsplit
                         :split reason)))
       ((not (circe-lurker-p nick))
        (circe-display 'circe-format-server-quit-channel
                       :nick nick
                       :userhost (or userhost "server")
                       :channel channel
                       :reason (or reason "[no reason given]")))))))

(circe-set-display-handler "QUIT" 'circe-display-QUIT)
(defun circe-display-QUIT (nick userhost _command &optional reason)
  "Show a QUIT message.

Channel quits are shown already, so just show quits in queries."
  (let ((buf (circe-server-get-chat-buffer nick)))
    (when buf
      (with-current-buffer buf
        (circe-display 'circe-format-server-quit
                       :nick nick
                       :userhost (or userhost "server")
                       :reason (or reason "[no reason given]"))))))

(defvar circe-netsplit-list nil
  "A list of recorded netsplits.
Every item is a list with four elements:
- The quit message for this split.
- The time when last we heard about a join in this split
- The time when last we heard about a quit in this split
- A hash table noting which nicks did leave")
(make-variable-buffer-local 'circe-netsplit-list)

(defun circe--netsplit-join (nick)
  "Search for NICK in the netsplit lists.
This either returns a pair whose car is the quit message of this
split, and the cadr the time we last heard anything of the split
of that user. If the NICK isn't split, this returns nil."
  (with-circe-server-buffer
    (catch 'return
      (dolist (entry circe-netsplit-list)
        (let ((table (nth 3 entry)))
          (when (gethash nick table)
            (let ((name (nth 0 entry))
                  (time (nth 1 entry)))
              (remhash nick table)
              (when (= 0 (hash-table-count table))
                (setq circe-netsplit-list
                      (delq entry circe-netsplit-list)))
              (setcar (cdr entry)
                      (float-time))
              (throw 'return (list name time))))))
      nil)))

(defun circe--netsplit-quit (reason nick)
  "If REASON indicates a netsplit, mark NICK as splitted.
This either returns the time when last we heard about this split,
or nil when this isn't a split."
  (when (circe--netsplit-reason-p reason)
    (with-circe-server-buffer
      (let ((entry (assoc reason circe-netsplit-list)))
        (if entry
            (let ((time (nth 2 entry))
                  (table (nth 3 entry)))
              (setcar (cddr entry)
                      (float-time))
              (puthash nick nick table)
              time)
          ;; New split!
          (let ((table (make-hash-table :test 'equal)))
            (puthash nick nick table)
            (setq circe-netsplit-list
                  (cons (list reason 0 (float-time) table)
                        circe-netsplit-list))
            0))))))

(defun circe--netsplit-reason-p (reason)
  "Return non-nil if REASON is the quit message of a netsplit.
This is true when it contains exactly two hosts, with a single
space in between them. The hosts must include at least one dot,
and must not include colons or slashes (else they might be
URLs). (Thanks to irssi for this criteria list)"
  (if (string-match "^[^ :/]+\\.[^ :/]* [^ :/]+\\.[^ :/]*$"
                    reason)
      t
    nil))

(let ((simple-format-specifiers
       '(("INVITE" active "Invite: {origin} invites you to {1}")
         ("KICK" 0 "Kick: {1} kicked by {origin}: {2}")
         ("ERROR" active "Error: {0-}")
         ("001" server "{1}")
         ("002" server "{1}")
         ("003" server "{1}")
         ("004" server "{1-}")
         ("005" server "{1-}")
         ;; IRCnet: * Please wait while we process your connection.
         ("020" server "{0-}")
         ;; IRCnet
         ("042" server "Your unique ID is {1}")
         ("200" active "{1-}")
         ("201" active "{1-}")
         ("203" active "{1-}")
         ("204" active "{1-}")
         ("205" active "{1-}")
         ("206" active "{1-}")
         ("207" active "{1-}")
         ("208" active "{1-}")
         ("209" active "{1-}")
         ("211" active "{1-}")
         ("212" active "{1-}")
         ("219" active "{1-}")
         ("221" active "User mode: {1-}")
         ("234" active "Service: {1-}")
         ("235" active "{1-}")
         ("242" active "{1}")
         ("243" active "{1-}")
         ("250" server "{1}")
         ("251" server "{1}")
         ("252" server "{1-}")
         ("253" server "{1-}")
         ("254" server "{1-}")
         ("255" server "{1}")
         ("256" active "{1-}")
         ("257" active "{1}")
         ("258" active "{1}")
         ("259" active "{1}")
         ("261" active "{1-}")
         ("262" active "{1-}")
         ("263" active "{1-}")
         ("265" server "{1-}")
         ("266" server "{1-}")
         ;; This is returned on both WHOIS and PRIVMSG. It
         ;; should go to the active window for the former, and
         ;; the query window for the latter. Oh well.
         ("301" active "User away: {1}")
         ("302" active "User hosts: {1}")
         ("303" active "Users online: {1}")
         ("305" active "{1}")
         ("306" active "{1}")
         ("307" active "{1-}")
         ;; Coldfront: 310 <nick> is available for help.
         ("310" active "{1-}")
         ("311" active "{1} is {2}@{3} ({5})")
         ("312" active "{1} is on {2} ({3})")
         ("313" active "{1} {2}")
         ("314" active "{1} was {2}@{3} ({5})")
         ("315" active "{2}")
         ("318" active "{2}")
         ("319" active "{1} is on {2}")
         ("320" active "{1-}")
         ("322" active "{1-}")
         ("323" active "{1-}")
         ("324" 1 "Channel mode for {1}: {2-}")
         ("325" 1 "Unique operator on {1} is {2}")
         ("328" 1 "Channel homepage for {1}: {2-}")
         ("330" active "{1} is logged in as {2}")
         ("331" 1 "No topic for {1} set")
         ("332" 1 "Topic for {1}: {2}")
         ("341" active "Inviting {1} to {2}")
         ("346" 1 "Invite mask: {2}")
         ("347" 1 "{2}")
         ("348" 1 "Except mask: {2}")
         ("349" 1 "{2}")
         ("351" active "{1-}")
         ("352" active "{5} ({2}@{3}) in {1} on {4}: {6-}")
         ("353" 2 "Names: {3}")
         ("364" active "{1-}")
         ("365" active "{1-}")
         ("366" 1 "{2}")
         ("367" 1 "Ban mask: {2}")
         ("368" 1 "{2}")
         ("369" active "{1} {2}")
         ("371" active "{1}")
         ("372" server "{1}")
         ("374" active "{1}")
         ("375" server "{1}")
         ("376" server "{1}")
         ("378" active "{1-}")
         ("381" active "{1}")
         ("382" active "{1-}")
         ("391" active "Time on {1}: {2}")
         ("401" active "No such nick: {1}")
         ("402" active "No such server: {1}")
         ("403" active "No such channel: {1}")
         ("404" 1 "Can not send to channel {1}")
         ("405" active "Can not join {1}: {2}")
         ("406" active "{1-}")
         ("407" active "{1-}")
         ("408" active "No such service: {1}")
         ("422" active "{1}")
         ("432" active "Erroneous nick name: {1}")
         ("433" active "Nick name in use: {1}")
         ("437" active "Nick/channel is temporarily unavailable: {1}")
         ("441" 2 "User not on channel: {1}")
         ("442" active "You are not on {1}")
         ("443" 2 "User {1} is already on channel {2}")
         ;; Coldfront: 451 * :You have not registered
         ("451" active "{1-}")
         ("467" 1 "{2}")
         ("470" 1 "{1} made you join {2}: {3-}")
         ("471" 1 "{2}")
         ("472" active "{1-}")
         ("473" active "{1-}")
         ("474" active "{1-}")
         ("475" active "{1-}")
         ("476" active "{1-}")
         ("477" active "{1-}")
         ("481" 1 "{2-}")
         ("484" active "{1-}")
         ;; Coldfront: 671 <nick> is using a Secure Connection
         ("671" active "{1-}")
         ("728" 1 "Quiet mask: {3}")
         ("729" 1 "{3-}")
         ;; Freenode SASL auth
         ("900" active "SASL: {3-}")
         ("903" active "{1-}"))))
  (dolist (fmt simple-format-specifiers)
    (circe-set-display-handler (car fmt) (cdr fmt))))

(defun circe-set-message-target (command target)
  "Set the target of COMMAND to TARGET.

This can be used to change format-based display handlers more
easily."
  (let ((handler (circe-get-display-handler command)))
    (when (not (consp handler))
      (error "Handler of command %s is not a list" command))
    (setcar handler target)))

;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helper Functions ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defun circe--list-drop-right (list pattern)
  "Drop elements from the right of LIST that match PATTERN.

LIST should be a list of strings, and PATTERN is used as a
regular expression."
  (let ((list (reverse list)))
    (while (and list
                (string-match pattern (car list)))
      (setq list (cdr list)))
    (nreverse list)))

(defun circe--nick-next (oldnick)
  "Return a new nick to try for OLDNICK."
  (cond
   ;; If the nick ends with -+, replace those with _
   ((string-match "^\\(.*[^-]\\)\\(-+\\)$" oldnick)
    (concat (match-string 1 oldnick)
            (make-string (- (match-end 2)
                            (match-beginning 2))
                         ?_)))
   ;; If the nick is 9 chars long, take prefix and rotate.
   ((>= (length oldnick)
        9)
    (when (string-match "^\\(.*[^-_]\\)[-_]*$" oldnick)
      (let ((nick (match-string 1 oldnick)))
        (concat (substring nick 1)
                (string (aref nick 0))))))
   ;; If the nick ends with _+ replace those with - and add one
   ((string-match "^\\(.*[^_]\\)\\(_+\\)$" oldnick)
    (concat (match-string 1 oldnick)
            (make-string (- (match-end 2)
                            (match-beginning 2))
                         ?-)
            "-"))
   ;; Else, just append -
   (t
    (concat oldnick "-"))))

(defun circe-duration-string (duration)
  "Return a description of a DURATION in seconds."
  (let ((parts `((,(* 12 30 24 60 60) "year")
                 (,(* 30 24 60 60) "month")
                 (,(* 24 60 60) "day")
                 (,(* 60 60) "hour")
                 (60 "minute")
                 (1 "second")))
        (duration (round duration))
        (result nil))
    (dolist (part parts)
      (let* ((seconds-per-part (car part))
             (description (cadr part))
             (count (/ duration seconds-per-part)))
        (when (not (zerop count))
          (setq result (cons (format "%d %s%s"
                                     count description
                                     (if (= count 1) "" "s"))
                             result)))
        (setq duration (- duration (* count seconds-per-part)))))
    (if result
        (mapconcat #'identity
                   (nreverse result)
                   " ")
      "a moment")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deprecated functions and variables

(define-obsolete-function-alias 'circe-server-nick 'circe-nick
  "Circe 2.0")

(define-obsolete-function-alias 'circe-server-message
  'circe-display-server-message
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-networks 'circe-network-defaults
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-name 'circe-host
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-service 'circe-port
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-network 'circe-network
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-ip-family 'circe-ip-family
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-nick 'circe-nick
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-user 'circe-user
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-pass 'circe-pass
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-realname 'circe-realname
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-use-tls 'circe-use-tls
  "Circe 2.0")

(define-obsolete-variable-alias 'circe-server-auto-join-channels
  'circe-channels
  "Circe 2.0")

(provide 'circe)
;;; circe.el ends here
