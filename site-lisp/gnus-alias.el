;;; gnus-alias.el --- an alternative to gnus-posting-styles

;; This file is not part of Emacs

;; Copyright (C) 2001 by Joseph L. Casadonte Jr.
;; Author:          Joe Casadonte <emacs@northbound-train.com>
;; Maintainer:      Mark A. Hershberger <mah@everybody.org>
;; Created:         September 08, 2001
;; Keywords:        personality, identity, news, mail, gnus
;; Version:         1.6
;; Latest Version:  http://github.com/hexmode/gnus-alias/

;; COPYRIGHT NOTICE

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;;  gnus-alias provides a simple mechanism to switch Identities when
;;  using a message-mode or a message-mode derived mode.  An Identity
;;  is one or more of the following elements:
;;
;;  o From - sets the From header (i.e. the sender)
;;  o Organization - sets the Organization header (a common, optional header)
;;  o Extra headers - a list of arbitrary header to set (e.g. X-Archive: no)
;;  o Body - adds text to the body of the message (just above the signature)
;;  o Signature - adds a signature to the message
;;
;;  All of this is also provided by the standard `gnus-posting-styles'
;;  (which see).  Whereas Posting Styles let you set these up
;;  initially, though, gnus-alias lets you change them on the fly
;;  easily, too (in this regard gnus-alias is much like gnus-pers,
;;  upon which it is based; see 'Credits' below).  With a simple
;;  command (`gnus-alias-select-identity') you can select & replace
;;  one Identity with another.
;;
;;  There are other significant differences between gnus-alias and
;;  Posting Styles, too.  gnus-alias has a much simpler interface/API
;;  for selecting an initial Identity automatically.  Posting Styles is
;;  much more flexible (especially in that you can build up an
;;  "Identity" piece by piece), but with that flexibility can come
;;  some complexity.
;;
;;  Other advantages to using gnus-alias:
;;
;;  o the ability to switch Identities in a message buffer
;;  o can access original message to help determine Identity of the
;;    followup/reply message
;;  o can act on a forwarded message as if it were a message being
;;    replied to
;;  o can start a new message with a given Identity pre-selected
;;
;;  It is possible to use both Posting Styles and gnus-alias, with
;;  `gnus-posting-styles' setup occuring before gnus-alias selects an
;;  Identity.  That much co-ordination is beyond my attention span,
;;  though; I just use this package.
;;
;;  There may also be some overlap between this package and
;;  `message-alternative-emails' (which see), though I'm not exactly
;;  sure what that really does.

;;; Installation:
;;
;;  Put this file on your Emacs-Lisp load path, then add one of the
;;  following to your ~/.emacs startup file.  You can load gnus-alias
;;  every time you start Emacs:
;;
;;     (require 'gnus-alias)
;;     (gnus-alias-init)
;;
;;  or you can load the package via autoload:
;;
;;     (autoload 'gnus-alias-determine-identity "gnus-alias" "" t)
;;     (add-hook 'message-setup-hook 'gnus-alias-determine-identity)
;;
;;  To add a directory to your load-path, use something like the following:
;;
;;      (add-to-list 'load-path (expand-file-name "/some/load/path"))

;;; Usage:
;;
;;  To get gnus-alias to determine your Identity automatically, you
;;  don't need to call anything directly, really.  You set up your
;;  Identities by customizing `gnus-alias-identity-alist' and then
;;  either set up `gnus-alias-identity-rules' to automatically choose
;;  an Identity given the message context.  You should also set up
;;  `gnus-alias-default-identity' to point to one of the Identities
;;  already set up, to be used when `gnus-alias-identity-rules' is
;;  empty, or when it isn't able to determine which Identity to use.
;;  Then, you must call `gnus-alias-init' at some point AFTER 'message'
;;  has been loaded.  This is best done in `message-load-hook':
;;
;;      (defun my-message-load-hook ()
;;        (gnus-alias-init))
;;
;;      (add-hook 'message-load-hook 'my-message-load-hook)
;;
;;  If you use message-x for tab-completion of names & newsgroups in
;;  the header, then you may also want gnus-alias to select an
;;  identity based on the current header values (possibly just
;;  changed), then add the following:
;;
;;      (defun my-message-load-hook ()
;;        (gnus-alias-init)
;;        (add-hook 'message-x-after-completion-functions
;;                  'gnus-alias-message-x-completion))
;;
;;  Anytime that message-x is used for completion, a new identity will
;;  be determined.
;;
;;  Switching Identities interactively is as easy as calling one of
;;  the following two functions:
;;  o `gnus-alias-use-identity' - pass in a valid Identity alias to be
;;    used in the current buffer.
;;  o `gnus-alias-select-identity' - will prompt you for an identity
;;    to use and then use it in the current buffer.
;;
;;  If you do either of them frequently, you can bind them to a key:
;;
;;      (defun my-message-load-hook ()
;;        (gnus-alias-init)
;;
;;        (define-key message-mode-map [(f10)]
;;          (function
;;           (lambda () "Set Identity to jcasadonte." (interactive)
;;             (gnus-alias-use-identity "JCasadonte"))))
;;
;;        (define-key message-mode-map [(f11)]
;;          'gnus-alias-select-identity)
;;        )
;;
;;      (add-hook 'message-load-hook 'my-message-load-hook)
;;
;;  This package also provides access to the original message's
;;  headers when forwarding news or email.  To use this, you must
;;  customize the variable `gnus-alias-allow-forward-as-reply'.  This
;;  will enable some advice for `message-setup' that makes it possible
;;  to access the original headers.
;;
;;; Customization:
;;
;;  The basic variables you'll want to customize are
;;  `gnus-alias-identity-alist', `gnus-alias-identity-rules' and
;;  `gnus-alias-default-identity' (all of which have extensive
;;  documentation).  If you'd like a menu of Identities to choose from
;;  take a look at `gnus-alias-add-identity-menu', and if you'd like a
;;  buttonized 'From' header, see `gnus-alias-use-buttonized-from'
;;  (coming soon).
;;
;;  To see all of the customization options, do one of the following:
;;
;;     M-x customize-group RET gnus-alias RET
;;
;;  or
;;
;;     M-x gnus-alias-customize RET
;;
;;  Both of them do the same thing.

;;; Known Bugs:
;;
;;  o When changing Identities, removing an Identity with a signature
;;    in a forwarded message, where the forwarded message is below the
;;    signature, will also remove the forwarded message.  This might be
;;    fixed at some point.
;;  o In `gnus-alias-identity-alist', if a string value for one of the
;;    elements happens to coincide with an actual file name, it will
;;    be treated as a file even though 'string' was selected.  This
;;    might be fixed at some point.
;;  o It's possible for a loop to be created when having one Identity
;;    refer to another.  This might be fixed at some point.

;;; To Do (maybe never):
;;
;;  o reply-using et al
;;  o Fix abbrev cache (or get rid of it)
;;  o Add 'prompt to uknown-rule
;;  o add buttonized from (or get rid of it)
;;  o [ ] New Mail only
;;    [ ] New News only
;;    [ ] Reply/Follow-up only
;;    [ ] Forward only
;;  o fix known bugs
;;  o `message-narrow-to-headers' doesn't work on reply-buffer; maybe
;;    a gnus-alias-narrow-to-headers function
;;  o Could have GADI functions return a new 'split' to be fed back
;;    into GADI
;;  o GADI functions could return an Identity instead of just t or nil
;;  o re-apply identity
;;  o better fault tolerance in string match substitution (in rules)
;;  o add Group Params to aliases?

;;; Credits:
;;
;;  The idea for gnus-alias is conceptually based on gnus-pers.el by
;;  BrYan P. Johnson <bilko@onebabyzebra.com>.  Although some of the
;;  API remains close to gnus-pers, it has been completely re-written.
;;  Major differences between gnus-pers and gnus-alias can be found in
;;  the Change History log (see below).

;;; Comments:
;;
;;  Any comments, suggestions, bug reports or upgrade requests are welcome.
;;  Please send them to Joe Casadonte (emacs@northbound-train.com).
;;
;;  This version of gnus-alias was developed and tested with NTEmacs
;;  21.1.1 under Windows 2000.  Please, let me know if it works with
;;  other OS and versions of Emacs.

;;; Change Log:
;;
;;  see http://www.northbound-train.com/emacs/gnus-alias.log

;;; **************************************************************************
;;; **************************************************************************
;;; **************************************************************************
;;; **************************************************************************
;;; **************************************************************************
;;; Code:
(eval-when-compile
  ;; silence the old byte-compiler
  (defvar byte-compile-dynamic)
  (set (make-local-variable 'byte-compile-dynamic) t)

  (require 'message)

  ;; variables/functions from other packages
  (defvar message-reply-buffer)
  (defvar message-signature-separator)
  (defvar message-mode-map)
  )

;;; **************************************************************************
;;; ***** customization routines
;;; **************************************************************************
(defgroup gnus-alias nil
  "Alternate identity mechanism for Gnus."
  :group 'message)

;; ---------------------------------------------------------------------------
(defun gnus-alias-customize ()
  "Customization of the group 'gnus-alias'."
  (interactive)
  (customize-group "gnus-alias"))

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-identity-alist ()
  "Association list of Identities.

Each Identity in the alist has an Alias as its key.  The Identity
itself is composed of one or more of the following elements:

 o Refers to - allows one Identity to refer to another for part of
   its definition.  The reference Identity is applied first, and then
   the current Identity is overlaid on top of the first one.
 o From - sets the 'From' header, designating who the mail or post is
   from.  It must be a valid format; examples:
   - emacs@northbound-train.com
   - \"Joe Casadonte\" <emacs@northbound-train.com>
 o Organization - sets the 'Organization' header (a common, optional
   header).  Note: this may be overridden by your ISP.
 o Extra headers - a list of arbitrary headers to set (e.g. X-Archive:
   no).  This can be used to setup any header you'd like)
 o Body - adds text to the body of the message (just above the signature)
 o Signature - adds a signature to the message

The value for each element can be a string (which will be used as-is),
a function that is expected to return a string, or a variable (also a
string).  In addition, 'Body' & 'Signature' can also be the name of a
file, the contents of which will be used (you guessed it, as a string)."
  :type '(repeat
          (cons :tag "Identity"
                (string :tag "Alias")
                (list :tag "Dossier - please fill in one or more of the following"
                      (choice :tag "-Refers to" (string) (function) (variable))
                      (choice :tag "-From" (string :tag "String (e.g. \"First Last\" <email@address.com>)") (function) (variable))
                      (choice :tag "-Organization" (string) (function) (variable))
                      (repeat :tag "-Extra Headers"
                              (cons
                               (choice :tag "Header (no ':')" (string) (function) (variable))
                               (choice :tag "Value" (string) (function) (variable))))
                      (choice :tag "-Body" (string) (function) (variable) (file))
                      (choice :tag "-Signature" (string) (function) (variable) (file))
                      )))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-default-identity ""
  "Identity to use if none is chosen via `gnus-alias-identity-rules'.

Set this to the Alias of one of your defined Identities."
  :type 'string
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-overlay-identities nil
  "Overlays one Identity on top of another (instead of replacing it).

If non-nil, the old Identity is not removed when applying a new
Identity.  This allows for a manual `gnus-posting-styles' effect of
building up an Identity in layers.  So, if the old Identity had an
Organization defined but the new one did not, overlaying the old one
with the new one will result in the message having an Organization
defined.

If nil, the old Identity is completely removed before the new one is
added.  So in the previous example, overlaying the old Identity with
the new one will result in the message NOT having an Organization
defined."
  :type 'boolean
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-identity-rules nil
  "Rules used to choose Identity whenever a new message is created.

The rules are evaluated to determine which Identity to use when
creating a new message (new email or article, a reply to an email or
article or follow-up to an article or a forwarded email or article).
Rules are individually evaluated by `gnus-alias-determine-identity' in
the order that they are defined in, until one of them results in an
Identity being chosen.  If this results in an invalid Identity being
chosen, what happens next is determined by
`gnus-alias-unknown-identity-rule' \(which see). If no valid Identites
are found,`gnus-alias-default-identity' is used instead.

Each rule has a NAME/DESCRIPTION, which is used mainly as
documentation for yourself, and is referenced when debugging is turned
on.  Then, one of two RULE METHODs are used:

o Header Match - matches a REGEXP (regular expression) to the value in
  the header field identified by HEADER SYMBOL (which is either a key
  into a list of headers defined by `gnus-alias-lookup-abbrev-alist',
  or the name of an actual header).  When replying to an email or
  following up to a post, both the original set of headers and the new
  message's headers are available to be matched against (with a new
  message, only the current set is available).  HEADER SET determines
  which set of headers are matched against.  Options are: current,
  previous or both (previous, and if that's empty, current).

o Function - this method is simply a function that returns either nil
  or non-nil.  Non-nil indicates that a match of whatever kind was
  achieved, and the specified Identity should be used.  This function
  can literally be anything you want from Message's `message-news-p'
  to a custom function (e.g. `my-identity-fn').

If the regexp matches or the function returns non-nil, the Identity
specified by IDENTITY is validated.  This can either be a key from
`gnus-alias-identity-alist' or a substitution scheme that results in
such a key (Header Match only).  Substitution is done just like in
normal regular expression processing, using \\\\D (where D is a number
corresponding to a sub-expression from the last match).

For example, given the following rule:

  NAME: Domain Match
  RULE METHOD: Header Match
    HEADER SYMBOL: to
    REGEXP: <\\\\(.+\\\\)@northbound-train.com
    HEADER SET: both
  IDENTITY: nt-\\\\1

Matching on \"CC: <emacs@northbound-train.com>\" would result in
the \"nt-emacs\" Identity being used.

See the Regular Expressions info node for more details on regexp
patterns and substitution:

    M-: (Info-goto-node \"(emacs)regexps\") RET"
  :type '(repeat
          (list :format "%v"
                (string :tag "Name/Description")
                (choice :tag "Rule Method"
                        (list :tag "Header Match"
                              (string :tag "Header Symbol")
                              (regexp :tag "Regexp")
                              (choice :tag "Header set"
                                      (const :tag "Current Headers only" current)
                                      (const :tag "Previous Headers only" previous)
                                      (const :tag "Previous Headers, then Current" both)))
                        (function :tag "Function"))
                (string :tag "Identity")
                ))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-unknown-identity-rule 'continue
  "Tells 'gnus-alias' what to do when it finds an unknown Identity.

If during the course of determining an Identity via
`gnus-alias-identity-rules' an Identity is chosen that
does not appear in `gnus-alias-identity-alist', this variable
determines what happens next.  Possible choices are:

  o error - generate an error and stop all processing
  o continue - ignore it and continue on, checking the next Identity rule
  o default - use the default Identity
  o identity - specify an Identity to use
  o function - call specified function with the unknown Identity,
    which should return a valid Identity

Regardless, logging occurs if debugging is on."
  :type '(choice :tag "Method"
                 (const :tag "Error" error)
                 (const :tag "Continue" continue)
                 (const :tag "Default" default)
                 (string :tag "Identity")
                 (function :tag "Function" ))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defvar gnus-alias-lookup-abbrev-cache (list)
  "Caches resolution of abbrev alist (is cleared when alist is reset).")

;; ...........................................................................
(defcustom gnus-alias-lookup-abbrev-alist '(("mail" "mailer-daemon postmaster uucp")
                                            ("to" "to cc apparently-to resent-to resent-cc")
                                            ("from" "from sender resent-from")
                                            ("any" "[from] [to]")
                                            ("newsgroup" "newsgroups")
                                            ("ngroupto" "[to] [newsgroup]"))
  "Alist of abbreviations allowed in `gnus-alias-identity-rules'.

SYMBOL is any mnemonic or abbreviation that makes sense for you.
HEADER LIST is a space-separated list of headers that will be used in
determining which Identity the new message should use.  You can refer
to a previously defined header list by putting its mnemonic in
square brackets in the new header list; see 'ngroupto' as an example.

This variable must be set/reset via Custom in order for changes to
take place without re-starting Emacs."
  :type '(repeat
          (list :format "%v"
                (string :tag "Symbol")
                (string :tag "Header list")))
  :set (lambda (sym val)
         (set-default sym val)
         (setq gnus-alias-lookup-abbrev-cache (list)))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-extra-header-pos-alist ' (("Gcc" "Bcc Fcc In-Reply-To Subject")
                                                ("Bcc" "Fcc In-Reply-To Subject")
                                                ("Fcc" "In-Reply-To Subject")
                                                ("Organization" "Date Gcc Bcc Fcc In-Reply-To Subject"))
  "Association list of Extra Header positions.

For the truly anal who want their headers in a prescribed order.  The
alist key is a Header and the value is a space-separated list of
headers that will be passed to `message-position-on-field' in order to
place the header/key properly.

\[Note: as far as I know, this is useful only to make the display look
the way you'd like it to.  I don't know of an RFC mandating the
positions of the headers that would normally be set via the Extra
Headers mechanism.  If there is such a creature, please let me know.]"
  :type '(repeat
          (list :format "%v"
                (string :tag "Header (no ':')")
                (string :tag "Position(s)")))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defadvice message-forward (around message-forward-with-reply-buffer)
  "Set `gnus-alias-reply-buffer' to message being forwarded."
  (let ((gnus-alias-reply-buffer (current-buffer)))
    ad-do-it))

;; ...........................................................................
(defcustom gnus-alias-allow-forward-as-reply nil
  "Allows access to original headers of a forwarded message.

Normally, when `message-forward' is called, no reply buffer is set up,
and consequently the previous headers can not be used to determine the
Identity of the forwarded message.  By setting this option to a
non-nil value, a piece of advice is enabled that allows access to the
headers of the forwarded message as if it were a message being replied
to.

This variable must be set/reset via Custom in order for changes to
take place without re-starting Emacs."
  :type 'boolean
  :set (lambda (sym val)
         (set-default sym val)
         (if val
             (ad-enable-advice 'message-forward
                               'around 'message-forward-with-reply-buffer)
           (ad-disable-advice 'message-forward
                              'around 'message-forward-with-reply-buffer))

         (ad-activate 'message-forward))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defadvice message-send-and-exit (around message-send-and-exit-special-user-mail-address)
  "Temporarily change the value of `user-mail-address' (maybe)."
  (let ((user-mail-address
         (save-restriction
           (message-narrow-to-headers)
           (message-fetch-field "From" t))))
    ad-do-it))

;; ...........................................................................
(defcustom gnus-alias-override-user-mail-address nil
  "Allow your Return-Path to be set properly.

Normally, even though you can successfully change your identity with
gnus-alias, not all headers are changed.  Return-Path: is typically set
from the value of `user-mail-address'.  Setting this variable to a
non-nil value will activate some defadvice for
`message-send-and-exit', essentially giving `user-mail-address' a
temporary value equal to your From: address.

Note: some mail servers will not allow this; there's nothing that can
be done about that except to contact the SysAdmin (good luck!)."
  :type 'boolean
  :set (lambda (sym val)
         (set-default sym val)
         (if val
             (ad-enable-advice 'message-send-and-exit
                               'around 'message-send-and-exit-special-user-mail-address)
           (ad-disable-advice 'message-send-and-exit
                              'around 'message-send-and-exit-special-user-mail-address))

         (ad-activate 'message-send-and-exit))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-point-position 'empty-header-or-body
  "After an Identity is used, where should point be moved to?

After a call to `gnus-alias-use-identity', where should point be left?

Choices are:
  o empty-header-or-body - leave point on first empty header, or
    start of body if there are no empty headers
  o empty-header-or-sig - leave point on first empty header, or
    start of signature if there are no empty headers
  o start-of-body - leave point at the start of body
  o start-of-sig - leave point at the start of signature, or the ned
    of body if there is no signature"
  :type '(choice
          (const :tag "First Empty Header or Start of Body" empty-header-or-body)
          (const :tag "First Empty Header or Start of Signature" empty-header-or-sig)
          (const :tag "Start of Body" start-of-body)
          (const :tag "Start of Signature" start-of-sig))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-add-identity-menu t
  "Controls whether or not an Identity menu is added to Message mode.

If non-nil, an Identity menu is added to Message mode, from which you
can choose which Identity to use.  If nil, no menu is added.

This variable must be set/reset via Custom in order for changes to
take place without re-starting Emacs."
  :type '(boolean)
  :set (lambda (sym val)
         (set-default sym val)
         (if gnus-alias-add-identity-menu
             ;; add hook if not there already
             (add-hook 'message-mode-hook 'gnus-alias-create-identity-menu)
           ;; remove hook if it's there
           (remove-hook 'message-mode-hook 'gnus-alias-create-identity-menu)))
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-use-buttonized-from t
  "Controls whether or not the 'From' header is buttonized.

If non-nil, the 'From' header becomes a button that you can click on
to bring up an Identity menu to select from.  If nil, then it's not."
  :type 'boolean
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-verbosity 0
  "Level of verbosity -- 0 is least, 9 is most.

  0 = no output
  1 = message output only
  2-9 = ever-increasing amounts of debug output

See also `gnus-alias-debug-buffer-name'."
  :type 'integer
  :group 'gnus-alias)

;; ...........................................................................
(defcustom gnus-alias-debug-buffer-name "*gnus-alias debug*"
  "Name of debug buffer (see `gnus-alias-verbosity')."
  :type 'string
  :group 'gnus-alias)

;; ---------------------------------------------------------------------------
(defcustom gnus-alias-load-hook nil
  "Hook run when 'gnus-alias' is first loaded."
  :type 'hook
  :group 'gnus-alias)

;;; **************************************************************************
;;; ***** version related routines
;;; **************************************************************************
(defconst gnus-alias-version
  "$Revision: 1.4 $"
  "Version number for 'gnus-alias' package.")

;; ---------------------------------------------------------------------------
(defun gnus-alias-version-number ()
  "Return 'gnus-alias' version number."
  (let ((version))
    (save-match-data
  (string-match "[0123456789.]+" gnus-alias-version)
      (setq version (match-string 0 gnus-alias-version)))
    version))

;; ---------------------------------------------------------------------------
(defun gnus-alias-version ()
  "Display 'gnus-alias' version."
  (interactive)
  (message "gnus-alias version <%s>." (gnus-alias-version-number)))

;;; **************************************************************************
;;; ***** internal variables
;;; **************************************************************************
(defvar gnus-alias-current-identity nil
  "[INTERNAL] The last Identity used.

This is needed to clean up the message when switching Identities.")

;; make this buffer-local always
(make-variable-buffer-local 'gnus-alias-current-identity)

;;; **************************************************************************
(defvar gnus-alias-reply-buffer nil
  "[INTERNAL] Used to make forward act like reply.

If for some reason you want to set this variable, please do so in a
`let' form, so that its value is cleared when you're done doing whatever
it is you're doing.  Also, NEVER make this variable buffer-local via
`make-variable-buffer-local'; it will no longer work as desired.")

;;; **************************************************************************
;;; ***** interactive functions
;;; **************************************************************************
;;;###autoload
(defun gnus-alias-init ()
  "Add gnus-alias call to message mode hook."
  (interactive)
  (add-hook 'message-setup-hook 'gnus-alias-determine-identity))

;;; **************************************************************************
;;;###autoload
(defun gnus-alias-select-identity ()
  "Prompt user for an identity and use it."
  (interactive)
  (gnus-alias-use-identity (gnus-alias-identity-prompt)))

;;; **************************************************************************
;;;###autoload
(defun gnus-alias-use-identity (&optional identity)
  "Use an Identity defined in `gnus-alias-identity-alist'.

IDENTITY must be a valid entry in `gnus-alias-identity-alist',
otherwise an error will occur (NOTE: this behavior has changed
significantly from that found in 'gnus-pers').

If called interactively with no identity, user will be prompted for
one."
  (interactive)
  (gnus-alias-ensure-message-mode)

  ;; do we need to prompt for identity?
  (when (and (not identity) (interactive-p))
    (setq identity (gnus-alias-identity-prompt)))

  ;; call internal function
  (gnus-alias-use-identity-1 identity)

  ;; where to leave point?
  (cond
   ;; .........................
   ;; EMPTY HEADER OR BODY
   ((equal gnus-alias-point-position 'empty-header-or-body)
    (gnus-alias-goto-first-empty-header t))

   ;; .........................
   ;; EMPTY HEADER OR SIGNATURE
   ((equal gnus-alias-point-position 'empty-header-or-sig)
    (gnus-alias-goto-first-empty-header nil))

   ;; .........................
   ;; START OF SIGNATURE
   ((equal gnus-alias-point-position 'start-of-sig)
    (gnus-alias-goto-sig))

   ;; .........................
   ;; START OF BODY (default)
   (t (message-goto-body))
   ))

;;; **************************************************************************
;;; ***** internal functions
;;; **************************************************************************
(defun gnus-alias-ensure-message-mode ()
  "Assert that the current buffer is a message buffer."
  (when (not (derived-mode-p 'message-mode))
    (gnus-alias-error "Must be in a mode derived from `message-mode'.")))

;;; **************************************************************************
;;;###autoload
(defun gnus-alias-determine-identity (&optional lookup-only)
  "Function that chooses a Identity based on message headers.

See `gnus-alias-identity-rules' for more information.  Optional
LOOKUP-ONLY is a boolean that, when non-nil, says to determine the
Identity, but don't actually use it (just return it)"
  (let ((rules-list gnus-alias-identity-rules)
        (message-reply-buffer (or gnus-alias-reply-buffer
                                  message-reply-buffer))
        current-choice first-elem class regexp which-headers
        header header-list header-value potential-identity identity
        rule-name)

    ;; debugging
    (gnus-alias-dump-headers "[GADI] ")

    ;; loop thru all electric headers until one matches
    (while (and (not identity) rules-list)
      ;; get next potential
      (setq current-choice (car rules-list))
      (setq rule-name (car current-choice))
      (setq current-choice (cdr current-choice))
      (gnus-alias-debug 2 "[GADI] Evaluating <%s>\n" rule-name)

      ;; get first elem
      (setq first-elem (car current-choice))

      ;; what is it, list or function?
      (cond
       ;; .........................
       ;; a function
       ((functionp first-elem)
        ;; call function; if it returns non-nil, use the identity
        (when (funcall first-elem)
          (setq identity (cadr current-choice))
          ))

       ;; .........................
       ;; a list - class regexp orig-headers
       ((listp first-elem)
        (setq class (nth 0 first-elem)
              regexp (nth 1 first-elem)
              which-headers (nth 2 first-elem))

        ;; lookup header class
        (setq header-list (gnus-alias-resolve-alist-abbrev class))
        (when (not header-list)
          ;; assume that it itself is a header
          (setq header-list (list class)))

        ;; loop thru all header pieces
        (while (and (not identity) header-list)
          (setq header (car header-list))

          ;; which headers wanted?
          (cond
           ;; .........................
           ;; PREVIOUS
           ((equal which-headers 'previous)
            (setq header-value (message-fetch-reply-field header)))

           ;; .........................
           ;; BOTH
           ((equal which-headers 'both)
            (setq header-value (message-fetch-reply-field header))
            (when (not header-value)
              (setq header-value (message-fetch-field header))))

           ;; .........................
           ;; CURRENT (default)
           (t (setq header-value (message-fetch-field header)))
           )

          ;; does it match??
          (save-match-data
            (when (and header-value
                       (string-match regexp header-value))
              (setq potential-identity (cadr current-choice))

              ;; check for & process substitutions
              (let ((orig-match-data (match-data))
                    potential-match-data match-num newtext)
                (while (string-match "\\\\\\([0-9]\\)" potential-identity)
                  (setq potential-match-data (match-data))
                  (setq match-num (string-to-number (match-string 1 potential-identity)))

                  ;; could use better (any) fault tolerance here
                  ;; (w/r/t looking up a match that doesn't exit)
                  (set-match-data orig-match-data)
                  (setq newtext (match-string match-num header-value))

                  (set-match-data potential-match-data)
                  (setq potential-identity
                        (replace-match newtext nil nil
                        potential-identity))
                  ))

              ;; we got the real deal, now
              (setq identity potential-identity)
              ))

          (setq header-list (cdr header-list))
          ))

       ;; .........................
       ;; unknown - ignore
       (t))

      ;; if we found anything, find out if it's valid
      (when (and identity
                 (not (assoc-string
                       identity gnus-alias-identity-alist t)))

        (gnus-alias-debug 2 "[GADI] Unknown Identity found:\n")
        (gnus-alias-debug 2 "       Rule: <%s>\n" rule-name)
        (gnus-alias-debug 2 "       Identity: <%s>\n" identity)
        (gnus-alias-debug 2 "       Action: <%s>\n"
                          (if (symbolp gnus-alias-unknown-identity-rule)
                              (symbol-name gnus-alias-unknown-identity-rule)
                            gnus-alias-unknown-identity-rule))

        (cond
         ;; .........................
         ;; ERROR
         ((equal gnus-alias-unknown-identity-rule 'error)
          (gnus-alias-error "Unknown Identity: <%s>" identity))

         ;; .........................
         ;; DEFAULT
         ((equal gnus-alias-unknown-identity-rule 'default)
          (setq identity gnus-alias-default-identity))

         ;; .........................
         ;; IDENTITY
         ((stringp gnus-alias-unknown-identity-rule)
          (setq identity gnus-alias-unknown-identity-rule))

         ;; .........................
         ;; FUNCTION
         ((functionp gnus-alias-unknown-identity-rule)
          (setq identity (funcall gnus-alias-unknown-identity-rule
                                  identity)))

         ;; .........................
         ;; CONTINUE (assumed)
         (t (setq identity nil))
        ))

      ;; get next element
      (setq rules-list (cdr rules-list))
      )

    ;; if no identity selected, try default
    (when (and (not identity) gnus-alias-default-identity)
      (setq identity gnus-alias-default-identity))

    ;; use it (unless asked not to)
    (unless (or lookup-only (not identity))
      (gnus-alias-debug 1 "Using the <%s> Identity" identity)
      (gnus-alias-use-identity identity))

    ;; return it
    identity))

;;; **************************************************************************
;;;###autoload
(defun gnus-alias-message-x-completion (which-header)
  "Can be used to select identifies in new mail after tab-completion.

WHICH-HEADER should be set to the header that completion was just
performed on.

When tab-completion is performed in the To: header, a new identity
will be selected according to the rules set up in
`gnus-alias-identity-alist' (which see).

This particular function expects an argument, and as such should only
be used with the `message-x-after-completion-functions'hook:

  (add-hook 'message-x-after-completion-functions
            'gnus-alias-message-x-completion)

This should be place in the `message-load-hook' (see gnus-alias file
for details).  If such an argument is not needed in the current
context, `gnus-alias-determine-identity' may be used directly in a hook."
  (when (string= which-header "to")
    (gnus-alias-determine-identity)))

;;; **************************************************************************
(defun gnus-alias-resolve-alist-abbrev (abbreviation &optional seen)
  "Return a list of headers from `gnus-alias-lookup-abbrev-alist'.

ABBREVIATION is used as a key into `gnus-alias-lookup-abbrev-alist'.
Function returns a list of strings of the headers in the alist, or nil
if ABBREVIATION is not in the alist.

SEEN is a variable used in recursive calls to this function, and
should not be set by an external caller."

  (let ((rv (assoc-string abbreviation gnus-alias-lookup-abbrev-cache t))
        (first-in (not seen))
        header-list lookup elem match recurse)

    (when (not rv)
      (setq rv (list))

      ;; lookup abbreviation
      (setq lookup (assoc-string abbreviation gnus-alias-lookup-abbrev-alist t))
      (when lookup
        (setq header-list (split-string (cadr lookup))))

      ;; prevent recursion -- first time thru only
      (when (not seen)
        (setq seen (list (cons (concat "[" abbreviation "]") t))))

      ;; keep looping till we're done
      (while header-list
        ;; pop one off
        (setq elem (car header-list))

        ;; is it a reference to another one?
        (save-match-data
          (if (string-match "^\\[\\(.+\\)\\]$" elem)
              ;; prevent recursion
              (when (not (assoc elem seen))
                ;; append it to seen list
                (setq seen (append (list (cons elem t)) seen))
                ;; recurse in to look it up
                (setq recurse
                      (gnus-alias-resolve-alist-abbrev (match-string 1 elem) seen))

                (setq rv (nconc rv (car recurse)))
                (setq seen (cdr recurse)))

            ;; just add it to the list
            (setq rv (nconc rv (list elem)))))

        ;; next!
        (setq header-list (cdr header-list)))

      ;; store it in the cache for next time
;;    (setq gnus-alias-lookup-abbrev-cache
;;          ;; maybe get rid of CONS?
;;          (append (list abbreviation rv)
;;                  gnus-alias-lookup-abbrev-cache))
      )

    ;; return whatever we found (or nil) plus 'seen', maybe
    (if first-in rv (cons rv seen))
    ))

;;; **************************************************************************
(defun gnus-alias-identity-prompt ()
  "Prompt user for an identity."
  (gnus-alias-ensure-message-mode)
  (let ((completion-ignore-case t)
        rv)
    (setq rv (car
              (assoc-string
               (completing-read "Identity: " gnus-alias-identity-alist nil t)
               gnus-alias-identity-alist t)))

    ;; return it
    rv))

;;; **************************************************************************
(defsubst gnus-alias-get-something (ID N)
  "Return the Nth something from ID."
  (let ((rv (nth N ID)))
    (if (and (stringp rv) (= (length rv) 0)) nil rv)))

;;; **************************************************************************
(defun gnus-alias-get-reference (ID)
  "Return the FROM portion of ID."
  (gnus-alias-get-something ID 1))

;;; **************************************************************************
(defun gnus-alias-get-from (ID)
  "Return the FROM portion of ID."
  (gnus-alias-get-something ID 2))

;;; **************************************************************************
(defun gnus-alias-get-org (ID)
  "Return the ORGANIZATION portion of ID."
  (gnus-alias-get-something ID 3))

;;; **************************************************************************
(defun gnus-alias-get-extras (ID)
  "Return the EXTRA HEADERS portion of ID."
  (gnus-alias-get-something ID 4))

;;; **************************************************************************
(defun gnus-alias-get-body (ID)
  "Return the BODY portion of ID."
  (gnus-alias-get-something ID 5))

;;; **************************************************************************
(defun gnus-alias-get-sig (ID)
  "Return the SIGNATURE portion of ID."
  (gnus-alias-get-something ID 6))

;;; **************************************************************************
(defun gnus-alias-position-on-field (header)
  "Lookup afters value for HEADER and call `message-position-on-field'.

If HEADER is in `gnus-alias-extra-header-pos-alist', look up its value
and pass into `message-position-on-field' as the value for AFTERS.  If
it's not, simply position the field at the end of the header list (not
the beginning as is normal)."
  (let ((afters (car-safe
                 (cdr-safe
                  (assoc-string header gnus-alias-extra-header-pos-alist t)
                  ))))

    ;; adjust it a little
    (setq afters
          (if afters
              ;; just split string into parts
              (split-string afters)
            ;; goto end of header, backup a line, use that header
            (message-goto-eoh)
            (forward-line -1)
            (save-match-data
              (re-search-forward "^\\(.+\\):")
              (list (match-string-no-properties 1)))
            ))

    ;; call message-position-on-field with whatever we've got
    (apply 'message-position-on-field header afters)))

;;; **************************************************************************
(defun gnus-alias-use-identity-1 (identity &optional suppress-error)
  "Use an Identity defined in `gnus-alias-identity-alist'.

IDENTITY must be a valid entry in `gnus-alias-identity-alist',
otherwise an error will occur (NOTE: this behavior has changed
significantly from that found in 'gnus-pers').

SUPPRESS-ERROR will cause the function to silently fail under the
above circumstances rather then generate an error."
  ;; lookup Identity
  (let ((ID (assoc-string identity gnus-alias-identity-alist t))
        reference from org extras body sig extras-list current-extra
        extra-hdr extra-val afters)
    ;; is IDENTITY valid?
    (if (not ID)
        (when (not suppress-error)
            (gnus-alias-error "Unknown Identity: <%s>" identity))

      ;; remove old identity unless we're overlaying
      (unless gnus-alias-overlay-identities
        (gnus-alias-remove-identity gnus-alias-current-identity)
        (setq gnus-alias-current-identity nil))

      ;; get ID elements
      (setq reference (gnus-alias-get-reference ID)
            from (gnus-alias-get-from ID)
            org (gnus-alias-get-org ID)
            extras (gnus-alias-get-extras ID)
            body (gnus-alias-get-body ID)
            sig (gnus-alias-get-sig ID))

      ;; lay down reference Identity maybe
      (when reference
        (gnus-alias-use-identity-1 (gnus-alias-get-value reference)))

      (save-restriction
	(goto-char (point-min))
	(save-match-data
	  (when (re-search-forward "<#\\(mml\\|part\\)" nil t)
	    (narrow-to-region (point-min) (match-beginning 0))))

      ;; add From maybe
      (when from
        (gnus-alias-remove-header "From")

        (message-position-on-field "From")
        (insert (gnus-alias-get-value from))

        (when gnus-alias-use-buttonized-from
          ;; do something with widgets here
;;        (gnus-alias-buttonize-from)
          ))

      ;; add Organization maybe
      (when org
        (gnus-alias-remove-header "Organization")

        (gnus-alias-position-on-field "Organization")
        (insert (gnus-alias-get-value org)))

      ;; add extra headers maybe
      (when extras
        (setq extras-list extras)
        (while extras-list
          (setq current-extra (car extras-list))
          (setq extra-hdr (gnus-alias-get-value (car current-extra)))
          (setq extra-val (gnus-alias-get-value (cdr current-extra)))

          (gnus-alias-remove-header extra-hdr)

          (gnus-alias-position-on-field extra-hdr)
          (insert extra-val)

          (setq extras-list (cdr extras-list))
          ))

      ;; add body maybe
      (when body
        (gnus-alias-remove-current-body)
        (gnus-alias-goto-sig)
        (insert (gnus-alias-get-value body))
        (unless (bolp) (insert "\n")))

      ;; remove old signature
      (gnus-alias-remove-sig)

      ;; add signature maybe
      (when sig
        (goto-char (point-max))
        (unless (bolp) (insert "\n"))
        (insert "-- \n")
        (insert (gnus-alias-get-value sig))))

      ;; remember last Identity used
      (setq gnus-alias-current-identity identity)))

  ;; position at start of message
  (message-goto-body))

;;; **************************************************************************
(defun gnus-alias-get-value (element)
  "Determine type of ELEMENT and return value accordingly.

ELEMENT may be one of: File String Function Variable

If a File, return the contents of the file.
If a String, simply return that.
If a Function, call it and return value.
If a Variable, return it's value.
If none of the above, return \"\"."
  (cond
   ;; .........................
   ;; some kind of STRING
   ((stringp element)
    (cond

     ;; .........................
     ;; FILE
     ((and (> (length element) 0)
           (file-exists-p element))
      (with-temp-buffer
        (insert-file-contents element nil)
        (buffer-string)))

     ;; .........................
     ;; STRING
     (t element)))

   ;; .........................
   ;; FUNCTION
   ((functionp element)
    (funcall element))

   ;; .........................
   ;; VARIABLE
   ((boundp element)
    (symbol-value element))

   ;; .........................
   ;; Don't know
   (t "")))

;;; **************************************************************************
(defun gnus-alias-remove-identity (identity)
  "Remove all traces of IDENTITY from the current message.

IDENTITY must be a valid key in `gnus-alias-identity-alist' or nil,
otherwise an error will occur.

This function depends on the fact that the definition of IDENTITY has
not changed, and any functions used for defining values return the
same value as it did previously (this latter piece is necessary only
for the header name in Extra Headers and the text auto-inserted into
the Body).  If such is not the case, chaos will ensue (i.e. I'm not
responsible for the subsequent mess)."
  (gnus-alias-ensure-message-mode)

  ;; only proceed when non-nil
  (when identity
    (let ((ID (assoc-string identity gnus-alias-identity-alist t))
          from org extras body sig extras-list current-extra extra-hdr)
      (if (not ID)
          (gnus-alias-error "Unknown Identity: <%s>" identity)

        (setq from (gnus-alias-get-from ID)
              org (gnus-alias-get-org ID)
              extras (gnus-alias-get-extras ID)
              body (gnus-alias-get-body ID)
              sig (gnus-alias-get-sig ID))

	(save-restriction
	  (goto-char (point-min))
	  (save-match-data
	    (when (re-search-forward "<#\\(mml\\|part\\)" nil t)
	      (narrow-to-region (point-min) (match-beginning 0))))

          ;; remove From
          (when from (gnus-alias-remove-header "From"))

          ;; remove Organization maybe
          (when org (gnus-alias-remove-header "Organization"))

          ;; remove extra headers maybe
          (when extras
            (setq extras-list extras)
            (while extras-list
              (setq current-extra (car extras-list))
              (setq extra-hdr (gnus-alias-get-value (car current-extra)))
              (gnus-alias-remove-header extra-hdr)
              (setq extras-list (cdr extras-list))
              ))

          ;; remove body maybe
          (when body (gnus-alias-remove-current-body))

          ;; remove signature maybe
          (when sig (gnus-alias-remove-sig))
          )))))

;;; **************************************************************************
(defun gnus-alias-remove-header (tag)
  "Find and remove TAG from headers."
  (message-position-on-field tag)
  (let ((beg) (end))
    (beginning-of-line)
    (setq beg (point))
    (end-of-line)
    (setq end (+ (point) 1))

    (delete-region beg end)))

;;; **************************************************************************
(defun gnus-alias-remove-sig ()
  "Find and remove signature."
  (gnus-alias-goto-sig)
  (delete-region (point) (point-max)))

;;; **************************************************************************
(defun gnus-alias-remove-current-body ()
  "Find and remove current Identity's body."
  (when gnus-alias-current-identity
    (let* ((ID (assoc-string gnus-alias-current-identity
                                  gnus-alias-identity-alist t))
           (current-body (when ID (gnus-alias-get-body ID)))
           start end)
      ;; remove it if there's something to remove
      (when current-body
        (save-restriction

          ;; find body and narrow to it
          (message-goto-eoh)
          (forward-line 1)
          (setq start (point))

          (gnus-alias-goto-sig)
          (setq end (point))

          (narrow-to-region start end)

          ;; search for current Identity's body text
          (goto-char (point-min))
          (save-match-data
            (when (re-search-forward
                   (regexp-quote (gnus-alias-get-value current-body)) nil t)
              (replace-match "")))
          ))
    )))

;;; **************************************************************************
(defun gnus-alias-goto-sig ()
  "Goto beginning of signature or end of buffer."
  (goto-char (point-min))
  (when (save-match-data
	  (re-search-forward message-signature-separator nil 'move))
    (beginning-of-line)))

;;; **************************************************************************
(defun gnus-alias-goto-first-empty-header (or-body)
  "Move point to first empty header.

If there are no empty headers, the value of OR-BODY will determine
whether point is move to the start of body or sig."
  (let ((found))
    (save-restriction
      (message-narrow-to-headers)
      (save-match-data
        (setq found (re-search-forward "^.+:\\s-*$" nil t))))
    (when (not found)
      (if or-body
          (message-goto-body)
        (gnus-alias-goto-sig)))))

;;; **************************************************************************
;;; ***** debug functions
;;; **************************************************************************
(defun gnus-alias-debug (level fmt &rest args)
  "Debug function.

LEVEL = level of message (1 = message, 2-9 = debug message)
FMT   = string format passed to `message' or `insert'
ARGS  = arguments for FMT"
  (when (> gnus-alias-verbosity 0)
    (if (= level 1)
        (progn
          ;; log the message is debugging is on then display message
          (gnus-alias-debug 2 (concat "[MSG] " fmt "\n") args)
          (apply 'message fmt args))
      ;; insert message into debug buffer
      (save-excursion
        (set-buffer (get-buffer-create gnus-alias-debug-buffer-name))
        (insert (apply 'format fmt args)))
      )))

;;; **************************************************************************
(defun gnus-alias-error (fmt &rest args)
  "Log the error and then call `error'.

FMT is the format of the error message, and ARGS are its arguments."
  ;; log the error and then call into `error'
  (gnus-alias-debug 2 (concat "[ERROR] " fmt "\n") args)
  (apply 'error fmt args))

;;; **************************************************************************
(defun gnus-alias-dump-headers (&optional prefix)
  "Dump headers to debug buffer (verbosity >= 4).

PREFIX is an optional prefeix to each header block."
  (interactive)
  (when (>= gnus-alias-verbosity 4)
    (let (tmp)
      (when (and message-reply-buffer
                   (buffer-name message-reply-buffer))
        (save-excursion
          (save-restriction
            (set-buffer message-reply-buffer)
            (message-narrow-to-headers)
            (setq tmp (buffer-string))
            (gnus-alias-debug 4 "%sOld Headers\n%s===========\n%s\n\n" prefix prefix tmp))))

      (save-excursion
        (save-restriction
          (message-narrow-to-headers)
          (setq tmp (buffer-string))
          (gnus-alias-debug 4 "%sNew Headers\n%s===========\n%s\n\n" prefix prefix tmp)))
        )))

;;; **************************************************************************
;;; ***** menu & button functions
;;; **************************************************************************
;; (defun gnus-alias-buttonize-from ()
;;   (goto-char (point-min))
;;   (search-forward "From:")
;;   (beginning-of-line)
;;   (let ((from (point))
;;          (to (+ (point) 5)))
;;  (gnus-article-add-button from to 'gnus-alias-popup-menu nil)))

;; (defun gnus-alias-popup-menu ()
;;   (interactive)
;;   (ding))

;; ;;; **************************************************************************
;; (defun gnus-alias-popup-menu (args)
;;   "Personality popup menu."
;;   (interactive "e")
;;   (let ((response (get-popup-menu-response
;;                 `("Personalities"
;;                   :filter gnus-alias-menu-filter
;;                   "Select a personality to insert:"
;;                   "-----"
;;                   ))))
;;     (set-buffer (event-buffer event))
;;     (goto-char (event-point event))
;;     (funcall (event-function response) (event-object response))))

;;; **************************************************************************
(defun gnus-alias-create-identity-menu ()
  "Add Identity menu in Message mode (see `gnus-alias-add-identity-menu')."

  (easy-menu-define message-mode-menu message-mode-map "Identity Menu."
    '("Identity"
      :filter gnus-alias-identity-menu-filter)))

;;; **************************************************************************
(defun gnus-alias-identity-menu-filter (menu)
  "Create Identity MENU from all defined Identities."
  (let ((identities gnus-alias-identity-alist)
        alias)
    (mapcar (lambda (identity)
              (setq alias (car identity))
              (vector alias `(gnus-alias-use-identity ,alias) t))
            identities)))

;;; **************************************************************************
;;; ***** we're done
;;; **************************************************************************
(provide 'gnus-alias)
(run-hooks 'gnus-alias-load-hook)

;;; gnus-alias.el ends here
;;; **************************************************************************
;;;; *****  EOF  *****  EOF  *****  EOF  *****  EOF  *****  EOF  *************
