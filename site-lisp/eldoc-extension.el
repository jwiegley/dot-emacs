;;; eldoc-extension.el --- Some extension for eldoc

;; Filename: eldoc-extension.el
;; Description: Some extension for eldoc
;; Author: Andy Stewart <lazycat.manatee@gmail.com>
;; Maintainer: rubikitch <rubikitch@ruby-lang.org>
;; Time-stamp: <2010-05-04 18:13:43 rubikitch>
;; Copyright (C) 2008, 2009, Andy Stewart, all rights reserved.
;; Copyright (C) 2010, rubikitch, all rights reserved.
;; Created: 2008-12-07 21:44:29
;; Version: 0.2
;; URL: http://www.emacswiki.org/cgi-bin/wiki/download/eldoc-extension.el
;; Keywords: eldoc
;; Compatibility: GNU Emacs 23.0.60.1
;;
;; Features that might be required by this library:
;;
;; `eldoc'
;;

;;; This file is NOT part of GNU Emacs

;;; License
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; Some extension for eldoc
;;

;;; Commands:
;;
;; Below are complete command list:
;;
;;
;;; Customizable Options:
;;
;; Below are customizable option list:
;;

;;; Installation:
;;
;; Put eldoc-extension.el to your load-path.
;; The load-path is usually ~/elisp/.
;; It's set in your ~/.emacs like this:
;; (add-to-list 'load-path (expand-file-name "~/elisp"))
;;
;; And the following to your ~/.emacs startup file.
;;
;; (require 'eldoc-extension)
;;
;; No need more.


;;; Bug Report:
;;
;; If you have problem, send a bug report via M-x eldoc-extension-send-bug-report.
;; The step is:
;;  0) Setup mail in Emacs, the easiest way is:
;;       (setq user-mail-address "your@mail.address")
;;       (setq user-full-name "Your Full Name")
;;       (setq smtpmail-smtp-server "your.smtp.server.jp")
;;       (setq mail-user-agent 'message-user-agent)
;;       (setq message-send-mail-function 'message-smtpmail-send-it)
;;  1) Be sure to use the LATEST version of eldoc-extension.el.
;;  2) Enable debugger. M-x toggle-debug-on-error or (setq debug-on-error t)
;;  3) Use Lisp version instead of compiled one: (load "eldoc-extension.el")
;;  4) Do it!
;;  5) If you got an error, please do not close *Backtrace* buffer.
;;  6) M-x eldoc-extension-send-bug-report and M-x insert-buffer *Backtrace*
;;  7) Describe the bug using a precise recipe.
;;  8) Type C-c C-c to send.
;;  # If you are a Japanese, please write in Japanese:-)

;;; Change log:
;;
;; See http://www.rubyist.net/~rubikitch/gitlog/eldoc-extension.txt

;;; Acknowledgements:
;;
;;
;;

;;; TODO
;;
;;
;;

;;; Require
(require 'eldoc)

;;; Code:

(defun eldoc-argument-list (string)
  "Down case and fortify STRING for use with `eldoc-mode'."
  (propertize (downcase string)
              'face 'font-lock-variable-name-face))

;;; added in Emacs23 http://gist.github.com/369189
;;; removed from Emacs23 http://gist.github.com/369190
(defvar new-functions-from-emacs23
  '(abbrev--active-tables
    abbrev--before-point
    abbrev--check-chars
    abbrev--describe
    abbrev--write
    abbrev-get
    abbrev-insert
    abbrev-put
    abbrev-table-get
    abbrev-table-menu
    abbrev-table-p
    abbrev-table-put
    abort-if-file-too-large
    accelerate-menu
    activate-mark
    apply-partially
    apropos-library
    auto-compose-chars
    auto-composition-mode
    auto-encryption-mode
    background-color-at-point
    balance-windows-area
    beginning-of-visual-line
    bibtex-initialize
    bibtex-search-entry
    bookmark-jump-other-window
    browse-url-elinks
    browse-url-text-emacs
    browse-url-text-xterm
    bubbles
    buffer-face-mde
    buffer-face-set
    buffer-face-toggle
    Buffer-menu-isearch-buffers
    Buffer-menu-isearch-buffers-regexp
    Buffer-menu-marked-buffers
    buffer-swap-text
    bug-reference-mode
    bug-reference-prog-mode
    butterfly
    byte-compile-disable-warning
    byte-compile-enable-warning
    calendar-hebrew-list-yahrzeits
    canonicalize-coding-system-name
    capitalized-words-mode
    char-code-property-description
    char-resolve-modifiers
    characterp
    charset-chars
    charset-description
    charset-dimension
    charset-id
    charset-id-internal
    charset-iso-final-char
    charset-plist
    charset-priority-list
    check-coding-systems-region
    check-declare-directory
    check-declare-file
    chmod
    clear-charset-maps
    clear-font-cache
    close-display-connection
    close-font
    coding-system-aliases
    coding-system-charset-list
    coding-system-from-name
    coding-system-priority-list
    complete-in-turn
    completion--do-completion
    completion--embedded-envvar-table
    completion--file-name-table
    completion--flush-all-sorted-completions
    completion--insert-strings
    completion--make-envvar-table
    completion--merge-suffix
    completion--some
    completion--try-word-completion
    completion-all-completions
    completion-all-sorted-completions
    completion-basic-all-completions
    completion-basic-try-completion
    completion-boundaries
    completion-emacs21-all-completions
    completion-emacs21-try-completion
    completion-emacs22-all-completions
    completion-emacs22-try-completion
    completion-hilit-commonality
    completion-pcm--all-completions
    completion-pcm--filename-try-filter
    completion-pcm--find-all-completions
    completion-pcm--hilit-commonality
    completion-pcm--merge-completions
    completion-pcm--merge-try
    completion-pcm--pattern->regex
    completion-pcm--pattern->string
    completion-pcm--pattern-trivial-p
    completion-pcm--prepare-delim-re
    completion-pcm--string->pattern
    completion-pcm-all-completions
    completion-pcm-try-completion
    completion-table-dynamic
    completion-table-in-turn
    completion-table-with-context
    completion-table-with-predicate
    completion-table-with-terminator
    completion-try-completion
    compose-glyph-string
    compose-glyph-string-relative
    compose-gstring-for-graphic
    compose-gstring-for-terminal
    compose-gstring-for-variation-glyph
    composition-get-gstring
    confirm-nonexistent-file-or-buffer
    controlling-tty-p
    convert-define-charset-argument
    copyright-update-directory
    create-default-fontset
    custom-note-var-changed
    daemon-initialized
    daemonp
    dbus-call-method
    dbus-call-method-asynchronously
    dbus-get-unique-name
    dbus-handle-event
    dbus-method-error-internal
    dbus-method-return-internal
    dbus-register-method
    dbus-register-signal
    dbus-send-signal
    decode-composition-components
    decode-composition-rule
    default-indent-new-line
    define-char-code-property
    define-charset-alias
    define-charset-internal
    define-coding-system
    delete-other-windows-vertically
    delete-terminal
    dir-locals-collect-mode-variables
    dir-locals-collect-variables
    dir-locals-find-file
    dir-locals-get-class-variables
    dir-locals-read-from-file
    dir-locals-set-class-variables
    dir-locals-set-directory-class
    dired-do-async-shell-command
    dired-do-isearch
    dired-do-isearch-regexp
    dired-isearch-filenames
    dired-isearch-filenames-regexp
    dired-isearch-filenames-setup
    dirtrack-mode
    display-time-world
    doc-view-bookmark-jump
    doc-view-minor-mode
    doc-view-mode
    doc-view-mode-p
    dynamic-completion-table
    ebnf-find-style
    ecomplete-setup
    emacs-init-time
    emacs-uptime
    encode-composition-components
    encoded-kbd-decode-code-list
    encoded-kbd-iso2022-designation
    encoded-kbd-iso2022-single-shift
    encoded-kbd-last-key
    encoded-kbd-self-insert-big5
    encoded-kbd-self-insert-ccl
    encoded-kbd-self-insert-charset
    encoded-kbd-self-insert-iso2022-7bit
    encoded-kbd-self-insert-iso2022-8bit
    encoded-kbd-self-insert-sjis
    encoded-kbd-self-insert-utf-8
    encoded-kbd-setup-display
    encoded-kbd-setup-keymap
    end-of-visual-line
    epa-decrypt-armor-in-region
    epa-decrypt-file
    epa-decrypt-region
    epa-delete-keys
    epa-dired-do-decrypt
    epa-dired-do-encrypt
    epa-dired-do-sign
    epa-dired-do-verify
    epa-encrypt-file
    epa-encrypt-region
    epa-export-keys
    epa-file--file-name-regexp-set
    epa-file-disable
    epa-file-enable
    epa-file-find-file-hook
    epa-file-handler
    epa-file-name-regexp-update
    epa-global-mail-mode
    epa-import-armor-in-region
    epa-import-keys
    epa-import-keys-region
    epa-insert-keys
    epa-list-keys
    epa-list-secret-keys
    epa-mail-decrypt
    epa-mail-encrypt
    epa-mail-import-keys
    epa-mail-mode
    epa-mail-sign
    epa-mail-verify
    epa-select-keys
    epa-sign-file
    epa-sign-region
    epa-verify-cleartext-in-region
    epa-verify-file
    epa-verify-region
    epg-cancel
    epg-check-configuration
    epg-configuration
    epg-decrypt-file
    epg-decrypt-string
    epg-delete-keys
    epg-encrypt-file
    epg-encrypt-string
    epg-expand-group
    epg-export-keys-to-file
    epg-export-keys-to-string
    epg-generate-key-from-file
    epg-generate-key-from-string
    epg-import-keys-from-file
    epg-import-keys-from-server
    epg-import-keys-from-string
    epg-list-keys
    epg-receive-keys
    epg-sign-file
    epg-sign-keys
    epg-sign-string
    epg-start-decrypt
    epg-start-delete-keys
    epg-start-encrypt
    epg-start-export-keys
    epg-start-generate-key
    epg-start-import-keys
    epg-start-receive-keys
    epg-start-sign
    epg-start-sign-keys
    epg-start-verify
    epg-verify-file
    epg-verify-string
    erc-dcc-mode
    erc-list-mode
    erc-xdcc-mode
    ethio-composition-function
    ethio-insert-ethio-space
    face-all-attributes
    face-at-point
    face-remap-add-relative
    face-remap-reset-base
    face-remap-set-base
    face-spec-recalc
    face-spec-set-2
    field-complete
    file-modes-char-to-right
    file-modes-char-to-who
    file-modes-rights-to-number
    file-modes-symbolic-to-number
    fill-forward-paragraph
    find-cmd
    find-font
    find-lisp-object-file-name
    font-at
    font-face-attributes
    font-family-list
    font-get
    font-match-p
    font-put
    font-shape-gstring
    font-show-log
    font-spec
    font-variation-glyphs
    font-xlfd-name
    fontp
    foreground-color-at-point
    format-seconds
    frame-geom-spec-cons
    frame-geom-value-cons
    frame-terminal
    get-byte
    get-device-terminal
    get-font-glyphs
    global-auto-composition-mode
    global-auto-composition-mode-check-buffers
    global-auto-composition-mode-cmhh
    global-auto-composition-mode-enable-in-buffers
    global-highlight-changes-mode
    global-linum-mode
    global-visual-line-mode
    global-visual-line-mode-check-buffers
    global-visual-line-mode-cmhh
    global-visual-line-mode-enable-in-buffers
    global-whitespace-newline-mode
    global-whitespace-toggle-options
    gmm-regexp-concat
    gnus-bookmark-bmenu-list
    gnus-bookmark-jump
    gnus-bookmark-set
    goto-address-mode
    goto-address-prog-mode
    goto-history-element
    gpm-mouse-mode
    gud-tooltip-mode
    hack-dir-local-variables
    hack-local-variables-filter
    handle-shift-selection
    hangul-input-method-activate
    hashcash-insert-payment
    hashcash-insert-payment-async
    hashcash-verify-payment
    help-window-display-message
    help-window-setup
    help-window-setup-finish
    highlight-changes-visible-mode
    holiday-list
    ibuffer-do-isearch
    ibuffer-do-isearch-regexp
    ibuffer-do-sort-by-filename/process
    image-bookmark-jump
    indian-2-column-to-ucs-region
    Info-bookmark-jump
    insert-byte
    internal-complete-buffer-except
    internal-event-symbol-parse-modifiers
    isearch-describe-bindings
    isearch-describe-key
    isearch-describe-mode
    isearch-filter-visible
    isearch-forward-word
    isearch-help-for-help
    isearch-help-for-help-internal
    isearch-help-for-help-internal-doc
    isearch-highlight-regexp
    isearch-occur
    isearch-toggle-word
    iwconfig
    keymap-canonicalize
    kill-buffer-ask
    kill-matching-buffers
    kill-visual-line
    last-nonminibuffer-frame
    lglyph-adjustment
    lglyph-ascent
    lglyph-char
    lglyph-code
    lglyph-copy
    lglyph-descent
    lglyph-from
    lglyph-lbearing
    lglyph-rbearing
    lglyph-set-adjustment
    lglyph-set-char
    lglyph-set-code
    lglyph-set-from-to
    lglyph-set-width
    lglyph-to
    lglyph-width
    lgstring-char
    lgstring-char-len
    lgstring-font
    lgstring-glyph
    lgstring-glyph-len
    lgstring-header
    lgstring-insert-glyph
    lgstring-set-glyph
    lgstring-set-header
    lgstring-set-id
    lgstring-shaped-p
    line-move-visual
    linum-mode
    list-fonts
    list-system-processes
    locale-translate
    locate-dominating-file
    locate-file-completion-table
    locate-user-emacs-file
    looking-at-p
    lunar-phases
    mail-abbrevs-mode
    mail-add-payment
    mail-add-payment-async
    mail-check-payment
    mail-quote-printable-region
    make-serial-process
    make-translation-table-from-alist
    make-vc-git-extra-fileinfo
    map-keymap-sorted
    match-substitute-replacement
    max-char
    menu-bar-open
    menu-set-font
    message-bold-region
    message-unbold-region
    minibuffer--bitset
    minibuffer--double-dollars
    minibuffer-complete-shell-command
    minibuffer-default-add-completions
    minibuffer-default-add-shell-commands
    minibuffer-depth-indicate-mode
    minibuffer-force-complete
    minibuffer-history-isearch-end
    minibuffer-history-isearch-message
    minibuffer-history-isearch-pop-state
    minibuffer-history-isearch-push-state
    minibuffer-history-isearch-search
    minibuffer-history-isearch-setup
    minibuffer-history-isearch-wrap
    minor-mode-menu-from-indicator
    mkdir
    mode-line-frame-control
    mouse-appearance-menu
    mouse-drag-drag
    mouse-drag-throw
    mouse-event-p
    mouse-menu-bar-map
    mouse-menu-major-mode-map
    mouse-menu-non-singleton
    mouse-minor-mode-menu
    mouse-select-font
    mouse-yank-primary
    move-file-to-trash
    multi-isearch-buffers
    multi-isearch-buffers-regexp
    multi-isearch-files
    multi-isearch-files-regexp
    multi-isearch-setup
    newsticker-plainview
    newsticker-treeview
    next-logical-line
    normal-erase-is-backspace-setup-frame
    nxml-enable-unicode-char-name-sets
    nxml-glyph-display-string
    nxml-mode
    occur-context-lines
    open-font
    org-agenda-check-for-timestamp-as-reason-to-ignore-todo-item
    org-attach
    org-bbdb-anniversaries
    org-calendar-goto-agenda
    org-clock-persistence-insinuate
    org-customize
    org-export
    org-export-as-ascii
    org-export-as-html
    org-export-as-html-and-open
    org-export-as-html-batch
    org-export-as-html-to-buffer
    org-export-as-pdf
    org-export-as-pdf-and-open
    org-export-as-xoxo
    org-export-htmlize-generate-css
    org-export-region-as-html
    org-export-visible
    org-footnote-action
    org-footnote-normalize
    org-get-clocktable
    org-id-copy
    org-id-find
    org-id-find-id-file
    org-id-get
    org-id-get-create
    org-id-get-with-outline-drilling
    org-id-get-with-outline-path-completion
    org-id-goto
    org-ido-switchb
    org-insert-export-options-template
    org-iswitchb
    org-map-entries
    org-open-link-from-string
    org-plot/gnuplot
    org-publish-project
    org-replace-region-by-html
    org-require-autoloaded-modules
    org-table-to-lisp
    org-timer
    org-timer-change-times-in-region
    org-timer-item
    org-timer-start
    pcomplete/scp
    pcomplete/ssh
    pp-macroexpand-expression
    pp-macroexpand-last-sexp
    previous-logical-line
    proced
    process-attributes
    process-file-shell-command
    process-lines
    process-type
    python-shell
    query-font
    read-buffer-to-switch
    read-char-by-name
    read-color
    read-file-modes
    read-regexp
    read-shell-command
    recenter-top-bottom
    region-active-p
    remember
    remember-clipboard
    remember-diary-extract-entries
    remember-other-frame
    resume-tty
    rmail-mime
    rmail-output-as-seen
    rng-c-load-schema
    rng-nxml-mode-init
    rng-validate-mode
    rng-xsd-compile
    robin-modify-package
    robin-use-package
    rst-minor-mode
    rst-mode
    ruby-mode
    save-buffers-kill-terminal
    selected-terminal
    serial-process-configure
    serial-term
    server-force-delete
    server-save-buffers-kill-terminal
    set-charset-priority
    set-coding-system-priority
    set-input-interrupt-mode
    set-input-meta-mode
    set-output-flow-control
    set-quit-char
    set-terminal-parameter
    set-window-parameter
    setenv-internal
    smerge-start-session
    sort-build-lists
    sort-fields-1
    sort-regexp-fields-next-record
    sort-reorder-buffer
    sort-skip-fields
    special-mode
    split-window-sensibly
    start-file-process
    start-file-process-shell-command
    string-match-p
    string-to-unibyte
    suspend-frame
    suspend-tty
    symbol-complete
    symbol-completion-try-complete
    tai-viet-composition-function
    talk
    terminal-list
    terminal-live-p
    terminal-name
    terminal-parameter
    terminal-parameters
    text-scale-adjust
    text-scale-decrease
    text-scale-increase
    timer--activate
    timer--args
    timer--function
    timer--high-seconds
    timer--idle-delay
    timer--low-seconds
    timer--repeat-delay
    timer--time
    timer--time-less-p
    timer--triggered
    timer--usecs
    toggle-auto-composition
    toggle-menu-bar-mode-from-frame
    toggle-tool-bar-mode-from-frame
    toggle-word-wrap
    tool-bar-make-keymap
    tool-bar-make-keymap-1
    tooltip-show-help-non-mode
    tpu-mapper
    truncated-partial-width-window-p
    tty-find-type
    tty-run-terminal-initialization
    tty-type
    turn-on-auto-composition-if-enabled
    turn-on-font-lock-if-desired
    turn-on-visual-line-mode
    uce-reply-to-uce
    ucs-names
    unibyte-string
    unify-charset
    url-basepath
    use-cjk-char-width-table
    use-default-char-width-table
    use-region-p
    utf-7-imap-post-read-conversion
    utf-7-imap-pre-write-conversion
    utf-7-post-read-conversion
    utf-7-pre-write-conversion
    variable-pitch-mode
    vc-create-tag
    vc-default-working-revision
    vc-delete-file
    vc-dir
    vc-git--call
    vc-git--empty-db-p
    vc-git--out-ok
    vc-git--run-command-string
    vc-git--state-code
    vc-git-after-dir-status-stage
    vc-git-annotate-command
    vc-git-annotate-extract-revision-at-line
    vc-git-annotate-time
    vc-git-checkin
    vc-git-checkout
    vc-git-checkout-model
    vc-git-command
    vc-git-create-extra-fileinfo
    vc-git-create-repo
    vc-git-create-tag
    vc-git-delete-file
    vc-git-diff
    vc-git-dir-extra-headers
    vc-git-dir-printer
    vc-git-dir-status
    vc-git-dir-status-files
    vc-git-dir-status-goto-stage
    vc-git-escape-file-name
    vc-git-extra-fileinfo->new-perm
    vc-git-extra-fileinfo->old-perm
    vc-git-extra-fileinfo->orig-name
    vc-git-extra-fileinfo->rename-state
    vc-git-extra-fileinfo-p
    vc-git-extra-menu
    vc-git-extra-status-menu
    vc-git-file-type-as-string
    vc-git-find-revision
    vc-git-grep
    vc-git-log-view-mode
    vc-git-mode-line-string
    vc-git-next-revision
    vc-git-permissions-as-string
    vc-git-previous-revision
    vc-git-print-log
    vc-git-register
    vc-git-rename-as-string
    vc-git-rename-file
    vc-git-responsible-p
    vc-git-retrieve-tag
    vc-git-revert
    vc-git-revision-completion-table
    vc-git-revision-granularity
    vc-git-revision-table
    vc-git-root
    vc-git-show-log-entry
    vc-git-state
    vc-git-symbolic-commit
    vc-git-unregister
    vc-git-workfile-unchanged-p
    vc-git-working-revision
    vc-retrieve-tag
    vc-revert
    vc-revision-other-window
    vc-rollback
    vc-version-diff
    vc-working-revision
    view-emacs-debugging
    view-external-packages
    view-help-file
    view-return-to-alist-update
    visual-line-mode
    whitespace-mode
    whitespace-newline-mode
    whitespace-report
    whitespace-report-region
    whitespace-toggle-options
    widget-value
    window--display-buffer-1
    window--display-buffer-2
    window--even-window-heights
    window--frame-usable-p
    window--try-to-split-window
    window-fixed-size-p
    window-parameter
    window-parameters
    window-splittable-p
    window-system
    word-search-backward-lax
    word-search-forward-lax
    x-file-dialog
    x-handle-parent-id
    x-initialize-window-system
    x-menu-bar-open-internal
    x-select-font
    x-setup-function-keys
    x-wm-set-size-hint
    xesam-search
    xml-find-file-coding-system
    xmltok-get-declared-encoding-position)
  "New functions introduced from Emacs23.")

(dolist (func new-functions-from-emacs23)
  (put func 'usable-from 23))

(defadvice eldoc-highlight-function-argument
  (around my-formatting (sym args index) compile activate preactivate)
  "Replace original to apply my style of formatting."
  ;; HACK: intercept the call to eldoc-docstring-format-sym-doc at the
  ;; end of the advices function. This is obviously brittle, but the
  ;; alternative approach of copy/pasting the original also has
  ;; downsides...
  (flet ((eldoc-docstring-format-sym-doc
          (sym doc face)
          (let* ((function-name (propertize (symbol-name sym)
                                            'face face))
                 (spec (format "%s %s%s"
                               function-name
                               (if (get sym 'usable-from)
                                   (format "{%d}" (get sym 'usable-from))
                                 "")
                               doc))
                 (docstring (or (eldoc-docstring-first-line
                                 (documentation sym t))
                                "Undocumented."))
                 (docstring (propertize docstring
                                        'face 'font-lock-doc-face))
                 ;; TODO: currently it strips from the start of spec by
                 ;; character instead of whole arguments at a time.
                 (fulldoc (format "%s: %s" spec docstring))
                 (ea-width (1- (window-width (minibuffer-window)))))
            (cond ((or (<= (length fulldoc) ea-width)
                       (eq eldoc-echo-area-use-multiline-p t)
                       (and eldoc-echo-area-use-multiline-p
                            (> (length docstring) ea-width)))
                   fulldoc)
                  ((> (length docstring) ea-width)
                   (substring docstring 0 ea-width))
                  ((>= (- (length fulldoc) (length spec)) ea-width)
                   docstring)
                  (t
                   ;; Show the end of the partial symbol name, rather
                   ;; than the beginning, since the former is more likely
                   ;; to be unique given package namespace conventions.
                   (setq spec (substring spec (- (length fulldoc) ea-width)))
                   (format "%s: %s" spec docstring))))))
    ad-do-it))

;;;; Bug report
(defvar eldoc-extension-maintainer-mail-address
  (concat "rubiki" "tch@ru" "by-lang.org"))
(defvar eldoc-extension-bug-report-salutation
  "Describe bug below, using a precise recipe.

When I executed M-x ...

How to send a bug report:
  1) Be sure to use the LATEST version of eldoc-extension.el.
  2) Enable debugger. M-x toggle-debug-on-error or (setq debug-on-error t)
  3) Use Lisp version instead of compiled one: (load \"eldoc-extension.el\")
  4) If you got an error, please paste *Backtrace* buffer.
  5) Type C-c C-c to send.
# If you are a Japanese, please write in Japanese:-)")
(defun eldoc-extension-send-bug-report ()
  (interactive)
  (reporter-submit-bug-report
   eldoc-extension-maintainer-mail-address
   "eldoc-extension.el"
   (apropos-internal "^eldoc-" 'boundp)
   nil nil
   eldoc-extension-bug-report-salutation))

(provide 'eldoc-extension)

;; (shell-command "emacs-test -l eldoc-extension -f eldoc-mode &")
;; (progn (git-log-upload) (emacswiki-post "eldoc-extension.el"))
;;; eldoc-extension.el ends here

;;; LocalWords:  eldoc sym args docstring
