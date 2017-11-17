;;; emojify.el --- Display emojis in Emacs           -*- lexical-binding: t; -*-

;; Copyright (C) 2015-2017  Iqbal Ansari

;; Author: Iqbal Ansari <iqbalansari02@yahoo.com>
;; Keywords: multimedia, convenience
;; URL: https://github.com/iqbalansari/emacs-emojify
;; Version: 0.4
;; Package-Requires: ((seq "1.11") (ht "2.0") (emacs "24.3"))

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

;; This package displays emojis in Emacs similar to how Github, Slack etc do.  It
;; can display plain ascii like ':)' as well as Github style emojis like ':smile:'
;;
;; It provides a minor mode `emojify-mode' to enable display of emojis in a buffer.
;; To enable emojify mode globally use `global-emojify-mode'
;;
;; For detailed documentation see the projects README file at
;; https://github.com/iqbalansari/emacs-emojify



;;; Code:

(require 'seq)
(require 'ht)

(require 'subr-x nil :no-error)
(require 'cl-lib)
(require 'json)
(require 'regexp-opt)
(require 'jit-lock)
(require 'pcase)
(require 'tar-mode)
(require 'apropos)



;; Satisfying the byte-compiler
;; We do not "require" these functions but if `org-mode' is active we use them

;; Required to determine point is in an org-list
(declare-function org-list-get-item-begin "org-list")
(declare-function org-at-heading-p "org")

;; Required to determine point is in an org-src block
(declare-function org-element-type "org-element")
(declare-function org-element-at-point "org-element")

;; Required for integration with company-mode
(declare-function company-pseudo-tooltip-unhide "company")

;; Shouldn't require 'jit-lock be enough :/
(defvar jit-lock-start)
(defvar jit-lock-end)

;; Used while inserting emojis using helm
(defvar helm-buffer)
(defvar helm-after-initialize-hook)



;; Compatibility functions

(defun emojify-user-error (format &rest args)
  "Signal a pilot error, making a message by passing FORMAT and ARGS to ‘format-message’."
  (if (fboundp 'user-error)
      (apply #'user-error format args)
    (apply #'error format args)))

(defun emojify-face-height (face)
  "Get font height for the FACE."
  (let ((face-font (face-font face)))
    (cond
     ((and (display-multi-font-p)
           ;; Avoid calling font-info if the frame's default font was
           ;; not changed since the frame was created.  That's because
           ;; font-info is expensive for some fonts, see bug #14838.
           (not (string= (frame-parameter nil 'font) face-font)))
      (aref (font-info face-font) 3))
     (t (frame-char-height)))))

(defun emojify-default-font-height ()
  "Return the height in pixels of the current buffer's default face font.

`default-font-height' seems to be available only on Emacs versions after 24.3.
This provides a compatibility version for previous versions."
  (if (fboundp 'default-font-height)
      (default-font-height)
    (emojify-face-height 'default)))

(defun emojify-overlays-at (pos &optional sorted)
  "Return a list of the overlays that contain the character at POS.
If SORTED is non-nil, then sort them by decreasing priority.

The SORTED argument was introduced in Emacs 24.4, along with the incompatible
change that overlay priorities can be any Lisp object (earlier they were
restricted to integer and nil).  This version uses the SORTED argument of
`overlays-at' on Emacs version 24.4 onwards and manually sorts the overlays by
priority on lower versions."
  (if (version< emacs-version "24.4")
      (let ((overlays-at-pos (overlays-at pos)))
        (if sorted
            (seq-sort (lambda (overlay1 overlay2)
                        (if (and (overlay-get overlay2 'priority)
                                 (overlay-get overlay1 'priority))
                            ;; If both overlays have priorities compare them
                            (< (overlay-get overlay1 'priority)
                               (overlay-get overlay2 'priority))
                          ;; Otherwise overlay with nil priority is sorted below
                          ;; the one with integer value otherwise preserve order
                          (not (overlay-get overlay1 'priority))))
                      overlays-at-pos)
          overlays-at-pos))
    (overlays-at pos sorted)))

(defun emojify--string-join (strings &optional separator)
  "Join all STRINGS using SEPARATOR.

This function is available on Emacs v24.4 and higher, it has been
backported here for compatibility with older Emacsen."
  (if (fboundp 'string-join)
      (apply #'string-join (list strings separator))
    (mapconcat 'identity strings separator)))



;; Debugging helpers

(define-minor-mode emojify-debug-mode
  "Enable debugging for emojify-mode.

By default emojify silences any errors during emoji redisplay.  This is done
since emojis are redisplayed using jit-lock (the same mechanism used for
font-lock) as such any bugs in the code can cause other important things to
fail. This also turns on jit-debug-mode so that (e)debugging emojify's redisplay
functions work."
  :init-value nil
  (if emojify-debug-mode
      (when (fboundp 'jit-lock-debug-mode)
        (jit-lock-debug-mode +1))
    (when (fboundp 'jit-lock-debug-mode)
      (jit-lock-debug-mode -1))))

(defmacro emojify-execute-ignoring-errors-unless-debug (&rest forms)
  "Execute FORMS ignoring errors unless variable `emojify-debug-mode' is non-nil."
  (declare (debug t) (indent 0))
  `(if emojify-debug-mode
       (progn
         ,@forms)
     (ignore-errors
       ,@forms)))



;; Utility functions

;; These should be bound dynamically by functions calling
;; `emojify--inside-rectangle-selection-p' and
;; `emojify--inside-non-rectangle-selection-p' to region-beginning and
;; region-end respectively. This is needed mark the original region which is
;; impossible to get after point moves during processing.
(defvar emojify-region-beg nil)
(defvar emojify-region-end nil)

;; This should be bound dynamically to the location of point before emojify's
;; display loop, this since getting the point after point moves during
;; processing is impossible
(defvar emojify-current-point nil)

(defmacro emojify-with-saved-buffer-state (&rest forms)
  "Execute FORMS saving current buffer state.

This saves point and mark, `match-data' and buffer modification state it also
inhibits buffer change, point motion hooks."
  (declare (debug t) (indent 0))
  `(let ((inhibit-point-motion-hooks t)
         (emojify-current-point (point))
         (emojify-region-beg (when (region-active-p) (region-beginning)))
         (emojify-region-end (when (region-active-p) (region-end))))
     (with-silent-modifications
       (save-match-data
         (save-excursion
           (save-restriction
             (widen)
             ,@forms))))))

(defmacro emojify-do-for-emojis-in-region (beg end &rest forms)
  "For all emojis between BEG and END, execute the given FORMS.

During the execution `emoji-start' and `emoji-end' are bound to the start
and end of the emoji for which the form is being executed."
  (declare (debug t) (indent 2))
  `(let ((--emojify-loop-current-pos ,beg)
         (--emojify-loop-end ,end)
         emoji-start)
     (while (and (> --emojify-loop-end --emojify-loop-current-pos)
                 (setq emoji-start (text-property-any --emojify-loop-current-pos --emojify-loop-end 'emojified t)))
       (let ((emoji-end (+ emoji-start
                           (length (get-text-property emoji-start 'emojify-text)))))
         ,@forms
         (setq --emojify-loop-current-pos emoji-end)))))

(defun emojify-message (format-string &rest args)
  "Log debugging messages to buffer named 'emojify-log'.

This is a substitute to `message' since using it during redisplay causes errors.
FORMAT-STRING and ARGS are same as the arguments to `message'."
  (when emojify-debug-mode
    (emojify-with-saved-buffer-state
      (with-current-buffer (get-buffer-create "emojify-log")
        (goto-char (point-max))
        (insert (apply #'format format-string args))
        (insert "\n")))))

(defun emojify--get-relevant-region ()
  "Try getting region in buffer that completely covers the current window.

This is used instead of directly using `window-start' and `window-end', since
they return the values corresponding buffer in currently selected window, which
is incorrect if the buffer where there are called is not actually the buffer
visible in the selected window."
  (let* ((window-size (- (window-end) (window-start)))
         (start (max (- (point) window-size) (point-min)))
         (end (min (+ (point) window-size) (point-max))))
    (cons start end)))

(defun emojify-quit-buffer ()
  "Hide the current buffer.
There are windows other than the one the current buffer is displayed in quit the
current window too."
  (interactive)
  (if (= (length (window-list)) 1)
      (bury-buffer)
    (quit-window)))

(defvar emojify-common-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "q" #'emojify-quit-buffer)
    (define-key map "n" #'next-line)
    (define-key map "p" #'previous-line)
    (define-key map "r" #'isearch-backward)
    (define-key map "s" #'isearch-forward)
    (define-key map ">" #'end-of-buffer)
    (define-key map "<" #'beginning-of-buffer)

    (dolist (key '("?" "h" "H"))
      (define-key map key #'describe-mode))

    (dolist (number (number-sequence 0 9))
      (define-key map (number-to-string number) #'digit-argument))

    map)
  "Common keybindings available in all special emojify buffers.")



;; Customizations for control how emojis are displayed

(defgroup emojify nil
  "Customization options for emojify"
  :group 'display
  :prefix "emojify-")

(defcustom emojify-emoji-json
  (expand-file-name "data/emoji.json"
                    (cond (load-file-name (file-name-directory load-file-name))
                          ((locate-library "emojify") (file-name-directory (locate-library "emojify")))
                          (t default-directory)))
  "The path to JSON file containing the configuration for displaying emojis."
  :type 'file
  :group 'emojify)

(defvar emojify-emoji-set-json
  (let ((json-array-type 'list)
        (json-object-type 'hash-table))
    (json-read-file (expand-file-name "data/emoji-sets.json"
                                      (cond (load-file-name (file-name-directory load-file-name))
                                            ((locate-library "emojify") (file-name-directory (locate-library "emojify")))
                                            (t default-directory))))))

(defcustom emojify-emoji-set "emojione-v2.2.6-22"
  "The emoji set used to display emojis."
  :type (append '(radio :tag "Emoji set")
                (mapcar (lambda (set) (list 'const set))
                        (ht-keys emojify-emoji-set-json)))
  :group 'emojify)

(defcustom emojify-emojis-dir
  (locate-user-emacs-file "emojis")
  "Path to the directory containing the emoji images."
  :type 'directory
  :group 'emojify)

(defcustom emojify-display-style
  'image
  "How the emoji's be displayed.

Possible values are
`image'   - Display emojis using images, this requires images are supported by
            user's Emacs installation
`unicode' - Display emojis using unicode characters, this works well on
            platforms with good emoji fonts.  In this case the emoji text
            ':wink:' will be substituted with 😉.
`ascii'   - Display emojis as ascii characters, this is simplest and does not
            require any external dependencies.  In this cases emoji text like
            ':wink:' are substituted with ascii equivalents like ';)'"
  :type '(radio :tag "Emoji display style"
                (const :tag "Display emojis as images" image)
                (const :tag "Display emojis as unicode characters" unicode)
                (const :tag "Display emojis as ascii string" ascii))
  :group 'emojify)



;; Customizations to control the enabling of emojify-mode

(defcustom emojify-inhibit-major-modes
  '(dired-mode
    doc-view-mode
    debugger-mode
    pdf-view-mode
    image-mode
    help-mode
    ibuffer-mode
    magit-popup-mode
    magit-diff-mode
    ert-results-mode
    compilation-mode
    proced-mode
    mu4e-headers-mode)
  "Major modes where emojify mode should not be enabled."
  :type '(repeat symbol)
  :group 'emojify)

(defcustom emojify-inhibit-in-buffer-functions
  '(emojify-minibuffer-p emojify-helm-buffer-p)
  "Functions used inhibit emojify-mode in a buffer.

These functions are called with one argument, the buffer where command
‘emojify-mode’ is about to be enabled, emojify is not enabled if any of the
functions return a non-nil value."
  :type 'hook
  :group 'emojify)

(defvar emojify-inhibit-emojify-in-current-buffer-p nil
  "Should emojify be inhibited in current buffer.

This is a buffer local variable that can be set to inhibit enabling of
emojify in a buffer.")
(make-variable-buffer-local 'emojify-inhibit-emojify-in-current-buffer-p)

(defvar emojify-minibuffer-reading-emojis-p nil
  "Are we currently reading emojis using minibuffer?")

(defun emojify-ephemeral-buffer-p (buffer)
  "Determine if BUFFER is an ephemeral/temporary buffer."
  (and (not (minibufferp))
       (string-match-p "^ " (buffer-name buffer))))

(defun emojify-inhibit-major-mode-p (buffer)
  "Determine if user has disabled the `major-mode' enabled for the BUFFER.

Returns non-nil if the buffer's major mode is part of `emojify-inhibit-major-modes'"
  (with-current-buffer buffer
    (apply #'derived-mode-p emojify-inhibit-major-modes)))

(defun emojify-helm-buffer-p (buffer)
  "Determine if the current BUFFER is a helm buffer."
  (unless emojify-minibuffer-reading-emojis-p
    (string-match-p "\\*helm" (buffer-name buffer))))

(defun emojify-minibuffer-p (buffer)
  "Determine if the current BUFFER is a minibuffer."
  (unless emojify-minibuffer-reading-emojis-p
    (minibufferp buffer)))

(defun emojify-buffer-p (buffer)
  "Determine if `emojify-mode' should be enabled for given BUFFER.

`emojify-mode' mode is not enabled in temporary buffers.  Additionally user
can customize `emojify-inhibit-major-modes' and
`emojify-inhibit-in-buffer-functions' to disabled emojify in additional buffers."
  (not (or emojify-inhibit-emojify-in-current-buffer-p
           (emojify-ephemeral-buffer-p (current-buffer))
           (emojify-inhibit-major-mode-p (current-buffer))
           (buffer-base-buffer buffer)
           (run-hook-with-args-until-success 'emojify-inhibit-in-buffer-functions buffer))))



;; Customizations to control display of emojis

(defvar emojify-emoji-style-change-hook nil
  "Hooks run when emoji style changes.")

;;;###autoload
(defun emojify-set-emoji-styles (styles)
  "Set the type of emojis that should be displayed.

STYLES is the styles emoji styles that should be used, see `emojify-emoji-styles'"
  (when (not (listp styles))
    (setq styles (list styles))
    (warn "`emojify-emoji-style' has been deprecated use `emojify-emoji-styles' instead!"))

  (setq-default emojify-emoji-styles styles)

  (run-hooks 'emojify-emoji-style-change-hook))

(defcustom emojify-emoji-styles
  '(ascii unicode github)
  "The type of emojis that should be displayed.

These can have one of the following values

`ascii'           - Display only ascii emojis for example ';)'
`unicode'         - Display only unicode emojis for example '😉'
`github'          - Display only github style emojis for example ':wink:'"
  :type '(set
          (const :tag "Display only ascii emojis" ascii)
          (const :tag "Display only github emojis" github)
          (const :tag "Display only unicode codepoints" unicode))
  :set (lambda (_ value) (emojify-set-emoji-styles value))
  :group 'emojify)

(defcustom emojify-program-contexts
  '(comments string code)
  "Contexts where emojis can be displayed in programming modes.

Possible values are
`comments' - Display emojis in comments
`string'   - Display emojis in strings
`code'     - Display emojis in code (this is applicable only for unicode emojis)"
  :type '(set :tag "Contexts where emojis should be displayed in programming modes"
              (const :tag "Display emojis in comments" comments)
              (const :tag "Display emojis in string" string)
              (const :tag "Display emojis in code" code))
  :group 'emojify)

(defcustom emojify-inhibit-functions
  '(emojify-in-org-tags-p emojify-in-org-list-p)
  "Functions used to determine given emoji should displayed at current point.

These functions are called with 3 arguments, the text to be emojified, the start
of emoji text and the end of emoji text.  These functions are called with the
buffer where emojis are going to be displayed selected."
  :type 'hook
  :group 'emojify)

(defcustom emojify-composed-text-p t
  "Should composed text be emojified."
  :type 'boolean
  :group 'emojify)

(defcustom emojify-company-tooltips-p t
  "Should company mode tooltips be emojified."
  :type 'boolean
  :group 'emojify)

(defun emojify-in-org-tags-p (match beg _end)
  "Determine whether the point is on `org-mode' tag.

MATCH, BEG and _END are the text currently matched emoji and the start position
and end position of emoji text respectively.

Easiest would have to inspect face at point but unfortunately, there is no
way to guarantee that we run after font-lock"
  (and (memq major-mode '(org-mode org-agenda-mode))
       (string-match-p ":[^:]+[:]?" match)
       (org-at-heading-p)
       (save-excursion
         (save-match-data
           (goto-char beg)
           (looking-at ":[^:]+:[\s-]*$")))))

(defun emojify-in-org-list-p (text beg &rest ignored)
  "Determine whether the point is in `org-mode' list.

TEXT is the text which is supposed to rendered a an emoji.  BEG is the beginning
of the emoji text in the buffer.  The arguments IGNORED are ignored."
  (and (eq major-mode 'org-mode)
       (equal text "8)")
       (equal (org-list-get-item-begin) beg)))

(defun emojify-valid-program-context-p (emoji beg end)
  "Determine if EMOJI should be displayed for text between BEG and END.

This returns non-nil if the region is valid according to `emojify-program-contexts'"
  (when emojify-program-contexts
    (let* ((syntax-beg (syntax-ppss beg))
           (syntax-end (syntax-ppss end))
           (context (cond ((and (nth 3 syntax-beg)
                                (nth 3 syntax-end))
                           'string)
                          ((and (nth 4 syntax-beg)
                                (nth 4 syntax-end))
                           'comments)
                          (t 'code))))
      (and (memql context emojify-program-contexts)
           (if (equal context 'code)
               (and (string= (ht-get emoji "style") "unicode")
                    (memql 'unicode emojify-emoji-styles))
             t)))))

(defun emojify-inside-org-src-p (point)
  "Return non-nil if POINT is inside `org-mode' src block.

This is used to inhibit display of emoji's in `org-mode' src blocks
since our mechanisms do not work in it."
  (when (eq major-mode 'org-mode)
    (save-excursion
      (goto-char point)
      (eq (org-element-type (org-element-at-point)) 'src-block))))

(defun emojify-looking-at-end-of-list-maybe (point)
  "Determine if POINT is end of a list.

This is not accurate since it restricts the region to scan to
the visible area."
  (let* ((area (emojify--get-relevant-region))
         (beg (car area))
         (end (cdr area)))
    (save-restriction
      (narrow-to-region beg end)
      (let ((list-start (ignore-errors (scan-sexps point -1))))
        (when (and list-start
                   ;; Ignore the starting brace if it is an emoji
                   (not (get-text-property list-start 'emojified)))
          ;; If we got a list start make sure both start and end
          ;; belong to same string/comment
          (let ((syntax-beg (syntax-ppss list-start))
                (syntax-end (syntax-ppss point)))
            (and list-start
                 (eq (nth 8 syntax-beg)
                     (nth 8 syntax-end)))))))))

(defun emojify-valid-ascii-emoji-context-p (beg end)
  "Determine if the okay to display ascii emoji between BEG and END."
  ;; The text is at the start of the buffer
  (and (or (not (char-before beg))
           ;; 32 space since ?  (? followed by a space) is not readable
           ;; 34 is "  since?" confuses font-lock
           ;; 41 is )  since?) (extra paren) confuses most packages
           (memq (char-syntax (char-before beg))
                 ;; space
                 '(32
                   ;; start/end of string
                   34
                   ;; whitespace syntax
                   ?-
                   ;; comment start
                   ?<
                   ;; comment end, this handles text at start of line immediately
                   ;; after comment line in a multiline comment
                   ?>)))
       ;; The text is at the end of the buffer
       (or (not (char-after end))
           (memq (char-syntax (char-after end))
                 ;; space
                 '(32
                   ;; start/end of string
                   34
                   ;; whitespace syntax
                   ?-
                   ;; punctuation
                   ?.
                   ;; closing braces
                   41
                   ;; comment end
                   ?>)))))



;; Obsolete vars

(define-obsolete-variable-alias 'emojify-emoji-style 'emojify-emoji-styles "0.2")
(define-obsolete-function-alias 'emojify-set-emoji-style 'emojify-set-emoji-styles "0.2")



;; Customizations to control the behaviour when point enters emojified text

(defcustom emojify-point-entered-behaviour 'echo
  "The behaviour when point enters, an emojified text.

It can be one of the following
`echo'    - Echo the underlying text in the minibuffer
`uncover' - Display the underlying text while point is on it
function  - It is called with 2 arguments (the buffer where emoji appears is
            current during execution)
            1) starting position of emoji text
            2) ending position of emoji text

Does nothing if the value is anything else."
  ;; TODO: Mention custom function
  :type '(radio :tag "Behaviour when point enters an emoji"
                (const :tag "Echo the underlying emoji text in the minibuffer" echo)
                (const :tag "Uncover (undisplay) the underlying emoji text" uncover))
  :group 'emojify)

(defcustom emojify-reveal-on-isearch t
  "Should underlying emoji be displayed when point enters emoji while in isearch mode.")

(defcustom emojify-show-help t
  "If non-nil the underlying text is displayed in a popup when mouse moves over it."
  :type 'boolean
  :group 'emojify)

(defun emojify-on-emoji-enter (beginning end)
  "Executed when point enters emojified text between BEGINNING and END."
  (cond ((and (eq emojify-point-entered-behaviour 'echo)
              ;; Do not echo in isearch-mode
              (not isearch-mode)
              (not (active-minibuffer-window))
              (not (current-message)))
         (message (substring-no-properties (get-text-property beginning 'emojify-text))))
        ((eq emojify-point-entered-behaviour 'uncover)
         (put-text-property beginning end 'display nil))
        ((functionp 'emojify-point-entered-behaviour)
         (funcall emojify-point-entered-behaviour beginning end)))

  (when (and isearch-mode emojify-reveal-on-isearch)
    (put-text-property beginning end 'display nil)))

(defun emojify-on-emoji-exit (beginning end)
  "Executed when point exits emojified text between BEGINNING and END."
  (put-text-property beginning
                     end
                     'display
                     (get-text-property beginning 'emojify-display)))

(defvar-local emojify--last-emoji-pos nil)

(defun emojify-detect-emoji-entry/exit ()
  "Detect emoji entry and exit and run appropriate handlers.

This is inspired by `prettify-symbol-mode's logic for
`prettify-symbols-unprettify-at-point'."
  (while-no-input
    (emojify-with-saved-buffer-state
      (when emojify--last-emoji-pos
        (emojify-on-emoji-exit (car emojify--last-emoji-pos) (cdr emojify--last-emoji-pos)))

      (when (get-text-property (point) 'emojified)
        (let* ((text-props (text-properties-at (point)))
               (buffer (plist-get text-props 'emojify-buffer))
               (match-beginning (plist-get text-props 'emojify-beginning))
               (match-end (plist-get text-props 'emojify-end)))
          (when (eq buffer (current-buffer))
            (emojify-on-emoji-enter match-beginning match-end)
            (setq emojify--last-emoji-pos (cons match-beginning match-end))))))))

(defun emojify-help-function (_window _string pos)
  "Function to get help string to be echoed when point/mouse into the point.

To understand WINDOW, STRING and POS see the function documentation for
`help-echo' text-property."
  (when (and emojify-show-help
             (not isearch-mode)
             (not (active-minibuffer-window))
             (not (current-message)))
    (plist-get (text-properties-at pos) 'emojify-text)))



;; Core functions and macros

;; Variables related to user emojis

(defcustom emojify-user-emojis nil
  "User specified custom emojis.

This is an alist where first element of cons is the text to be displayed as
emoji, while the second element of the cons is an alist containing data about
the emoji.

The inner alist should have atleast (not all keys are strings)

`name'  - The name of the emoji
`style' - This should be one of \"github\", \"ascii\" or \"github\"
          (see `emojify-emoji-styles')

The alist should contain one of (see `emojify-display-style')
`unicode' - The replacement for the provided emoji for \"unicode\" display style
`image'   - The replacement for the provided emoji for \"image\" display style.
            This should be the absolute path to the image
`ascii'   - The replacement for the provided emoji for \"ascii\" display style

Example -
The following assumes that custom images are at ~/.emacs.d/emojis/trollface.png and
~/.emacs.d/emojis/neckbeard.png

'((\":troll:\"     . ((\"name\" . \"Troll\")
                    (\"image\" . \"~/.emacs.d/emojis/trollface.png\")
                    (\"style\" . \"github\")))
  (\":neckbeard:\" . ((\"name\" . \"Neckbeard\")
                    (\"image\" . \"~/.emacs.d/emojis/neckbeard.png\")
                    (\"style\" . \"github\"))))")

(defvar emojify--user-emojis nil
  "User specified custom emojis.")

(defvar emojify--user-emojis-regexp nil
  "Regexp to match user specified custom emojis.")

;; Variables related to default emojis
(defvar emojify-emojis nil
  "Data about the emojis, this contains only the emojis that come with emojify.")

(defvar emojify-regexps nil
  "List of regexps to match text to be emojified.")

(defvar emojify--completing-candidates-cache nil
  "Cached values for completing read candidates calculated for `emojify-completing-read'.")

;; Cache for emoji completing read candidates
(defun emojify--get-completing-read-candidates ()
  "Get the candidates to be used for `emojify-completing-read'.

The candidates are calculated according to currently active
`emojify-emoji-styles' and cached"
  (let ((styles (mapcar #'symbol-name emojify-emoji-styles)))
    (unless (and emojify--completing-candidates-cache
                 (equal styles (car emojify--completing-candidates-cache)))
      (setq emojify--completing-candidates-cache
            (cons styles
                  (let ((emojis (ht-create #'equal)))
                    (emojify-emojis-each (lambda (key value)
                                           (when (seq-position styles (ht-get value "style"))
                                             (ht-set! emojis
                                                      (format "%s - %s (%s)"
                                                              key
                                                              (ht-get value "name")
                                                              (ht-get value "style"))
                                                      value))))
                    emojis))))
    (cdr emojify--completing-candidates-cache)))

(defun emojify-create-emojify-emojis (&optional force)
  "Create `emojify-emojis' if needed.

The function avoids reading emoji data if it has already been read unless FORCE
in which case emoji data is re-read."
  (when (or force (not emojify-emojis))
    (emojify-set-emoji-data)))

(defun emojify-get-emoji (emoji)
  "Get data for given EMOJI.

This first looks for the emoji in `emojify--user-emojis',
and then in `emojify-emojis'."
  (or (when emojify--user-emojis
        (ht-get emojify--user-emojis emoji))
      (ht-get emojify-emojis emoji)))

(defun emojify-emojis-each (function)
  "Execute FUNCTION for each emoji.

This first runs function for `emojify--user-emojis',
and then `emojify-emojis'."
  (when emojify--user-emojis
    (ht-each function emojify--user-emojis))
  (ht-each function emojify-emojis))

(defun emojify--verify-user-emojis (emojis)
  "Verify the EMOJIS in correct user format."
  (seq-every-p (lambda (emoji)
                 (and (assoc "name" (cdr emoji))
                      ;; Make sure style is present is only one of
                      ;; "unicode", "ascii" and "github".
                      (assoc "style" (cdr emoji))
                      (seq-position '("unicode" "ascii" "github")
                                    (cdr (assoc "style" (cdr emoji))))
                      (or (assoc "unicode" (cdr emoji))
                          (assoc "image" (cdr emoji))
                          (assoc "ascii" (cdr emoji)))))
               emojis))

(defun emojify-set-emoji-data ()
  "Read the emoji data for STYLES and set the regexp required to search them."
  (setq-default emojify-emojis (let ((json-array-type 'list)
                                     (json-object-type 'hash-table))
                                 (json-read-file emojify-emoji-json)))

  (let (unicode-emojis ascii-emojis)
    (ht-each (lambda (emoji data)
               (when (string= (ht-get data "style") "unicode")
                 (push emoji unicode-emojis))

               (when (string= (ht-get data "style") "ascii")
                 (push emoji ascii-emojis)))
             emojify-emojis)

    ;; Construct emojify-regexps such that github style are searched first
    ;; followed by unicode and then ascii emojis.
    (setq emojify-regexps (list ":[[:alnum:]+_-]+:"
                                (regexp-opt unicode-emojis)
                                (regexp-opt ascii-emojis))))

  (when emojify-user-emojis
    (if (emojify--verify-user-emojis emojify-user-emojis)
        ;; Create entries for user emojis
        (let ((emoji-pairs (mapcar (lambda (user-emoji)
                                     (cons (car user-emoji)
                                           (ht-from-alist (cdr user-emoji))))
                                   emojify-user-emojis)))
          (setq emojify--user-emojis (ht-from-alist emoji-pairs))
          (setq emojify--user-emojis-regexp (regexp-opt (mapcar #'car emoji-pairs))))
      (message "[emojify] User emojis are not in correct format ignoring them.")))

  (emojify-emojis-each (lambda (emoji data)
                         ;; Add the emoji text to data, this makes the values
                         ;; of the `emojify-emojis' standalone containing all
                         ;; data about the emoji
                         (ht-set! data "emoji" emoji)
                         (ht-set! data "custom" (and emojify--user-emojis
                                                     (ht-get emojify--user-emojis emoji)))))

  ;; Clear completion candidates cache
  (setq emojify--completing-candidates-cache nil))

(defvar emojify-emoji-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map [remap delete-char] #'emojify-delete-emoji-forward)
    (define-key map [remap delete-forward-char] #'emojify-delete-emoji-forward)
    (define-key map [remap backward-delete-char] #'emojify-delete-emoji-backward)
    (define-key map [remap org-delete-backward-char] #'emojify-delete-emoji-backward)
    (define-key map [remap delete-backward-char] #'emojify-delete-emoji-backward)
    (define-key map [remap backward-delete-char-untabify] #'emojify-delete-emoji-backward)
    map))

(defun emojify-image-dir ()
  "Get the path to directory containing images for currently selected emoji set."
  (expand-file-name emojify-emoji-set
                    emojify-emojis-dir))

(defun emojify--get-point-col-and-line (point)
  "Return a cons of containing the column number and line at POINT."
  (save-excursion
    (goto-char point)
    (cons (current-column) (line-number-at-pos))))

(defun emojify--get-composed-text (point)
  "Get the text used as composition property at POINT.

This does not check if there is composition property at point the callers should
make sure the point has a composition property otherwise this function will
fail."
  (emojify--string-join (mapcar #'char-to-string
                                (decode-composition-components (nth 2
                                                                    (find-composition point
                                                                                      nil
                                                                                      nil
                                                                                      t))))))

(defun emojify--inside-rectangle-selection-p (beg end)
  "Check if region marked by BEG and END is inside a rectangular selection.

In addition to explicit the parameters BEG and END, calling functions should
also dynamically bind `emojify-region-beg' and `emojify-region-end' to beginning
and end of region respectively."
  (when (and emojify-region-beg
             (bound-and-true-p rectangle-mark-mode))
    (let ((rect-beg (emojify--get-point-col-and-line emojify-region-beg))
          (rect-end (emojify--get-point-col-and-line emojify-region-end))
          (emoji-start-pos (emojify--get-point-col-and-line beg))
          (emoji-end-pos (emojify--get-point-col-and-line end)))
      (or (and (<= (car rect-beg) (car emoji-start-pos))
               (<= (car emoji-start-pos) (car rect-end))
               (<= (cdr rect-beg) (cdr emoji-start-pos))
               (<= (cdr emoji-start-pos) (cdr rect-end)))
          (and (<= (car rect-beg) (car emoji-end-pos))
               (<= (car emoji-end-pos) (car rect-end))
               (<= (cdr rect-beg) (cdr emoji-end-pos))
               (<= (cdr emoji-end-pos) (cdr rect-end)))))))

(defun emojify--inside-non-rectangle-selection-p (beg end)
  "Check if region marked by BEG and END is inside a non-regular selection.

In addition to the explicit parameters BEG and END, calling functions should
also dynamically bind `emojify-region-beg' and `emojify-region-end' to beginning
and end of region respectively."
  (when (and emojify-region-beg
             (region-active-p)
             (not (bound-and-true-p rectangle-mark-mode)))
    (or (and (<  emojify-region-beg beg)
             (<= beg emojify-region-end))
        (and (<  emojify-region-beg end)
             (<= end emojify-region-end)))))

(defun emojify--region-background-maybe (beg end)
  "If the BEG and END falls inside an active region return the region face.

This returns nil if the emojis between BEG and END do not fall in region."
  ;; `redisplay-highlight-region-function' was not defined in Emacs 24.3
  (when (and (or (not (boundp 'redisplay-highlight-region-function))
                 (equal (default-value 'redisplay-highlight-region-function) redisplay-highlight-region-function))
             (or (emojify--inside-non-rectangle-selection-p beg end)
                 (emojify--inside-rectangle-selection-p beg end)))
    (face-background 'region)))

(defun emojify--get-image-background (beg end)
  "Get the color to be used as background for emoji between BEG and END."
  ;; We do a separate check for region since `background-color-at-point'
  ;; does not always detect background color inside regions properly
  (or (emojify--region-background-maybe beg end)
      (save-excursion
        (goto-char beg)
        (background-color-at-point))))

(defun emojify--get-image-display (data buffer beg end &optional target)
  "Get the display text property to display the emoji as an image.

DATA holds the emoji data, _BUFFER is the target buffer where the emoji is to be
displayed, BEG and END delimit the region where emoji will be displayed.  For
explanation of TARGET see the documentation of `emojify--get-text-display-props'.

TODO: Perhaps TARGET should be generalized to work with overlays, buffers and
other different display constructs, for now this works."
  (when (ht-get data "image")
    (let* ((image-file (expand-file-name (ht-get data "image")
                                         (emojify-image-dir)))
           (image-type (intern (upcase (file-name-extension image-file)))))
      (when (file-exists-p image-file)
        (create-image image-file
                      ;; use imagemagick if available and supports PNG images
                      ;; (allows resizing images)
                      (when (and (fboundp 'imagemagick-types)
                                 (memq image-type (imagemagick-types)))
                        'imagemagick)
                      nil
                      :ascent 'center
                      :heuristic-mask t
                      :background (cond ((equal target 'mode-line)
                                         (face-background 'mode-line nil 'default))
                                        (t (emojify--get-image-background beg end)))
                      ;; no-op if imagemagick is  not available
                      :height (cond ((bufferp target)
                                     (with-current-buffer target
                                       (emojify-default-font-height)))
                                    ((equal target 'mode-line)
                                     (emojify-face-height 'mode-line))
                                    (t (with-current-buffer buffer
                                         (emojify-default-font-height)))))))))

(defun emojify--get-unicode-display (data &rest ignored)
  "Get the display text property to display the emoji as an unicode character.

DATA holds the emoji data, rest of the arguments IGNORED are ignored"
  (let* ((unicode (ht-get data "unicode"))
         (characters (when unicode
                       (string-to-vector unicode))))
    (when (seq-every-p #'char-displayable-p characters)
      unicode)))

(defun emojify--get-ascii-display (data &rest ignored)
  "Get the display text property to display the emoji as an ascii characters.

DATA holds the emoji data, rest of the arguments IGNORED are ignored."
  (ht-get data "ascii"))

(defun emojify--get-text-display-props (emoji buffer beg end &optional target)
  "Get the display property for an EMOJI.

BUFFER is the buffer currently holding the EMOJI, BEG and END delimit the region
containing the emoji.  TARGET can either be a buffer object or a special value
mode-line.  It is used to indicate where EMOJI would be displayed, properties
like font-height are inherited from TARGET if provided."
  (funcall (pcase emojify-display-style
             (`image #'emojify--get-image-display)
             (`unicode #'emojify--get-unicode-display)
             (`ascii #'emojify--get-ascii-display))
           emoji
           buffer
           beg
           end
           target))

(defun emojify--propertize-text-for-emoji (emoji text buffer start end &optional target)
  "Display EMOJI for TEXT in BUFFER between START and END.

For explanation of TARGET see the documentation of
`emojify--get-text-display-props'."
  (let ((display-prop
         (emojify--get-text-display-props emoji buffer start end target))
        (buffer-props (unless target
                        (list 'emojify-buffer buffer
                              'emojify-beginning (copy-marker start)
                              'emojify-end (copy-marker end)
                              'yank-handler (list nil text)
                              'keymap emojify-emoji-keymap
                              'help-echo #'emojify-help-function))))
    (when display-prop
      (add-text-properties start
                           end
                           (append (list 'emojified t
                                         'emojify-display display-prop
                                         'display display-prop
                                         'emojify-text text)
                                   buffer-props)))))

(defun emojify-display-emojis-in-region (beg end)
  "Display emojis in region.

BEG and END are the beginning and end of the region respectively.

Displaying happens in two phases, first search based phase displays actual text
appearing in buffer as emojis.  In the next phase composed text is searched for
emojis and displayed.

A minor problem here is that if the text is composed after this display loop it
would not be displayed as emoji, although in practice the two packages that use
the composition property `prettify-symbol-mode' and `org-bullets' use the
font-lock machinery which runs before emojify's display loop, so hopefully this
should not be a problem 🤞."
  (emojify-with-saved-buffer-state
    ;; Make sure we halt if displaying emojis takes more than a second (this
    ;; might be too large duration)
    (with-timeout (1 (emojify-message "Failed to display emojis under 1 second"))
      (seq-doseq (regexp (apply #'append
                                (when emojify--user-emojis-regexp
                                  (list emojify--user-emojis-regexp))
                                (list emojify-regexps)))
        (let (case-fold-search)
          (goto-char beg)
          (while (and (> end (point))
                      (search-forward-regexp regexp end t))
            (let* ((match-beginning (match-beginning 0))
                   (match-end (match-end 0))
                   (match (match-string-no-properties 0))
                   (buffer (current-buffer))
                   (emoji (emojify-get-emoji match))
                   (force-display (get-text-property match-beginning 'emojify-force-display)))
              (when (and emoji
                         (not (or (get-text-property match-beginning 'emojify-inhibit)
                                  (get-text-property match-end 'emojify-inhibit)))
                         (memql (intern (ht-get emoji "style"))
                                emojify-emoji-styles)
                         ;; Skip displaying this emoji if the its bounds are
                         ;; already part of an existing emoji. Since the emojis
                         ;; are searched in descending order of length (see
                         ;; construction of emojify-regexp in `emojify-set-emoji-data'),
                         ;; this means larger emojis get precedence over smaller
                         ;; ones
                         (not (or (get-text-property match-beginning 'emojified)
                                  (get-text-property (1- match-end) 'emojified)))
                         ;; Display unconditionally in non-prog mode
                         (or (not (derived-mode-p 'prog-mode 'tuareg--prog-mode 'comint-mode 'smalltalk-mode))
                             ;; In prog mode enable respecting `emojify-program-contexts'
                             (emojify-valid-program-context-p emoji match-beginning match-end))

                         ;; Display ascii emojis conservatively, since they have potential
                         ;; to be annoying consider d: in head:, except while executing apropos
                         ;; emoji
                         (or (not (string= (ht-get emoji "style") "ascii"))
                             force-display
                             (emojify-valid-ascii-emoji-context-p match-beginning match-end))

                         (or force-display
                             (not (emojify-inside-org-src-p match-beginning)))

                         ;; Inhibit possibly inside a list
                         ;; 41 is ?) but packages get confused by the extra closing paren :)
                         ;; TODO Report bugs to such packages
                         (or force-display
                             (not (and (eq (char-syntax (char-before match-end)) 41)
                                       (emojify-looking-at-end-of-list-maybe match-end))))

                         (not (run-hook-with-args-until-success 'emojify-inhibit-functions match match-beginning match-end)))
                (emojify--propertize-text-for-emoji emoji match buffer match-beginning match-end)))
            ;; Stop a bit to let `with-timeout' kick in
            (sit-for 0 t))))

      ;; Loop to emojify composed text
      (when (and emojify-composed-text-p
                 ;; Skip this if user has disabled unicode style emojis, since
                 ;; we display only composed text that are unicode emojis
                 (memql 'unicode emojify-emoji-styles))
        (goto-char beg)
        (let ((compose-start (if (get-text-property beg 'composition)
                                 ;; Check `beg' first for composition property
                                 ;; since `next-single-property-change' will
                                 ;; search for region after `beg' for property
                                 ;; change thus skipping any composed text at
                                 ;; `beg'
                                 beg
                               (next-single-property-change beg
                                                            'composition
                                                            nil
                                                            end))))
          (while (and (> end (point))
                      ;; `end' would be equal to `compose-start' if there was no
                      ;; text with composition found within `end', this happens
                      ;; because `next-single-property-change' returns the limit
                      ;; (and we use `end' as the limit) if no match is found
                      (> end compose-start)
                      compose-start)
            (let* ((match (emojify--get-composed-text compose-start))
                   (emoji (emojify-get-emoji match))
                   (compose-end (next-single-property-change compose-start 'composition nil end)))
              ;; Display only composed text that is unicode char
              (when (and emoji
                         (string= (ht-get emoji "style") "unicode"))
                (emojify--propertize-text-for-emoji emoji match (current-buffer) compose-start compose-end))
              ;; Setup the next loop
              (setq compose-start (and compose-end (next-single-property-change compose-end
                                                                                'composition
                                                                                nil
                                                                                end)))
              (goto-char compose-end))
            ;; Stop a bit to let `with-timeout' kick in
            (sit-for 0 t)))))))

(defun emojify-undisplay-emojis-in-region (beg end)
  "Undisplay the emojis in region.

BEG and END are the beginning and end of the region respectively"
  (emojify-with-saved-buffer-state
    (while (< beg end)
      ;; Get the start of emojified region in the region, the region is marked
      ;; with text-property `emojified' whose value is `t'. The region is marked
      ;; so that we do not inadvertently remove display or other properties
      ;; inserted by other packages.  This might fail too if a package adds any
      ;; of these properties between an emojified text, but that situation is
      ;; hopefully very rare and this is better than blindly removing all text
      ;; properties
      (let* ((emoji-start (text-property-any beg end 'emojified t))
             ;; Get the end emojified text, if we could not find the start set
             ;; emoji-end to region `end', this merely to make looping easier.
             (emoji-end (or (and emoji-start
                                 (text-property-not-all emoji-start end 'emojified t))
                            ;; If the emojified text is at the end of the region
                            ;; assume that end is the emojified text.
                            end)))
        ;; Proceed only if we got start of emojified text
        (when emoji-start
          ;; Remove the properties
          (remove-text-properties emoji-start emoji-end (append (list 'emojified t
                                                                      'display t
                                                                      'emojify-display t
                                                                      'emojify-buffer t
                                                                      'emojify-text t
                                                                      'emojify-beginning t
                                                                      'emojify-end t
                                                                      'yank-handler t
                                                                      'keymap t
                                                                      'help-echo t
                                                                      'rear-nonsticky t))))
        ;; Setup the next iteration
        (setq beg emoji-end)))))

(defun emojify-redisplay-emojis-in-region (&optional beg end)
  "Redisplay emojis in region between BEG and END.

Redisplay emojis in the visible region if BEG and END are not specified"
  (let* ((area (emojify--get-relevant-region))
         (beg (save-excursion
                (goto-char (or beg (car area)))
                (line-beginning-position)))
         (end (save-excursion
                (goto-char (or end (cdr area)))
                (line-end-position))))
    (unless (> (- end beg) 5000)
      (emojify-execute-ignoring-errors-unless-debug
        (emojify-undisplay-emojis-in-region beg end)
        (emojify-display-emojis-in-region beg end)))))

(defun emojify-after-change-extend-region-function (beg end _len)
  "Extend the region to be emojified.

This simply extends the region to be fontified to the start of line at BEG and
end of line at END.  _LEN is ignored.

The idea is since an emoji cannot span multiple lines, redisplaying complete
lines ensures that all the possibly affected emojis are redisplayed."
  (let ((emojify-jit-lock-start (save-excursion
                                  (goto-char beg)
                                  (line-beginning-position)))
        (emojify-jit-lock-end (save-excursion
                                (goto-char end)
                                (line-end-position))))
    (setq jit-lock-start (if jit-lock-start
                             (min jit-lock-start emojify-jit-lock-start)
                           emojify-jit-lock-start))
    (setq jit-lock-end (if jit-lock-end
                           (max jit-lock-end emojify-jit-lock-end)
                         emojify-jit-lock-end))))



;; Emojify standalone strings

(defun emojify-string (string &optional styles target)
  "Create a propertized version of STRING, to display emojis belonging STYLES.

TARGET can either be a buffer object or a special value mode-line.  It is used
to indicate where EMOJI would be displayed, properties like font-height are
inherited from TARGET if provided.  See also `emojify--get-text-display-props'."
  (emojify-create-emojify-emojis)
  (let ((target (or target (current-buffer))))
    (with-temp-buffer
      (insert string)
      (let ((beg (point-min))
            (end (point-max))
            (styles (or styles '(unicode))))
        (seq-doseq (regexp (apply #'append
                                  (when emojify--user-emojis-regexp
                                    (list emojify--user-emojis-regexp))
                                  (list emojify-regexps)))
          (goto-char beg)
          (while (and (> end (point))
                      (search-forward-regexp regexp end t))
            (let* ((match-beginning (match-beginning 0))
                   (match-end (match-end 0))
                   (match (match-string-no-properties 0))
                   (buffer (current-buffer))
                   (emoji (emojify-get-emoji match)))
              (when (and emoji
                         (not (or (get-text-property match-beginning 'emojify-inhibit)
                                  (get-text-property match-end 'emojify-inhibit)))
                         (memql (intern (ht-get emoji "style")) styles)
                         ;; Skip displaying this emoji if the its bounds are
                         ;; already part of an existing emoji. Since the emojis
                         ;; are searched in descending order of length (see
                         ;; construction of emojify-regexp in `emojify-set-emoji-data'),
                         ;; this means larger emojis get precedence over smaller
                         ;; ones
                         (not (or (get-text-property match-beginning 'emojified)
                                  (get-text-property (1- match-end) 'emojified))))
                (emojify--propertize-text-for-emoji emoji match buffer match-beginning match-end target))))))
      (buffer-string))))



;; Electric delete functionality

(defun emojify--find-key-binding-ignoring-emojify-keymap (key)
  "Find the binding for given KEY ignoring the text properties at point.

This is needed since `key-binding' looks up in keymap text property as well
which is not what we want when falling back in `emojify-delete-emoji'"
  (let* ((key-binding (or (minor-mode-key-binding key)
                          (local-key-binding key)
                          (global-key-binding key))))
    (when key-binding
      (or (command-remapping key-binding
                             nil
                             (seq-filter (lambda (keymap)
                                           (not (equal keymap emojify-emoji-keymap)))
                                         (current-active-maps)))
          key-binding))))

(defun emojify-delete-emoji (point)
  "Delete emoji at POINT."
  (if (get-text-property point 'emojified)
      (delete-region (get-text-property point 'emojify-beginning)
                     (get-text-property point 'emojify-end))
    (call-interactively (emojify--find-key-binding-ignoring-emojify-keymap (this-command-keys)))))

(defun emojify-delete-emoji-forward ()
  "Delete emoji after point."
  (interactive)
  (emojify-delete-emoji (point)))

(defun emojify-delete-emoji-backward ()
  "Delete emoji before point."
  (interactive)
  (emojify-delete-emoji (1- (point))))

;; Integrate with delete-selection-mode
;; Basically instruct delete-selection mode to override our commands
;; if the region is active.
(put 'emojify-delete-emoji-forward 'delete-selection 'supersede)
(put 'emojify-delete-emoji-backward 'delete-selection 'supersede)



;; Updating background color on selection

(defun emojify--update-emojis-background-in-region (&optional beg end)
  "Update the background color for emojis between BEG and END."
  (when (equal emojify-display-style 'image)
    (emojify-with-saved-buffer-state
      (emojify-do-for-emojis-in-region beg end
        (plist-put (cdr (get-text-property emoji-start 'display))
                   :background
                   (emojify--get-image-background emoji-start
                                                  emoji-end))))))

(defun emojify--update-emojis-background-in-region-starting-at (point)
  "Update background color for emojis in buffer starting at POINT.

This updates the emojis in the region starting from POINT, the end of region is
determined by product of `frame-height' and `frame-width' which roughly
corresponds to the visible area.  POINT usually corresponds to the starting
position of the window, see
`emojify-update-visible-emojis-background-after-command' and
`emojify-update-visible-emojis-background-after-window-scroll'

NOTE: `window-text-height' and `window-text-width' would have been more
appropriate here however they were not defined in Emacs v24.3 and below."
  (let* ((region-beginning point)
         (region-end (min (+ region-beginning (* (frame-height)
                                                 (frame-width)))
                          (point-max))))
    (emojify--update-emojis-background-in-region region-beginning
                                                 region-end)))

(defun emojify-update-visible-emojis-background-after-command ()
  "Function added to `post-command-hook' when region is active.

This function updates the backgrounds of the emojis in the region changed after
the command.

Ideally this would have been good enough to update emoji backgounds after region
changes, unfortunately this does not work well with commands that scroll the
window specifically `window-start' and `window-end' (sometimes only `window-end')
report incorrect values.

To work around this
`emojify-update-visible-emojis-background-after-window-scroll' is added to
`window-scroll-functions' to update emojis on window scroll."
  (while-no-input (emojify--update-emojis-background-in-region-starting-at (window-start))))

(defun emojify-update-visible-emojis-background-after-window-scroll (_window display-start)
  "Function added to `window-scroll-functions' when region is active.

This function updates the backgrounds of the emojis in the newly displayed area
of the window.  DISPLAY-START corresponds to the new start of the window."
  (while-no-input (emojify--update-emojis-background-in-region-starting-at display-start)))



;; Lazy image downloading

(defvar emojify--refused-image-download-p nil
  "Used to remember that user has refused to download images in this session.")
(defvar emojify--download-in-progress-p nil
  "Is emoji download in progress used to avoid multiple emoji download prompts.")

(defun emojify--emoji-download-emoji-set (data)
  "Download the emoji images according to DATA."
  (let ((destination (expand-file-name (make-temp-name "emojify")
                                       temporary-file-directory)))
    (url-copy-file (ht-get data "url")
                   destination)
    (let ((downloaded-sha (with-temp-buffer
                            (insert-file-contents-literally destination)
                            (secure-hash 'sha256 (current-buffer)))))
      (when (string= downloaded-sha (ht-get data "sha256"))
        destination))))

(defun emojify--extract-emojis (file)
  "Extract the tar FILE in emoji directory."
  (let* ((default-directory emojify-emojis-dir))
    (with-temp-buffer
      (insert-file-contents-literally file)
      (let ((emojify-inhibit-emojify-in-current-buffer-p t))
        (tar-mode))
      (tar-untar-buffer))))

(defun emojify-download-emoji (emoji-set)
  "Download the provided EMOJI-SET."
  (interactive (list (completing-read "Select the emoji set you want to download: "
                                      (ht-keys emojify-emoji-set-json))))
  (let ((emoji-data (ht-get emojify-emoji-set-json emoji-set)))
    (cond ((not emoji-data)
           (error "No emoji set named %s found" emoji-set))
          ((and (file-exists-p (expand-file-name emoji-set emojify-emojis-dir))
                (called-interactively-p 'any))
           (message "%s emoji-set already downloaded, not downloading again!" emoji-set))
          (t
           (emojify--extract-emojis (emojify--emoji-download-emoji-set (ht-get emojify-emoji-set-json emoji-set)))))))

(defun emojify-download-emoji-maybe ()
  "Download emoji images if needed."
  (when (and (equal emojify-display-style 'image)
             (not (file-exists-p (emojify-image-dir)))
             (not emojify--refused-image-download-p))
    (unwind-protect
        ;; Do not prompt for download if download is in progress
        (unless emojify--download-in-progress-p
          (setq emojify--download-in-progress-p t)
          (if (yes-or-no-p "[emojify] Emoji images not available should I download them now?")
              (emojify-download-emoji emojify-emoji-set)
            ;; Remember that user has refused to download the emojis so that we
            ;; do not ask again in present session
            (setq emojify--refused-image-download-p t)
            (warn "[emojify] Not downloading emoji images for now. Emojis would
not be displayed since images are not available. If you wish to download emojis,
run the command `emojify-download-emoji'")))
      (setq emojify--download-in-progress-p nil))))

(defun emojify-ensure-images ()
  "Ensure that emoji images are downloaded."
  (if after-init-time
      (emojify-download-emoji-maybe)
    (add-hook 'after-init-hook #'emojify-download-emoji-maybe t)))



;; Minor mode definitions

(defun emojify-turn-on-emojify-mode ()
  "Turn on `emojify-mode' in current buffer."

  ;; Calculate emoji data if needed
  (emojify-create-emojify-emojis)

  (when (emojify-buffer-p (current-buffer))
    ;; Download images if not available
    (emojify-ensure-images)

    ;; Install our jit-lock function
    (jit-lock-register #'emojify-redisplay-emojis-in-region)
    (add-hook 'jit-lock-after-change-extend-region-functions #'emojify-after-change-extend-region-function t t)

    ;; Handle point entered behaviour
    (add-hook 'post-command-hook #'emojify-detect-emoji-entry/exit t t)

    ;; Update emoji backgrounds after each command
    (add-hook 'post-command-hook #'emojify-update-visible-emojis-background-after-command t t)

    ;; Update emoji backgrounds after mark is deactivated, this is needed since
    ;; deactivation can happen outside the command loop
    (add-hook 'deactivate-mark-hook #'emojify-update-visible-emojis-background-after-command t t)

    ;; Update emoji backgrounds after when window scrolls
    (add-hook 'window-scroll-functions #'emojify-update-visible-emojis-background-after-window-scroll t t)

    ;; Redisplay emojis after enabling `prettify-symbol-mode'
    (add-hook 'prettify-symbols-mode-hook #'emojify-redisplay-emojis-in-region)

    ;; Redisplay visible emojis when emoji style changes
    (add-hook 'emojify-emoji-style-change-hook #'emojify-redisplay-emojis-in-region)))

(defun emojify-turn-off-emojify-mode ()
  "Turn off `emojify-mode' in current buffer."
  ;; Remove currently displayed emojis
  (save-restriction
    (widen)
    (emojify-undisplay-emojis-in-region (point-min) (point-max)))

  ;; Uninstall our jit-lock function
  (jit-lock-unregister #'emojify-redisplay-emojis-in-region)
  (remove-hook 'jit-lock-after-change-extend-region-functions #'emojify-after-change-extend-region-function t)

  (remove-hook 'post-command-hook #'emojify-detect-emoji-entry/exit t)

  ;; Disable hooks to update emoji backgrounds
  (remove-hook 'post-command-hook #'emojify-update-visible-emojis-background-after-command t)
  (remove-hook 'deactivate-mark-hook #'emojify-update-visible-emojis-background-after-command t)
  (remove-hook 'window-scroll-functions #'emojify-update-visible-emojis-background-after-window-scroll t)

  ;; Remove hook to redisplay emojis after enabling `prettify-symbol-mode'
  (remove-hook 'prettify-symbols-mode-hook #'emojify-redisplay-emojis-in-region)

  ;; Remove style change hooks
  (remove-hook 'emojify-emoji-style-change-hook #'emojify-redisplay-emojis-in-region))

;;;###autoload
(define-minor-mode emojify-mode
  "Emojify mode"
  :init-value nil
  (if emojify-mode
      ;; Turn on
      (emojify-turn-on-emojify-mode)
    ;; Turn off
    (emojify-turn-off-emojify-mode)))

;;;###autoload
(define-globalized-minor-mode global-emojify-mode
  emojify-mode emojify-mode
  :init-value nil)

(defadvice set-buffer-multibyte (after emojify-disable-for-unibyte-buffers (&rest ignored))
  "Disable emojify when unibyte encoding is enabled for a buffer.
Re-enable it when buffer changes back to multibyte encoding."
  (ignore-errors
    (if enable-multibyte-characters
        (when global-emojify-mode
          (emojify-mode +1))
      (emojify-mode -1))))

(ad-activate #'set-buffer-multibyte)



;; Displaying emojis in mode-line

(defun emojify--emojied-mode-line (format)
  "Return an emojified version of mode-line FORMAT.

The format is converted to the actual string to be displayed using
`format-mode-line' and the unicode characters are replaced by images."
  (if emojify-mode
      ;; Remove "%e" from format since we keep it as first part of the
      ;; emojified mode-line, see `emojify-emojify-mode-line'
      (emojify-string (format-mode-line (delq "%e" format)) nil 'mode-line)
    (format-mode-line format)))

(defun emojify-mode-line-emojified-p ()
  "Check if the mode-line is already emojified.

If the `mode-line-format' is of following format

\(\"%e\" (:eval (emojify-emojied-mode-line ... )))

We can assume the mode-line is already emojified."
  (and (consp mode-line-format)
       (equal (ignore-errors (cl-caadr mode-line-format))
              :eval)
       (equal (ignore-errors (car (cl-cadadr mode-line-format)))
              'emojify--emojied-mode-line)))

(defun emojify-emojify-mode-line ()
  "Emojify unicode characters in the mode-line.

This updates `mode-line-format' to a modified version which emojifies the
mode-line before it is displayed."
  (unless (emojify-mode-line-emojified-p)
    (setq mode-line-format `("%e" (:eval
                                   (emojify--emojied-mode-line ',mode-line-format))))))

(defun emojify-unemojify-mode-line ()
  "Restore `mode-line-format' to unemojified version.

This basically reverses the effect of `emojify-emojify-mode-line'."
  (when (emojify-mode-line-emojified-p)
    (setq mode-line-format (cl-cadadr (cl-cadadr mode-line-format)))))

;;;###autoload
(define-minor-mode emojify-mode-line-mode
  "Emojify mode line"
  :init-value nil
  (if emojify-mode-line-mode
      ;; Turn on
      (emojify-emojify-mode-line)
    ;; Turn off
    (emojify-unemojify-mode-line)))

;;;###autoload
(define-globalized-minor-mode global-emojify-mode-line-mode
  emojify-mode-line-mode emojify-mode-line-mode
  :init-value nil)



;; Searching emojis

(defvar emojify-apropos-buffer-name "*Apropos Emojis*")

(defun emojify-apropos-quit ()
  "Delete the window displaying Emoji search results."
  (interactive)
  (if (= (length (window-list)) 1)
      (bury-buffer)
    (quit-window)))

(defun emojify-apropos-copy-emoji ()
  "Copy the emoji being displayed at current line in apropos results."
  (interactive)
  (save-excursion
    (goto-char (line-beginning-position))
    (if (not (get-text-property (point) 'emojified))
        (emojify-user-error "No emoji at point")
      (kill-new (get-text-property (point) 'emojify-text))
      (message "Copied emoji (%s) to kill ring!"
               (get-text-property (point) 'emojify-text)))))

(defun emojify-apropos-describe-emoji ()
  "Copy the emoji being displayed at current line in apropos results."
  (interactive)
  (save-excursion
    (goto-char (line-beginning-position))
    (if (not (get-text-property (point) 'emojified))
        (emojify-user-error "No emoji at point")
      (emojify-describe-emoji (get-text-property (point) 'emojify-text)))))

(defvar emojify-apropos-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map emojify-common-mode-map)
    (define-key map "c" #'emojify-apropos-copy-emoji)
    (define-key map "w" #'emojify-apropos-copy-emoji)
    (define-key map "d" #'emojify-apropos-describe-emoji)
    (define-key map (kbd "RET") #'emojify-apropos-describe-emoji)
    (define-key map "g" #'emojify-apropos-emoji)
    map)
  "Keymap used in `emojify-apropos-mode'.")

(define-derived-mode emojify-apropos-mode fundamental-mode "Apropos Emojis"
  "Mode used to display results of `emojify-apropos-emoji'

\\{emojify-apropos-mode-map}"
  (emojify-mode +1)
  ;; view mode being a minor mode eats up our bindings avoid it
  (let (view-read-only)
    (read-only-mode +1)))

(put 'emojify-apropos-mode 'mode-class 'special)

(defvar emojify--apropos-last-query nil)
(make-variable-buffer-local 'emojify--apropos-last-query)

(defun emojify-apropos-read-pattern ()
  "Read apropos pattern with INITIAL-INPUT as the initial input.

Borrowed from apropos.el"
  (let ((pattern (read-string (concat "Search for emoji (word list or regexp): ")
                              emojify--apropos-last-query)))
    (if (string-equal (regexp-quote pattern) pattern)
        (or (split-string pattern "[ \t]+" t)
            (emojify-user-error "No word list given"))
      pattern)))

;;;###autoload
(defun emojify-apropos-emoji (pattern)
  "Show Emojis that match PATTERN."
  (interactive (list (emojify-apropos-read-pattern)))

  (emojify-create-emojify-emojis)

  (let ((in-apropos-buffer-p (equal major-mode 'emojify-apropos-mode))
        matching-emojis
        sorted-emojis)

    (unless (listp pattern)
      (setq pattern (list pattern)))

    ;; Convert the user entered text to a regex to match the emoji name or
    ;; description
    (apropos-parse-pattern pattern)

    ;; Collect matching emojis in a list of (list score emoji emoji-data)
    ;; elements, where score is the proximity of the emoji to given pattern
    ;; calculated using `apropos-score-str'
    (emojify-emojis-each (lambda (key value)
                           (when (or (string-match apropos-regexp key)
                                     (string-match apropos-regexp (ht-get value "name")))
                             (push (list (max (apropos-score-str key)
                                              (apropos-score-str (ht-get value "name")))
                                         key
                                         value)
                                   matching-emojis))))

    ;; Sort the emojis by the proximity score
    (setq sorted-emojis (mapcar #'cdr
                                (sort matching-emojis
                                      (lambda (emoji1 emoji2)
                                        (> (car emoji1) (car emoji2))))))

    ;; Insert result in apropos buffer and display it
    (with-current-buffer (get-buffer-create emojify-apropos-buffer-name)
      (let ((inhibit-read-only t)
            (query (mapconcat 'identity pattern " ")))
        (erase-buffer)
        (insert (propertize "Emojis matching" 'face 'apropos-symbol))
        (insert (format " - \"%s\"" query))
        (insert "\n\nUse `c' or `w' to copy emoji on current line\nUse `g' to rerun apropos\n\n")
        (dolist (emoji sorted-emojis)
          (insert (format "%s - %s (%s)"
                          (car emoji)
                          (ht-get (cadr emoji) "name")
                          (ht-get (cadr emoji) "style")))
          (insert "\n"))
        (goto-char (point-min))
        (forward-line (1- 6))
        (emojify-apropos-mode)
        (setq emojify--apropos-last-query (concat query " "))
        (setq-local line-spacing 7)))

    (pop-to-buffer (get-buffer emojify-apropos-buffer-name)
                   (when in-apropos-buffer-p
                     (cons #'display-buffer-same-window nil)))))



;; Inserting emojis

(defun emojify--completing-read-minibuffer-setup-hook ()
  "Enables `emojify-mode' in minbuffer while inserting emojis.

This ensures `emojify' is enabled even when `global-emojify-mode' is not on."
  (emojify-mode +1))

(defun emojify--completing-read-helm-hook ()
  "Enables `emojify-mode' in helm buffer.

This ensures `emojify' is enabled in helm buffer displaying completion even when
`global-emojify-mode' is not on."
  (with-current-buffer helm-buffer
    (emojify-mode +1)))

(defun emojify-completing-read (prompt &optional predicate require-match initial-input hist def inherit-input-method)
  "Read emoji from the user and return the selected emoji.

PROMPT is a string to prompt with, PREDICATE, REQUIRE-MATCH, INITIAL-INPUT,
HIST, DEF, INHERIT-INPUT-METHOD correspond to the arguments for
`completing-read' and are passed to ‘completing-read’ without any
interpretation.

For each possible emoji PREDICATE is called with emoji text and data about the
emoji as a hash-table, the predate should return nil if it the emoji should
not be displayed for selection.

For example the following can be used to display only github style emojis for
selection

\(emojify-completing-read \"Select a Github style emoji: \"
                         (lambda (emoji data)
                           (equal (gethash \"style\" data) \"github\")))

This function sets up `ido', `icicles', `helm', `ivy' and vanilla Emacs
completion UI to display properly emojis."
  (emojify-create-emojify-emojis)
  (let* ((emojify-minibuffer-reading-emojis-p t)
         (line-spacing 7)
         (completion-ignore-case t)
         (candidates (emojify--get-completing-read-candidates))
         ;; Vanilla Emacs completion and Icicles use the completion list mode to display candidates
         ;; the following makes sure emojify is enabled in the completion list
         (completion-list-mode-hook (cons #'emojify--completing-read-minibuffer-setup-hook
                                          completion-list-mode-hook))
         ;; (Vertical) Ido and Ivy displays candidates in minibuffer this makes sure candidates are emojified
         ;; when Ido or Ivy are used
         (minibuffer-setup-hook (cons #'emojify--completing-read-minibuffer-setup-hook
                                      minibuffer-setup-hook))
         (helm-after-initialize-hook (cons #'emojify--completing-read-helm-hook
                                           (bound-and-true-p helm-after-initialize-hook))))
    (car (split-string (completing-read prompt
                                        candidates
                                        predicate
                                        require-match
                                        initial-input
                                        hist
                                        def
                                        inherit-input-method)
                       " "))))

;;;###autoload
(defun emojify-insert-emoji ()
  "Interactively prompt for Emojis and insert them in the current buffer.

This respects the `emojify-emoji-styles' variable."
  (interactive)
  (insert (emojify-completing-read "Insert Emoji: ")))



;; Describing emojis

(defvar emojify-help-buffer-name "*Emoji Help*")

(defvar-local emojify-described-emoji nil)

(defun emojify-description-copy-emoji ()
  "Copy the emoji being displayed at current line in apropos results."
  (interactive)
  (save-excursion
    (kill-new emojify-described-emoji)
    (message "Copied emoji (%s) to kill ring!" emojify-described-emoji)))

(defvar emojify-description-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map emojify-common-mode-map)
    (define-key map "c" #'emojify-description-copy-emoji)
    (define-key map "w" #'emojify-description-copy-emoji)
    map)
  "Keymap used in `emojify-description-mode'.")

(define-derived-mode emojify-description-mode fundamental-mode "Describe Emoji"
  "Mode used to display results of description for emojis.

\\{emojify-description-mode-map}"
  (emojify-mode +1)
  ;; view mode being a minor mode eats up our bindings avoid it
  (let (view-read-only)
    (read-only-mode +1))
  (goto-address-mode +1))

(put 'emojify-description-mode 'mode-class 'special)

(defun emojify--display-emoji-description-buffer (emoji)
  "Display description for EMOJI."
  (with-current-buffer (get-buffer-create emojify-help-buffer-name)
    (let ((inhibit-read-only t))
      (erase-buffer)
      (save-excursion
        (insert (propertize (ht-get emoji "emoji") 'emojify-inhibit t)
                " - Displayed as "
                (propertize (ht-get emoji "emoji") 'emojify-force-display t)
                "\n\n")
        (insert (propertize "Name" 'face 'font-lock-keyword-face)
                ": "
                (ht-get emoji "name") "\n")
        (insert (propertize "Style" 'face 'font-lock-keyword-face)
                ": "
                (ht-get emoji "style") "\n")
        (insert (propertize "Image used" 'face 'font-lock-keyword-face)
                ": "
                (expand-file-name (ht-get emoji "image")
                                  (emojify-image-dir))
                "\n")
        (when (and (not (string= (ht-get emoji "style") "unicode"))
                   (ht-get emoji "unicode"))
          (insert (propertize "Unicode representation"
                              'face 'font-lock-keyword-face)
                  ": "
                  (propertize (ht-get emoji "unicode") 'emojify-inhibit t)
                  "\n"))
        (when (and (not (string= (ht-get emoji "style") "ascii"))
                   (ht-get emoji "ascii"))
          (insert (propertize "Ascii representation"
                              'face 'font-lock-keyword-face)
                  ": "
                  (propertize (ht-get emoji "ascii") 'emojify-inhibit t)
                  "\n"))
        (insert (propertize "User defined"
                            'face 'font-lock-keyword-face)
                ": "
                (if (ht-get emoji "custom") "Yes" "No")
                "\n")
        (unless (ht-get emoji "custom")
          (when (or (ht-get emoji "unicode")
                    (string= (ht-get emoji "style") "unicode"))
            (insert (propertize "Unicode Consortium" 'face 'font-lock-keyword-face)
                    ": "
                    (concat "http://www.unicode.org/emoji/charts-beta/full-emoji-list.html#"
                            (string-join (mapcar (apply-partially #'format "%x")
                                                 (string-to-list (or (ht-get emoji "unicode")
                                                                     (ht-get emoji "emoji"))))
                                         "_"))
                    "\n"))
          (insert (propertize "Emojipedia" 'face 'font-lock-keyword-face)
                  ": "
                  (let* ((tone-stripped (replace-regexp-in-string "- *[Tt]one *\\([0-9]+\\)$"
                                                                  "- type \\1"
                                                                  (ht-get emoji "name")))
                         (non-alphanumeric-stripped (replace-regexp-in-string "[^0-9a-zA-Z]"
                                                                              " "
                                                                              tone-stripped))
                         (words (split-string non-alphanumeric-stripped " " t " ")))
                    (concat "http://emojipedia.org/"
                            (downcase (emojify--string-join words "-"))))
                  "\n"))))
    (emojify-description-mode)
    (setq emojify-described-emoji (ht-get emoji "emoji")))
  (display-buffer (get-buffer emojify-help-buffer-name))
  (get-buffer emojify-help-buffer-name))

(defun emojify-describe-emoji (emoji-text)
  "Display description for EMOJI-TEXT."
  (interactive (list (emojify-completing-read "Describe Emoji: ")))
  (if (emojify-get-emoji emoji-text)
      (emojify--display-emoji-description-buffer (emojify-get-emoji emoji-text))
    (emojify-user-error "No emoji found for '%s'" emoji-text)))

(defun emojify-describe-emoji-at-point ()
  "Display help for EMOJI displayed at point."
  (interactive)
  (if (not (get-text-property (point) 'emojified))
      (emojify-user-error "No emoji at point!")
    (emojify--display-emoji-description-buffer (emojify-get-emoji (get-text-property (point) 'emojify-text)))))



;; Listing emojis

(defun emojify-list-copy-emoji ()
  "Copy the emoji being displayed at current line in apropos results."
  (interactive)
  (save-excursion
    (let ((emoji (get-text-property (point) 'tabulated-list-id)))
      (if (not emoji)
          (emojify-user-error "No emoji at point")
        (kill-new emoji)
        (message "Copied emoji (%s) to kill ring!" emoji)))))

(defun emojify-list-describe-emoji ()
  "Copy the emoji being displayed at current line in apropos results."
  (interactive)
  (save-excursion
    (let ((emoji (get-text-property (point) 'tabulated-list-id)))
      (if (not emoji)
          (emojify-user-error "No emoji at point")
        (emojify-describe-emoji emoji)))))

(defvar-local emojify-list--emojis-displayed nil
  "Record that emojis have been successfully displayed in the current buffer.

`emojify-list-emojis' checks to this decide if it should print the entries
again.")

(defun emojify-list-force-refresh ()
  "Force emoji list to be refreshed."
  (interactive)
  (setq emojify-list--emojis-displayed nil)
  (emojify-list-emojis))

(defvar emojify-list-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map emojify-common-mode-map)
    (define-key map "c" #'emojify-list-copy-emoji)
    (define-key map "w" #'emojify-list-copy-emoji)
    (define-key map "d" #'emojify-list-describe-emoji)
    (define-key map "g" #'emojify-list-force-refresh)
    (define-key map (kbd "RET") #'emojify-list-describe-emoji)
    map)
  "Keymap used in `emojify-list-mode'.")

(defun emojify-list-printer (id cols)
  "Printer used to print the emoji rows in tabulated list.

See `tabulated-list-print-entry' to understand the arguments ID and COLS."
  (let ((beg (point))
        (padding (max tabulated-list-padding 0))
        (inhibit-read-only t))
    (when (> tabulated-list-padding 0)
      (insert (make-string padding ?\s)))

    (tabulated-list-print-col 0
                              (propertize (aref cols 0) 'emojify-inhibit t)
                              (current-column))

    ;; Inhibit display of second column ("Text") as emoji
    (tabulated-list-print-col 1
                              (propertize (aref cols 1) 'emojify-inhibit t)
                              (current-column))

    ;; The type of this emoji
    (tabulated-list-print-col 2
                              (aref cols 2)
                              (current-column))

    ;; Is this a custom emoji
    (tabulated-list-print-col 3
                              (aref cols 3)
                              (current-column))

    ;; Force display of last column ("Display") as emoji
    (tabulated-list-print-col 4
                              (propertize (aref cols 4) 'emojify-force-display t)
                              (current-column))

    (insert ?\n)
    (add-text-properties beg
                         (point)
                         `(tabulated-list-id ,id tabulated-list-entry ,cols))

    (message "Listing emojis (%d of %d) ..." (1- (line-number-at-pos)) (aref cols 5))))

(defun emojify-list-entries ()
  "Return entries to display in tabulated list."
  (emojify-create-emojify-emojis)

  (let (entries count)
    (emojify-emojis-each (lambda (emoji data)
                           (push (list emoji (vector (ht-get data "name")
                                                     emoji
                                                     (ht-get data "style")
                                                     (if (ht-get data "custom") "Yes" "No")
                                                     emoji))
                                 entries)))

    (setq count (length entries))

    (mapcar (lambda (entry)
              (list (car entry) (vconcat (cadr entry) (vector count))))
            entries)))

(define-derived-mode emojify-list-mode tabulated-list-mode "Emoji-List"
  "Major mode for listing emojis.
\\{emojify-list-mode-map}"
  (setq line-spacing 7
        tabulated-list-format [("Name" 30 t)
                               ("Text" 20 t)
                               ("Style" 10 t)
                               ("Custom" 10 t)
                               ("Display" 20 nil)]
        tabulated-list-sort-key (cons "Name" nil)
        tabulated-list-padding 2
        tabulated-list-entries #'emojify-list-entries
        tabulated-list-printer #'emojify-list-printer)
  (tabulated-list-init-header))

(defun emojify-list-emojis ()
  "List emojis in a tabulated view."
  (interactive)
  (let ((buffer (get-buffer-create "*Emojis*")))
    (with-current-buffer buffer
      (unless emojify-list--emojis-displayed
        (emojify-list-mode)
        (tabulated-list-print)
        (setq emojify-list--emojis-displayed t))
      (pop-to-buffer buffer))))



;; Integration with company mode

(defadvice company-pseudo-tooltip-unhide (after emojify-display-emojis-in-company-tooltip (&rest ignored))
  "Advice to display emojis in company mode tooltips.

This function does two things, first it adds text properties to the completion
tooltip to make it display the emojis, secondly it makes company always render
the completion tooltip using `after-string' overlay property rather than
`display' text property.

The second step is needed because emojify displays the emojis using `display'
text property, similarly company-mode in some cases uses `display' overlay
property to render its pop, this results into a `display' property inside
`display' property, however Emacs ignores recursive display text property.
Using `after-string' works as well as `display' while allowing the emojis to be
displayed."
  (when (and emojify-mode
             emojify-company-tooltips-p
             (overlayp (bound-and-true-p company-pseudo-tooltip-overlay)))
    (let* ((ov company-pseudo-tooltip-overlay)
           (disp (or (overlay-get ov 'display)
                     (overlay-get ov 'after-string)))
           (emojified-display (when disp
                                (emojify-string disp)))
           (emojified-p (when emojified-display
                          (text-property-any 0 (1- (length emojified-display))
                                             'emojified t
                                             emojified-display))))
      ;; Do not switch to after-string if menu is not emojified
      (when (and disp emojified-p)
        (overlay-put ov 'after-string nil)
        (overlay-put ov 'display (propertize " " 'invisible t))
        (overlay-put ov 'after-string emojified-display)))))

(ad-activate #'company-pseudo-tooltip-unhide)



;; Integration with some miscellaneous functionality

(defadvice mouse--drag-set-mark-and-point (after emojify-update-emoji-background (&rest ignored))
  "Advice to update emoji backgrounds after selection is changed using mouse.

Currently there are no hooks run after mouse movements, as such the emoji
backgrounds are updated only after the mouse button is released.  This advices
`mouse--drag-set-mark-and-point' which is run after selection changes to trigger
an update of emoji backgrounds.  Not the cleanest but the only way I can think of."
  (when emojify-mode
    (emojify-update-visible-emojis-background-after-command)))

(ad-activate #'mouse--drag-set-mark-and-point)

(defadvice text-scale-increase (after emojify-resize-emojis (&rest ignored))
  "Advice `text-scale-increase' to resize emojis on text resize."
  (when emojify-mode
    (let ((new-font-height (emojify-default-font-height)))
      (emojify-do-for-emojis-in-region (point-min) (point-max)
        (plist-put (cdr (get-text-property emoji-start 'display))
                   :height
                   new-font-height)))))

(ad-activate #'text-scale-increase)



(provide 'emojify)
;;; emojify.el ends here
