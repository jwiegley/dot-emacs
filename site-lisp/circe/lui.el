;;; lui.el --- Linewise User Interface -*- lexical-binding: t -*-

;; Copyright (C) 2005 - 2016  Jorgen Schaefer

;; Author: Jorgen Schaefer <forcer@forcix.cx>
;; URL: https://github.com/jorgenschaefer/circe/wiki/Lui

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

;; Lui is a library for other Emacs Lisp programs and not useful by
;; itself.

;; This major mode provides a user interface for applications. The
;; user interface is quite simple, consisting of an input line, a
;; prompt, and some output area, but Lui includes a lot of common
;; options, such as time stamps, filling, colorization, etc.

;; Application programs should create modes derived from lui-mode.

;; The application API consists of:

;; lui-mode
;; lui-set-prompt
;; lui-insert
;; lui-input-function
;; lui-completion-function
;; lui-time-stamp-time
;; lui-time-stamp-zone
;; and the 'lui-fool and 'lui-do-not-track text properties

;;; Code:

(require 'button)
(require 'flyspell)
(require 'help-mode)
(require 'ispell)
(require 'paren)
(require 'ring)
(require 'thingatpt)
(require 'rx)

(require 'tracking)


;;;;;;;;;;;;;;;;;;;;;
;;; Customization ;;;
;;;;;;;;;;;;;;;;;;;;;

(defgroup lui nil
  "The Linewise User Interface."
  :prefix "lui-"
  :group 'applications)

(defcustom lui-scroll-behavior t
  "Set the behavior lui should exhibit for scrolling.

The following values are possible. If in doubt, use post-output.

nil
  Use default Emacs scrolling.

post-command
  Keep the input line at the end of the window if point is
  after the input mark.

post-output
  Keep the input line at the end of the window only after output.

t
  Combine both post-command and post-output.

post-scroll
  Keep the input line at the end of the window on every scroll
  event. Careful, this might interact badly with other functions
  on `window-scroll-functions'.


It would be entirely sensible for Emacs to provide a setting to
do this kind of scrolling by default in a buffer. It seems rather
intuitive and sensible. But as noted on emacs-devel:

  [T]hose who know the code know that it's going to be a pain to
  implement, especially if you want acceptable performance. IOW,
  patches welcome

The full discussion can be found here:

https://lists.gnu.org/archive/html/emacs-devel/2012-10/msg00652.html

These settings are all hacks that try to give the user the choice
between most correct behavior (post-scroll) and most compliant
behavior (post-output)."
  :type '(choice (const :tag "Post Command" t)
                 (const :tag "Post Output" post-output)
                 (const :tag "Post Scroll" post-scroll)
                 (const :tag "Use default scrolling" nil))
  :group 'lui)
(defvaralias 'lui-scroll-to-bottom-p 'lui-scroll-behavior)

(defcustom lui-flyspell-p nil
  "Non-nil if Lui should spell-check your input.
See the function `flyspell-mode' for more information."
  :type 'boolean
  :group 'lui)

(defcustom lui-flyspell-alist nil
  "Alist of buffer dictionaries.

This is a list of mappings from buffers to dictionaries to use
for the function `flyspell-mode'. The appropriate dictionary is
automatically used when Lui is activated in a buffer with a
matching buffer name.

The entries are of the form (REGEXP DICTIONARY), where REGEXP
must match a buffer name, and DICTIONARY specifies an existing
dictionary for the function `flyspell-mode'. See
`ispell-local-dictionary-alist' and `ispell-dictionary-alist' for
a valid list of dictionaries."
  :type 'string
  :group 'lui)

(defcustom lui-highlight-keywords nil
  "A list of keywords to highlight.

This specifies a list of keywords that Lui should highlight. Each
entry is of one of the following forms (similar to
`font-lock-keywords'):

  REGEXP
    Highlight every match in `lui-highlight-face'
  (REGEXP SUBMATCH)
    Highlight the SUBMATCH (a number) in REGEXP in
    `lui-highlight-face'
  (REGEXP FACE)
    Highlight everything matching REGEXP in FACE (a symbol)
  (REGEXP SUBMATCH FACE)
    Highlight the SUBMATCH in REGEXP in FACE

In all of these cases, the FACE can also be a property list which
is then associated with the match.

All matches are run, which means later matches can override
changes by earlier ones."
  :type '(repeat (choice
                  (string :tag "Regular Expression")
                  (list :tag "Submatch"
                        (string :tag "Regular Expression")
                        (integer :tag "Submatch"))
                  (list :tag "Regular Expression in Specific Face"
                        (string :tag "Regular Expression")
                        (face :tag "Face"))
                  (list :tag "Submatch in Specific Face"
                        (string :tag "Regular Expression")
                        (integer :tag "Submatch")
                        (face :tag "Face"))))
  :group 'lui)

(defface lui-strong-face
  '((t (:inherit bold)))
  "Face used for strong markup."
  :group 'lui-irc-colors)

(defface lui-emphasis-face
  '((t (:inherit italic)))
  "Face for emphasis markup."
  :group 'lui-irc-colors)

(defface lui-deleted-face
  '((t (:strike-through t)))
  "Face for deleted messages"
  :group 'lui-irc-colors)

(defcustom lui-formatting-list nil
  "List of enabled formatting types.
Each list item is a list consisting of a regular expression
matching the highlighted text, an integer for the submatch and a
face for highlighting the match."
  :type `(set
          (const :tag "*Strong* text"
                 (,(rx (or bol whitespace)
                       (group "*" (+? (not (any whitespace "*"))) "*")
                       (or eol whitespace))
                  1 lui-strong-face))
          (const :tag "_Emphasized_ text"
                 (,(rx (or bol whitespace)
                       (group "_" (+? (not (any whitespace "_"))) "_")
                       (or eol whitespace))
                  1 lui-emphasis-face)))
  :group 'lui)

(defcustom lui-buttons-list
  `(("`\\([A-Za-z0-9+=*/-]+\\)'" 1
     lui-button-elisp-symbol 1)
    ("\\<debbugs[#:]\\([0-9]+\\)" 0
     "https://debbugs.gnu.org/cgi/bugreport.cgi?bug=%s" 1)
    ("\\<RFC ?\\([0-9]+\\)" 0
     "http://www.ietf.org/rfc/rfc%s.txt" 1)
    ("\\<CVE[- ]\\([0-9]+-[0-9]+\\)" 0
     "https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-%s" 1)
    ("\\<SRFI[- ]?\\([0-9]+\\)" 0
     "http://srfi.schemers.org/srfi-%s/srfi-%s.html" 1 1)
    ("\\<PEP[- ]?\\([0-9]+\\)" 0 lui-button-pep 1)
    ("\\<xkcd[ #]*\\([0-9]+\\)" 0
     "https://xkcd.com/%s" 1)
    ("\\([0-9a-zA-Z_.-]+/[0-9a-zA-Z_.-]+\\)#\\([0-9]+\\)" 0
     "https://github.com/%s/issues/%s" 1 2))
  "The list of buttons to buttonize.
This consists of lists of four elements each:

  (REGEXP SUBMATCH FUNCTION ARG-MATCH...)

Whenever REGEXP is found, SUBMATCH is marked as a button. When
that button is activated, FUNCTION is called with the matches
specified in ARG-MATCHES as its arguments.

If FUNCTION is a string, it is formatted with %s replaced by
the matches in ARG-MATCHES."
  :type '(repeat (list (regexp :tag "Regular expression")
                       (integer :tag "Submatch to buttonize")
                       (function :tag "Function to call for this button")
                       (integer :tag "Submatch to pass as an argument")))
  :group 'lui)

(defcustom lui-button-issue-tracker nil
  "A tracker URL for the current channel.

This will cause simple #123 links to highlight as issue links to
the given repository. Use %s to insert the actual number."
  :type 'string
  :group 'lui)

(defcustom lui-fill-type "    "
  "How Lui should fill its output.
This can be one of the following values:

  A string
      This is used as the fill prefix
  'variable
      The first sequence of non-whitespace characters in the
      output is used as an alignment, and the rest is filled with
      spaces.
  A number
      The first sequence of non-whitespace characters is
      right-aligned at this column, and the rest is filled to
      this column.
  nil
      Turn filling off."
  :type '(choice (string :tag "Fill Prefix")
                 (const :tag "Variable Fill Prefix" variable)
                 (integer :tag "Fill Column")
                 (const :tag "No filling" nil))
  :group 'lui)

(defcustom lui-fill-column 70
  "The column at which Lui should break output.
See `fill-column'."
  :type 'integer
  :group 'lui)

(defcustom lui-fill-remove-face-from-newline t
  "Non-nil when filling should remove faces from newlines.
Faces on a newline extend to the end of the displayed line, which
is often not was is wanted."
  :type 'boolean
  :group 'lui)

(defcustom lui-time-stamp-format "[%H:%M]"
  "The format of time stamps.
See `format-time-string' for a full description of available
formatting directives."
  :type 'string
  :group 'lui)

(defcustom lui-time-stamp-position 'right
  "Where Lui should put time-stamps.
This can be one of the following values:

  A number
      At this column of the first line of output
  'right
      At a column just right to `lui-fill-column'
  'left
      At the left side of the output. The output is thereby moved
      to the right.
  'right-margin
      In the right margin.  You will need to set `right-margin-width'
      in all circe buffers.
  'left-margin
      In the left margin.  You will need to set `left-margin-width'
      in all circe buffers.
  nil
      Do not add any time stamp."
  :type '(choice (const :tag "Right" right)
                 (integer :tag "Column")
                 (const :tag "Left" left)
                 (const :tag "Right Margin" right-margin)
                 (const :tag "Left Margin" left-margin)
                 (const :tag "None" nil))
  :group 'lui)

(defcustom lui-time-stamp-only-when-changed-p t
  "Non-nil if Lui should only add a time stamp when the time changes.
If `lui-time-stamp-position' is 'left, this will still add the
necessary whitespace."
  :type 'boolean
  :group 'lui)

(defcustom lui-read-only-output-p t
  "Non-nil if Lui should make the output read-only.
Switching this off makes copying (by killing) easier for some."
  :type 'boolean
  :group 'lui)

(defcustom lui-max-buffer-size 102400
  "Non-nil if Lui should truncate the buffer if it grows too much.
If the buffer size (in characters) exceeds this number, it is
truncated at the top."
  :type '(choice (const :tag "Never Truncate" nil)
                 (integer :tag "Maximum Buffer Size"))
  :group 'lui)

(defcustom lui-input-ring-size 32
  "The size of the input history of Lui.
This is the size of the input history used by
\\[lui-previous-input] and \\[lui-next-input]."
  :type 'integer
  :group 'lui)

(defcustom lui-mode-hook nil
  "The hook run when Lui is started."
  :type 'hook
  :group 'lui)

(defcustom lui-pre-input-hook nil
  "A hook run before Lui interprets the user input.
It is called with the buffer narrowed to the input line.
Functions can modify the input if they really want to, but the
user won't see the modifications, so that's a bad idea."
  :type 'hook
  :group 'lui)

(defcustom lui-pre-output-hook nil
  "The hook run before output is formatted."
  :type 'hook
  :group 'lui)

(defcustom lui-post-output-hook nil
  "The hook run after output has been formatted."
  :type 'hook
  :group 'lui)

(defface lui-time-stamp-face
  '((t (:foreground "SlateBlue" :weight bold)))
  "Lui mode face used for time stamps."
  :group 'lui)

(defface lui-highlight-face
  ;; Taken from `font-lock-keyword-face'
  '((((class grayscale) (background light)) (:foreground "LightGray" :weight bold))
    (((class grayscale) (background dark)) (:foreground "DimGray" :weight bold))
    (((class color) (background light)) (:foreground "Purple"))
    (((class color) (background dark)) (:foreground "Cyan1"))
    (t (:weight bold)))
  "Lui mode face used for highlighting."
  :group 'lui)

(defface lui-button-face
  '((((class color) (background light)) (:foreground "Purple" :underline t))
    (((class color) (background dark)) (:foreground "Cyan" :underline t))
    (t (:underline t)))
  "Default face used for LUI buttons."
  :group 'lui)


;;;;;;;;;;;;;;;;;;;;;;;;
;;; Client interface ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lui-input-function nil
  "The function to be called for Lui input.
This function is called with a single argument, the input
string.")
(make-variable-buffer-local 'lui-input-function)

(defvar lui-completion-function 'completion-at-point
  "A function called to actually do completion.")


;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Private variables ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lui-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") 'lui-send-input)
    (define-key map (kbd "TAB") 'lui-next-button-or-complete)
    (define-key map (kbd "<backtab>") 'lui-previous-button)
    (define-key map (kbd "<S-tab>") 'lui-previous-button)
    (define-key map (kbd "M-p") 'lui-previous-input)
    (define-key map (kbd "M-n") 'lui-next-input)
    (define-key map (kbd "C-c C-u") 'lui-kill-to-beginning-of-line)
    (define-key map (kbd "C-c C-i") 'lui-fool-toggle-display)
    map)
  "The key map used in Lui modes.")

(defvar lui-input-marker nil
  "The marker where input should be inserted.")
(make-variable-buffer-local 'lui-input-marker)

(defvar lui-output-marker nil
  "The marker where output should be inserted.
Use `lui-insert' instead of accessing this marker directly.")
(make-variable-buffer-local 'lui-output-marker)

(defvar lui-input-ring nil
  "The input history ring.")
(make-variable-buffer-local 'lui-input-ring)

(defvar lui-input-ring-index nil
  "The index to the current item in the input ring.")
(make-variable-buffer-local 'lui-input-ring-index)


;;;;;;;;;;;;;;
;;; Macros ;;;
;;;;;;;;;;;;;;

(defmacro lui-save-undo-list (&rest body)
  "Run BODY without modifying the undo list."
  (let ((old-marker-sym (make-symbol "old-marker")))
    `(let ((,old-marker-sym (marker-position lui-input-marker))
           (val nil))
       ;; Don't modify the undo list. The undo list is for the user's
       ;; input only.
       (let ((buffer-undo-list t))
         (setq val (progn ,@body)))
       (when (consp buffer-undo-list)
         ;; Not t :-)
         (lui-adjust-undo-list  ,old-marker-sym (- lui-input-marker
                                                   ,old-marker-sym)))
       val)))


;;;;;;;;;;;;;;;;;;
;;; Major Mode ;;;
;;;;;;;;;;;;;;;;;;

(define-derived-mode lui-mode nil "LUI"
  "The Linewise User Interface mode.
This can be used as a user interface for various applications.
Those should define derived modes of this, so this function
should never be called directly.

It can be customized for an application by specifying a
`lui-input-function'."
  (setq lui-input-marker (make-marker)
        lui-output-marker (make-marker)
        lui-input-ring (make-ring lui-input-ring-size)
        lui-input-ring-index nil
        flyspell-generic-check-word-p 'lui-flyspell-check-word-p)
  (set-marker lui-input-marker (point-max))
  (set-marker lui-output-marker (point-max))
  (add-hook 'window-scroll-functions 'lui-scroll-window nil t)
  (add-hook 'post-command-hook 'lui-scroll-post-command)
  (add-hook 'change-major-mode-hook 'lui-change-major-mode nil t)
  (lui-paren-highlighting)
  (lui-time-stamp-enable-filtering)
  (tracking-mode 1)
  (auto-fill-mode 0)
  (when (fboundp 'cursor-intangible-mode)
    (cursor-intangible-mode 1))
  (when lui-flyspell-p
    (require 'flyspell)
    (lui-flyspell-change-dictionary)))

(defun lui-change-major-mode ()
  "Assure that the user really wants to change the major mode.
This is a good value for a buffer-local `change-major-mode-hook'."
  (when (not (y-or-n-p "Really change major mode in a Lui buffer? "))
    (error "User disallowed mode change")))

(defun lui-scroll-window (window _display-start)
  "Scroll the input line to the bottom of the WINDOW.

DISPLAY-START is passed by the hook `window-scroll-functions' and
is ignored.

See `lui-scroll-behavior' for how to customize this."
  (when (and (eq lui-scroll-behavior 'post-scroll)
             window
             (window-live-p window))
    (with-selected-window window
      (when (or (>= (point) lui-input-marker)
                (equal (point-max)
                       (window-end nil t)))
        (let ((resize-mini-windows nil))
          (save-excursion
            (goto-char (point-max))
            (recenter -1)))))))

(defun lui-scroll-post-command ()
  "Scroll the input line to the bottom of the window.

This is called from `post-command-hook'.

See `lui-scroll-behavior' for how to customize this."
  (condition-case err
      (dolist (w (window-list))
        (with-current-buffer (window-buffer w)
          (when (and lui-input-marker
                     (memq lui-scroll-behavior '(t post-command)))
            ;; Code from ERC's erc-goodies.el. I think this was originally
            ;; mine anyhow, not sure though.
            (save-restriction
              (widen)
              (when (>= (point) lui-input-marker)
                (save-excursion
                  (goto-char (point-max))
                  (with-selected-window w
                    (recenter -1))))))))
    (error
     (message "Error in lui-scroll-post-command: %S" err)
     )))

(defun lui-scroll-post-output ()
  "Scroll the input line to the bottom of the window.

This is called when lui output happens.

See `lui-scroll-behavior' for how to customize this."
  (when (memq lui-scroll-behavior '(t post-output))
    (let ((resize-mini-windows nil))
      (dolist (window (get-buffer-window-list (current-buffer) nil t))
        (when (or (>= (point) lui-input-marker)
                  (equal (point-max)
                         (window-end window)))
          (with-selected-window window
            (save-excursion
              (goto-char (point-max))
              (recenter -1))))))))


;;;;;;;;;;;;;
;;; Input ;;;
;;;;;;;;;;;;;

(defun lui-send-input ()
  "Send the current input to the Lui application.
If point is not in the input area, insert a newline."
  (interactive)
  (if (< (point) lui-input-marker)
      (newline)
    (save-restriction
      (narrow-to-region lui-input-marker (point-max))
      (run-hooks 'lui-pre-input-hook))
    (let ((input (buffer-substring lui-input-marker (point-max))))
      (delete-region lui-input-marker (point-max))
      (lui-add-input input)
      (if lui-input-function
          (funcall lui-input-function input)
        (error "No input function specified")))))

(defun lui-add-input (input)
  "Add INPUT as if entered by the user."
  (ring-insert lui-input-ring input)
  (setq lui-input-ring-index nil))


;;;;;;;;;;;;;;;
;;; Buttons ;;;
;;;;;;;;;;;;;;;

(define-button-type 'lui-button
  'supertype 'button
  'follow-link t
  'face 'lui-button-face)

(defun lui-buttonize ()
  "Buttonize the current message."
  (lui-buttonize-urls)
  (lui-buttonize-custom)
  (lui-buttonize-issues))

(defun lui-buttonize-custom ()
  "Add custom buttons to the current message.

This uses `lui-buttons-list'."
  (dolist (entry lui-buttons-list)
    (let ((regex (nth 0 entry))
          (submatch (nth 1 entry))
          (function-or-url (nth 2 entry))
          (arg-matches (nthcdr 3 entry)))
      (goto-char (point-min))
      (while (re-search-forward regex nil t)
        ;; Ensure we're not inserting a button inside a URL button
        (when (not (button-at (match-beginning 0)))
          (let* ((function (if (functionp function-or-url)
                               function-or-url
                             'browse-url))
                 (matches (mapcar (lambda (n)
                                    (match-string-no-properties n))
                                  arg-matches))
                 (arguments (if (functionp function-or-url)
                                matches
                              (list (apply #'format function-or-url
                                           matches)))))
            (make-button (match-beginning submatch)
                         (match-end submatch)
                         'type 'lui-button
                         'action 'lui-button-activate
                         'lui-button-function function
                         'lui-button-arguments arguments)))))))

(defun lui-buttonize-issues ()
  "Buttonize issue references in the current message, if configured."
  (when lui-button-issue-tracker
    (goto-char (point-min))
    (while (re-search-forward "\\(?:^\\|\\W\\)\\(#\\([0-9]+\\)\\)" nil t)
      ;; Ensure we're not inserting a button inside a URL button
      (when (not (button-at (point)))
        (make-button (match-beginning 1)
                     (match-end 1)
                     'type 'lui-button
                     'action 'lui-button-activate
                     'lui-button-function 'browse-url
                     'lui-button-arguments
                     (list (format lui-button-issue-tracker
                                   (match-string 2))))))))

(defun lui-buttonize-urls ()
  "Buttonize URLs in the current message."
  (let ((regex (regexp-opt thing-at-point-uri-schemes)))
    (goto-char (point-min))
    (while (re-search-forward regex nil t)
      (let ((bounds (bounds-of-thing-at-point 'url)))
        (when bounds
          (make-button (car bounds)
                       (cdr bounds)
                       'type 'lui-button
                       'action 'lui-button-activate
                       'lui-button-function 'browse-url
                       'lui-button-arguments
                       (list (buffer-substring-no-properties
                              (car bounds)
                              (cdr bounds)))))))))

(defun lui-button-activate (button)
  "Activate BUTTON.
This calls the function stored in the `lui-button-function'
property with the argument stored in `lui-button-arguments'."
  (apply (button-get button 'lui-button-function)
         (button-get button 'lui-button-arguments)))

(defun lui-next-button-or-complete ()
  "Go to the next button, or complete at point.
When point is in the input line, call `lui-completion-function'.
Otherwise, we move to the next button."
  (interactive)
  (if (>= (point)
          lui-input-marker)
      (funcall lui-completion-function)
    (forward-button 1)))

(defun lui-previous-button ()
  "Go to the previous button."
  (interactive)
  (backward-button 1))

(defun lui-button-elisp-symbol (name)
  "Show the documentation for the symbol named NAME."
  (let ((sym (intern-soft name)))
    (cond
     ((not sym)
      (message "No such symbol %s" name)
      (ding))
     (t
      (help-xref-interned sym)))))

(defun lui-button-pep (number)
  "Browse the PEP NUMBER."
  (browse-url (format "https://www.python.org/dev/peps/pep-%04i"
                      (string-to-number number))))

(defun lui-button-issue (issue)
  "Browse the issue tracker number ISSUE, if configured."
  (if lui-button-issue-tracker
      (browse-url (format lui-button-issue-tracker issue))
    (error "No issue tracker configured, see `lui-button-issue-tracker'")))


;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Input Line Killing ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lui-kill-to-beginning-of-line ()
  "Kill the input from point to the beginning of the input."
  (interactive)
  (let* ((beg (point-at-bol))
         (end (point))
         (str (buffer-substring beg end)))
    (delete-region beg end)
    (kill-new str)))


;;;;;;;;;;;;;;;;;;;;;
;;; Input History ;;;
;;;;;;;;;;;;;;;;;;;;;

;; FIXME!
;; These need some better algorithm. They clobber input when it is not
;; in the ring!
(defun lui-previous-input ()
  "Cycle through the input history to the last input."
  (interactive)
  (when (> (ring-length lui-input-ring) 0)
    (if (and lui-input-ring-index
             (= (1- (ring-length lui-input-ring))
                lui-input-ring-index))
        ;; last item - insert a single empty line
        (progn
          (lui-replace-input "")
          (setq lui-input-ring-index nil))
      ;; If any input is left, store it in the input ring
      (when (and (null lui-input-ring-index)
                 (> (point-max) lui-input-marker))
        (ring-insert lui-input-ring
                     (buffer-substring lui-input-marker (point-max)))
        (setq lui-input-ring-index 0))
      ;; Increment the index
      (setq lui-input-ring-index
            (if lui-input-ring-index
                (ring-plus1 lui-input-ring-index (ring-length lui-input-ring))
              0))
      ;; And insert the last input
      (lui-replace-input (ring-ref lui-input-ring lui-input-ring-index))
      (goto-char (point-max)))))

(defun lui-next-input ()
  "Cycle through the input history to the next input."
  (interactive)
  (when (> (ring-length lui-input-ring) 0)
    (if (and lui-input-ring-index
             (= 0 lui-input-ring-index))
        ;; first item - insert a single empty line
        (progn
          (lui-replace-input "")
          (setq lui-input-ring-index nil))
      ;; If any input is left, store it in the input ring
      (when (and (null lui-input-ring-index)
                 (> (point-max) lui-input-marker))
        (ring-insert lui-input-ring
                     (buffer-substring lui-input-marker (point-max)))
        (setq lui-input-ring-index 0))
      ;; Decrement the index
      (setq lui-input-ring-index (ring-minus1 (or lui-input-ring-index 0)
                                              (ring-length lui-input-ring)))
      ;; And insert the next input
      (lui-replace-input (ring-ref lui-input-ring lui-input-ring-index))
      (goto-char (point-max)))))

(defun lui-replace-input (str)
  "Replace input with STR."
  (save-excursion
    (goto-char lui-input-marker)
    (delete-region lui-input-marker (point-max))
    (insert str)))


;;;;;;;;;;;;;
;;; Fools ;;;
;;;;;;;;;;;;;

(defun lui-fools ()
  "Propertize the current narrowing according to foolhardiness.
That is, if any part of it has the text property 'lui-fool set,
make the whole thing invisible."
  (when (text-property-any (point-min)
                           (point-max)
                           'lui-fool t)
    (add-text-properties (point-min)
                         (point-max)
                         '(invisible lui-fool))))

(defun lui-fools-hidden-p ()
  "Return whether fools are currently hidden."
  (if (or (eq t buffer-invisibility-spec)
          (memq 'lui-fool buffer-invisibility-spec))
      t
    nil))

(defun lui-fool-toggle-display ()
  "Display what fools have said."
  (interactive)
  (when (eq buffer-invisibility-spec t)
    (add-to-invisibility-spec 'lui-fool))
  (cond
   ((lui-fools-hidden-p)
    (message "Now showing the gibberish of fools")
    (remove-from-invisibility-spec 'lui-fool))
   (t
    (message "Now hiding fools again *phew*")
    (add-to-invisibility-spec 'lui-fool)))
  ;; For some reason, after this, the display does not always update
  ;; (issue #31). Force an update just in case.
  (force-mode-line-update t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Blink Paren and Show Paren Mode ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lui-paren-highlighting ()
  "Enable sane parenthesis highlighting in this buffer."
  (set (make-local-variable 'blink-paren-function)
       'lui-blink-paren-function)
  (when (boundp 'show-paren-data-function)
    (set (make-local-variable 'show-paren-data-function)
         'lui-show-paren-data-function)))

(defun lui-blink-paren-function ()
  "Do not blink opening parens outside of the lui input area.

When point is within the lui input area, inserting a closing
parenthesis should only blink parens within the input area, not
outside of it.

This is a suitable value for `blink-paren-function', which see."
  (if (> (point) lui-input-marker)
      (let ((blink-matching-paren-distance (- (point)
                                              lui-input-marker)))
        (blink-matching-open))
    (blink-matching-open)))

(defun lui-show-paren-data-function ()
  "Show parens only within the input area.

When `show-paren-mode' is enabled, and point is in the input
area, parenthesis highlighting should only happen within the
input area, not include the rest of the buffer.

This is a suitable value for `show-paren-data-function', which see."
  (when (fboundp 'show-paren--default)
    (let ((range (show-paren--default)))
      (if (or (< (point) lui-input-marker)
              (not (elt range 2))
              (>= (elt range 2) lui-input-marker))
          range
        nil))))


;;;;;;;;;;;;;;;;
;;; Flyspell ;;;
;;;;;;;;;;;;;;;;

(defun lui-flyspell-change-dictionary (&optional dictionary)
  "*Change flyspell to DICTIONARY.
If DICTIONARY is nil, set a default dictionary according to
`lui-flyspell-alist'.
If it is \"\", disable flyspell."
  (interactive (list (completing-read
                      "Use new dictionary (RET for none, SPC to complete): "
                      (and (fboundp 'ispell-valid-dictionary-list)
                           (mapcar 'list (ispell-valid-dictionary-list)))
                      nil t)))
  (let ((dictionary (or dictionary
                        (lui-find-dictionary (buffer-name)))))
    (when flyspell-mode
      (flyspell-mode 0))
    (when (and dictionary
               (not (equal dictionary "")))
      (ispell-change-dictionary dictionary))
    (flyspell-mode 1)))


(defun lui-find-dictionary (buffer-name)
  "Return a dictionary appropriate for BUFFER-NAME."
  (let ((lis lui-flyspell-alist)
        (result nil))
    (while lis
      (if (string-match (caar lis) buffer-name)
          (setq result (cadr (car lis))
                lis nil)
         (setq lis (cdr lis))))
    result))

(defun lui-flyspell-check-word-p ()
  "Return non-nil when flyspell should verify at this position.
This is the value of Lui for `flyspell-generic-check-word-p'."
  (>= (point)
      lui-input-marker))


;;;;;;;;;;;;;;
;;; Output ;;;
;;;;;;;;;;;;;;

(defvar lui-message-id 0
  "Unique id for each message.
Used to allow navigation between messages and editing and
deleting.")
(make-variable-buffer-local 'lui-message-id)

(defvar lui-internal-text-properties '(lui-formatted-time-stamp
                                       lui-time-stamp-last
                                       lui-raw-text
                                       lui-message-id
                                       lui-saved-text-properties)
  "Text properties used internally by lui.

These are always kept when replacing messages.")

(defun lui-insert (str &optional not-tracked-p)
  "Insert STR into the current Lui buffer.

If NOT-TRACKED-P is given, this insertion won't trigger tracking
of the buffer."
  (if not-tracked-p
      (lui-insert-with-text-properties str 'not-tracked-p t)
    (lui-insert-with-text-properties str)))

(defun lui-plist-keys (plist)
  "Get the keys from PLIST.

PLIST should be a flat list with keys and values alternating,
like used for setting and getting text properties."
  (let ((key t) result)
    (dolist (item plist (reverse result))
      (when key
        (push item result))
      (setq key (not key)))))

(defun lui-insert-with-text-properties (str &rest text-properties)
  "Insert STR into the current Lui buffer.

TEXT-PROPERTIES is a property list containing text properties to
add to the inserted message."
  (let ((not-tracked-p (plist-get text-properties 'not-tracked-p))
        (saved-text-properties (append (lui-plist-keys text-properties)
                                       lui-internal-text-properties)))
    (lui-save-undo-list
     (save-excursion
       (save-restriction
         (let ((inhibit-read-only t)
               (inhibit-point-motion-hooks t))
           (widen)
           (goto-char lui-output-marker)
           (let ((beg (point))
                 (end nil))
             (insert str "\n")
             (setq end (point))
             (set-marker lui-output-marker (point))
             (narrow-to-region beg end))
           (goto-char (point-min))
           (add-text-properties (point-min)
                                (point-max)
                                `(lui-raw-text ,str))
           (run-hooks 'lui-pre-output-hook)
           (lui-apply-formatting)
           (lui-highlight-keywords)
           (lui-buttonize)
           (lui-fill)
           (lui-time-stamp
            (plist-get text-properties 'lui-formatted-time-stamp))
           (goto-char (point-min))
           (add-text-properties
            (point-min) (point-max)
            (plist-put text-properties 'lui-message-id lui-message-id))
           (setq lui-message-id (1+ lui-message-id))
           (run-hooks 'lui-post-output-hook)
           (lui-fools)
           (goto-char (point-min))
           (let ((faces (lui-faces-in-region (point-min)
                                             (point-max)))
                 (foolish (text-property-any (point-min)
                                             (point-max)
                                             'lui-fool t))
                 (not-tracked-p
                  (or not-tracked-p
                      (text-property-any (point-min)
                                         (point-max)
                                         'lui-do-not-track t))))
             (widen)
             (lui-truncate)
             (lui-read-only)
             (when (and (not not-tracked-p)
                        (not foolish))
               (tracking-add-buffer (current-buffer)
                                    faces)))
           (lui-scroll-post-output)
           (add-text-properties
            (point-min) (point-max)
            `(lui-saved-text-properties ,saved-text-properties))))))))

(defun lui--adjust-p (pos old)
  (and (numberp pos) (>= (abs pos) old)))

(defun lui--new-pos (pos shift)
  (* (if (< pos 0) -1 1) (+ (abs pos) shift)))

(defun lui-adjust-undo-list (old-begin shift)
  ;; Translate buffer positions in buffer-undo-list by SHIFT.
  (unless (or (zerop shift) (atom buffer-undo-list))
    (let ((list buffer-undo-list) elt)
      (while list
        (setq elt (car list))
        (cond ((integerp elt)           ; POSITION
               (if (lui--adjust-p elt old-begin)
                   (setf (car list) (lui--new-pos elt shift))))
              ((or (atom elt)           ; nil, EXTENT
                   (markerp (car elt))) ; (MARKER . DISTANCE)
               nil)
              ((integerp (car elt))     ; (BEGIN . END)
               (if (lui--adjust-p (car elt) old-begin)
                   (setf (car elt) (lui--new-pos (car elt) shift)))
               (if (lui--adjust-p (cdr elt) old-begin)
                   (setf (cdr elt) (lui--new-pos (cdr elt) shift))))
              ((stringp (car elt))      ; (TEXT . POSITION)
               (if (lui--adjust-p (cdr elt) old-begin)
                   (setf (cdr elt) (lui--new-pos (cdr elt) shift))))
              ((null (car elt))         ; (nil PROPERTY VALUE BEG . END)
               (let ((cons (nthcdr 3 elt)))
                 (if (lui--adjust-p (car cons) old-begin)
                     (setf (car cons) (lui--new-pos (car cons) shift)))
                 (if (lui--adjust-p (cdr cons) old-begin)
                     (setf (cdr cons) (lui--new-pos (cdr cons) shift)))))
              ((and (featurep 'xemacs)
                    (extentp (car elt))) ; (EXTENT START END)
               (if (lui--adjust-p (nth 1 elt) old-begin)
                     (setf (nth 1 elt) (lui--new-pos (nth 1 elt) shift)))
                 (if (lui--adjust-p (nth 2 elt) old-begin)
                     (setf (nth 2 elt) (lui--new-pos (nth 2 elt) shift)))))
        (setq list (cdr list))))))

(defvar lui-prompt-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<end>") 'lui-prompt-end-of-line)
    (define-key map (kbd "C-e") 'lui-prompt-end-of-line)
    map)
  "Keymap for Lui prompts.
Since \\[end-of-line] can't move out of fields, this DTRT for an
unexpecting user.")

(defun lui-set-prompt (prompt)
  "Set PROMPT as the current Lui prompt."
  (let ((inhibit-read-only t))
    (lui-save-undo-list
     (save-excursion
       (goto-char lui-output-marker)
       (insert prompt)
       (if (> lui-input-marker (point))
           (delete-region (point) lui-input-marker)
         (set-marker lui-input-marker (point)))
       (add-text-properties lui-output-marker lui-input-marker
                            `(read-only t
                                        rear-nonsticky t
                                        field lui-prompt
                                        keymap ,lui-prompt-map
                                        front-sticky t
                                        ))))))

(defun lui-prompt-end-of-line (&optional _N)
  "Move past the prompt, and then to the end of the line.
This uses `end-of-line'.

The argument N is ignored."
  (interactive "p")
  (goto-char lui-input-marker)
  (call-interactively 'end-of-line))

(defun lui-faces-in-region (beg end)
  "Return a face that describes the region between BEG and END."
  (goto-char beg)
  (let ((faces nil))
    (while (not (= (point) end))
      (let ((face (get-text-property (point) 'face)))
        (dolist (face (if (consp face)
                          face
                        (list face)))
          (when (and face
                     (facep face)
                     (face-differs-from-default-p face))
            (push face faces)))
        (goto-char (next-single-property-change (point) 'face
                                                nil end))))
    faces))



;;;;;;;;;;;;;;;;;;;;
;;; Highlighting ;;;
;;;;;;;;;;;;;;;;;;;;

(defun lui-highlight-keywords ()
  "Highlight the entries in the variable `lui-highlight-keywords'.

This is called automatically when new text is inserted."
  (let ((regex (lambda (entry)
                 (if (stringp entry)
                     entry
                   (car entry))))
        (submatch (lambda (entry)
                    (if (and (consp entry)
                             (numberp (cadr entry)))
                        (cadr entry)
                      0)))
        (properties (lambda (entry)
                      (let ((face (cond
                                   ;; REGEXP
                                   ((stringp entry)
                                    'lui-highlight-face)
                                   ;; (REGEXP SUBMATCH)
                                   ((and (numberp (cadr entry))
                                         (null (cddr entry)))
                                    'lui-highlight-face)
                                   ;; (REGEXP FACE)
                                   ((null (cddr entry))
                                    (cadr entry))
                                   ;; (REGEXP SUBMATCH FACE)
                                   (t
                                    (nth 2 entry)))))
                        (if (facep face)
                            `(face ,face)
                          face)))))
    (dolist (entry lui-highlight-keywords)
      (goto-char (point-min))
      (while (re-search-forward (funcall regex entry) nil t)
        (let* ((exp (funcall submatch entry))
               (beg (match-beginning exp))
               (end (match-end exp)))
          (when (not (text-property-any beg end 'lui-highlight-fontified-p t))
            (add-text-properties beg end
                                 (append (funcall properties entry)
                                         '(lui-highlight-fontified-p t)))))))))

(defun lui-apply-formatting ()
  "Highlight the entries in `lui-formatting-list'."
  (dolist (entry lui-formatting-list)
    (goto-char (point-min))
    (let ((re (car entry))
          (subgroup (cadr entry))
          (face (nth 2 entry)))
      (while (re-search-forward re nil t)
        (when face
          (add-face-text-property (match-beginning subgroup) (match-end subgroup)
                                  face nil (current-buffer)))))))


;;;;;;;;;;;;;;;
;;; Filling ;;;
;;;;;;;;;;;;;;;

(defun lui-fill ()
  "Fill the text in the buffer.
This is called automatically when new text is inserted. See
`lui-fill-type' and `lui-fill-column' on how to customize this
function."
  (cond
   ((stringp lui-fill-type)
    (let ((fill-prefix lui-fill-type)
          (fill-column (or lui-fill-column
                           fill-column)))
      (fill-region (point-min) (point-max)
                   nil t)))
   ((eq lui-fill-type 'variable)
    (let ((fill-prefix (save-excursion
                         (goto-char (point-min))
                         (let ((beg (point)))
                           (re-search-forward "\\s-" nil t)
                           (make-string (- (point) beg) ? ))))
          (fill-column (or lui-fill-column
                           fill-column)))
      (fill-region (point-min) (point-max)
                   nil t)))
   ((numberp lui-fill-type)
    (let ((right-end (save-excursion
                       (goto-char (point-min))
                       (re-search-forward "\\s-" nil t)
                       (- (point)
                          (point-at-bol)))))
      (goto-char (point-min))
      (when (< right-end lui-fill-type)
        (insert (make-string (- lui-fill-type
                                right-end)
                             ? )))
      (let ((fill-prefix (make-string lui-fill-type ? ))
            (fill-column (or lui-fill-column
                             fill-column)))
        (fill-region (point-min) (point-max)
                     nil t)))))
  (when lui-fill-remove-face-from-newline
    (goto-char (point-min))
    (while (re-search-forward "\n" nil t)
      (put-text-property (match-beginning 0)
                         (match-end 0)
                         'face
                         nil))))


;;;;;;;;;;;;;;;;;;;
;;; Time Stamps ;;;
;;;;;;;;;;;;;;;;;;;

(defvar lui-time-stamp-last nil
  "The last time stamp.")
(make-variable-buffer-local 'lui-time-stamp-last)

(defvar lui-time-stamp-time nil
  "A custom time to use as the time stamp for `lui-insert'.

This variable should be let-bound when you wish to provide a
custom time to be printed by `lui-time-stamp'.  If this variable
is nil the current time is used.  See the TIME argument to
`format-time-string' for more information.")

(defvar lui-time-stamp-zone nil
  "A custom timezone to use for the time stamp for `lui-insert'.

This variable should be let-bound when you wish to provide a
custom time zone when printing the time stamp with
`lui-time-stamp'.  If this variable is nil local time is used.
See the ZONE argument to `format-time-string' for more
information.")

(defun lui-time-stamp (&optional text)
  "Add a time stamp to the current buffer.

If TEXT is specified, use that instead of formatting a new time stamp."
  (let ((ts (or text
                (format-time-string lui-time-stamp-format
                                    lui-time-stamp-time
                                    lui-time-stamp-zone))))
    (cond
     ;; Time stamps right
     ((or (numberp lui-time-stamp-position)
          (eq lui-time-stamp-position 'right))
      (when (or (not lui-time-stamp-only-when-changed-p)
                (not lui-time-stamp-last)
                (not (string= ts lui-time-stamp-last)))
        (goto-char (point-min))
        (goto-char (point-at-eol))
        (let* ((curcol (current-column))
               (col (if (numberp lui-time-stamp-position)
                        lui-time-stamp-position
                      (+ 2 (or lui-fill-column
                               fill-column
                               (point)))))
               (indent (if (> col curcol)
                           (- col curcol)
                         1))
               (ts-string (propertize
                           (concat (make-string indent ?\s)
                                   (propertize
                                    ts
                                    'face 'lui-time-stamp-face))
                           'lui-time-stamp t))
               (start (point)))
          (insert ts-string)
          (add-text-properties start (1+ (point)) '(intangible t))
          (add-text-properties (1+ start) (point) '(cursor-intangible t)))))
     ;; Time stamps left
     ((eq lui-time-stamp-position 'left)
      (let ((indent-string (propertize (make-string (length ts) ?\s)
                                       'lui-time-stamp t)))
        (goto-char (point-min))
        (cond
         ;; Time stamp
         ((or (not lui-time-stamp-only-when-changed-p)
              (not lui-time-stamp-last)
              (not (string= ts lui-time-stamp-last)))
          (insert (propertize ts
                              'face 'lui-time-stamp-face
                              'lui-time-stamp t)))
         ;; Just indentation
         (t
          (insert indent-string)))
        (forward-line 1)
        (while (< (point) (point-max))
          (insert indent-string)
          (forward-line 1))))
     ;; Time stamps in margin
     ((or (eq lui-time-stamp-position 'right-margin)
          (eq lui-time-stamp-position 'left-margin))
      (when (or (not lui-time-stamp-only-when-changed-p)
                (not lui-time-stamp-last)
                (not (string= ts lui-time-stamp-last)))
        (goto-char (point-min))
        (when lui-fill-type
          (goto-char (point-at-eol)))
        (let* ((ts (propertize ts 'face 'lui-time-stamp-face))
               (ts-margin (propertize
                           " "
                           'display `((margin ,lui-time-stamp-position)
                                      ,ts)
                           'lui-time-stamp t)))
          (insert ts-margin)))))
    (add-text-properties (point-min) (point-max)
                         `(lui-formatted-time-stamp ,ts
                           lui-time-stamp-last ,lui-time-stamp-last))
    (setq lui-time-stamp-last ts)))

(defun lui-time-stamp-enable-filtering ()
  "Enable filtering of timestamps from copied text."
  (set (make-local-variable 'filter-buffer-substring-functions)
       '(lui-filter-buffer-time-stamps)))

(defun lui-filter-buffer-time-stamps (fun beg end delete)
  "Filter text from copied strings.

This is meant for the variable `filter-buffer-substring-functions',
which see for an explanation of the argument FUN, BEG, END and
DELETE."
  (let ((string (funcall fun beg end delete))
        (inhibit-point-motion-hooks t)
        (inhibit-read-only t)
        ;; Emacs 24.4, 24.5
        deactivate-mark)
    (with-temp-buffer
      (insert string)
      (let ((start (text-property-any (point-min)
                                      (point-max)
                                      'lui-time-stamp t)))
        (while start
          (let ((end (next-single-property-change start 'lui-time-stamp
                                                  nil (point-max))))
            (delete-region start end)
            (setq start (text-property-any (point-min) (point-max)
                                           'lui-time-stamp t))))
        (buffer-string)))))

(defun lui-time-stamp-buffer-substring (buffer-string)
  "Filter text from copied strings.

This is meant for the variable `buffer-substring-filters',
which see for an explanation of the argument BUFFER-STRING."
  (lui-filter-buffer-time-stamps (lambda (_beg _end _delete)
                                  buffer-string)
                                nil nil nil))


;;;;;;;;;;;;;;;;;;
;;; Truncating ;;;
;;;;;;;;;;;;;;;;;;

(defun lui-truncate ()
  "Truncate the current buffer if it exceeds `lui-max-buffer-size'."
  (when (and lui-max-buffer-size
             (> (point-max)
                lui-max-buffer-size))
    (goto-char (- (point-max)
                  lui-max-buffer-size))
    (forward-line 0)
    (let ((inhibit-read-only t))
      (delete-region (point-min) (point)))))


;;;;;;;;;;;;;;;;;
;;; Read-Only ;;;
;;;;;;;;;;;;;;;;;

(defun lui-read-only ()
  "Make the current output read-only if `lui-read-only-output-p' is non-nil."
  (when lui-read-only-output-p
    (add-text-properties (point-min) lui-output-marker
                         '(read-only t
                           front-sticky t))))


;;;;;;;;;;;;;;;;;;
;;; Navigation ;;;
;;;;;;;;;;;;;;;;;;

(defun lui-at-message-p ()
  "Check if point is on a message."
  (get-text-property (point) 'lui-message-id))

(defun lui-beginning-of-message-p ()
  "Check if point is at the beginning of a message."
  (or (= (point) (point-min))
      (not (equal (get-text-property (point) 'lui-message-id)
                  (get-text-property (1- (point)) 'lui-message-id)))))

(defun lui-beginning-of-message ()
  "Move point to the beginning of the message at point."
  (goto-char (previous-single-property-change (point) 'lui-message-id)))

(defun lui-forward-message ()
  "Move point to the next message in the buffer and return point.
If there is no next message, move to the end of the buffer instead."
  (let ((current-id (get-text-property (point) 'lui-message-id))
        (next-point
         (next-single-property-change (point) 'lui-message-id)))
    (if (not next-point)
        (goto-char (point-max))
      (let ((message-id
             (get-text-property next-point 'lui-message-id)))
        (goto-char next-point)
        (when (or (not (or current-id message-id))
                  (and current-id (not message-id))
                  (and current-id message-id
                       (= current-id message-id)))
          (lui-forward-message))))
    (point)))

(defun lui-backward-message ()
  "Move point to the previous message in the buffer and return point.
If there is no previous message, move to the beginning of the
buffer instead."
  (let ((current-id (get-text-property (point) 'lui-message-id))
        (prev-point
         (previous-single-property-change (point) 'lui-message-id)))
    (if (not prev-point)
        (goto-char (point-min))
      (let ((message-id
             (get-text-property prev-point 'lui-message-id)))
        (goto-char prev-point)
        (when (or (not (or current-id message-id))
                  (and current-id (not message-id))
                  (and current-id message-id
                       (= current-id message-id)))
          (lui-backward-message))))
    (point)))


;;;;;;;;;;;;;;;
;;; Editing ;;;
;;;;;;;;;;;;;;;

(defun lui-recover-output-marker ()
  "Reset the output marker to just before the lui prompt."
  (let ((input-position (marker-position lui-input-marker)))
    (set-marker lui-output-marker
                (field-beginning (1- input-position)))))

(defun lui-build-plist (keys)
  "Build a plist with KEYS taken from current text properties."
  (let (result)
    (dolist (key keys result)
      (let ((value (get-text-property (point) key)))
        (when value
          (setq result (plist-put result key value)))))))

(defun lui-replace-message (new-message)
  "Replace the message at point with NEW-MESSAGE."
  (unless (lui-at-message-p)
    (error "Point is not on a message"))
  (unless (lui-beginning-of-message-p)
    (lui-beginning-of-message))
  (let* ((saved-text-properties
          (get-text-property (point) 'lui-saved-text-properties))
         (text-properties (lui-build-plist saved-text-properties))
         (inhibit-read-only t)
         (lui-time-stamp-last
          (get-text-property (point) 'lui-time-stamp-last))
         (lui-message-id
          (get-text-property (point) 'lui-message-id)))
    (unwind-protect
        (progn
          (setq lui-output-marker (point-marker))
          (delete-region (point)
                         (next-single-property-change (point) 'lui-message-id))
          (apply #'lui-insert-with-text-properties new-message
                 (plist-put text-properties 'not-tracked-p t)))
      (lui-recover-output-marker))))

(defun lui-replace (new-message predicate)
  "Replace a message with NEW-MESSAGE.

PREDICATE should be a function that returns a non-nil value for
the message that should be replaced."
  (save-excursion
    (goto-char (point-max))
    (while (> (lui-backward-message) (point-min))
      (when (funcall predicate)
        (lui-replace-message new-message)))))

(defun lui-delete-message ()
  "Delete the message at point."
  (unless (lui-at-message-p)
    (error "Point is not on a message"))
  (unless (lui-beginning-of-message-p)
    (lui-beginning-of-message))
  (let ((inhibit-read-only t))
    (add-text-properties (point)
                         (next-single-property-change (point) 'lui-message-id)
                         '(face lui-deleted-face))))

(defun lui-delete (predicate)
  "Delete a message.

PREDICATE should be a function that returns a non-nil value for
the message that should be replaced."
  (save-excursion
    (goto-char (point-max))
    (while (> (lui-backward-message) (point-min))
      (when (funcall predicate)
        (lui-delete-message)))))


(provide 'lui)
;;; lui.el ends here
