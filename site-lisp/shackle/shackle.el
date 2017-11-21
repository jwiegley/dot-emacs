;;; shackle.el --- Enforce rules for popups

;; Copyright (C) 2014-2016 Vasilij Schneidermann <v.schneidermann@gmail.com>

;; Author: Vasilij Schneidermann <v.schneidermann@gmail.com>
;; URL: https://github.com/wasamasa/shackle
;; Version: 1.0.0
;; Keywords: convenience
;; Package-Requires: ((cl-lib "0.5"))

;; This file is NOT part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING. If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This global minor mode allows you to easily set up rules for
;; popups in Emacs.

;; See the README for more info:
;; https://github.com/wasamasa/shackle

;;; Code:

(require 'cl-lib)

(defgroup shackle nil
  "Enforce rules for popups"
  :group 'convenience
  :prefix "shackle-")

(defcustom shackle-select-reused-windows nil
  "Make Emacs select reused windows by default?
When t, select every window that is already displaying the buffer
after attempting to display its buffer again by default,
otherwise only do that if the :select keyword is present."
  :type 'boolean
  :group 'shackle)

(defcustom shackle-inhibit-window-quit-on-same-windows nil
  "Make Emacs inhibit quitting same windows by default?
When t, a buffer that has been displayed by switching to it in
the same window is exempt from `quit-window' closing its window,
otherwise only do that if the :inhibit-window-quit keyword is
present."
  :type 'boolean
  :group 'shackle)

(defcustom shackle-default-alignment 'below
  "Default alignment of aligned windows.
It may be one of the following values:

'above: Align above the currently selected window.

'below: Align below the currently selected window.

'left: Align on the left side of the currently selected window.

'right: Align on the right side of the currently selected
window.

<function>: Call the specified function with no arguments to
determine side, must return one of the above four values."
  :type '(choice (const :tag "Above" above)
                 (const :tag "Below" below)
                 (const :tag "Left" left)
                 (const :tag "Right" right))
  :group 'shackle)

(define-obsolete-variable-alias 'shackle-default-ratio 'shackle-default-size
  "0.9.0")
(defcustom shackle-default-size 0.5
  "Default size of aligned windows.
A floating point number between 0 and 1 is interpreted as a
ratio.  An integer equal or greater than 1 is interpreted as a
number of lines."
  :type 'number
  :group 'shackle)

(defcustom shackle-rules nil
  "Association list of rules what to do with windows.
Each rule consists of a condition and a property list.  The
condition can be a symbol, a string or a list of either type.  If
it's a symbol, match the buffer's major mode.  If it's a string,
match the name of the buffer.  A list of symbols or strings
requires a match of any element as described earlier for its
type.  Use the following option in the property list to use
regular expression matching on a buffer name:

:regexp and t

As a special case, a list of the (:custom function) form
will call the supplied predicate with the buffer to be displayed
as value and be interpreted as a match for a non-nil return value.

A default rule can be set up with `shackle-default-rule'.
To make an exception to `shackle-default-rule', use the condition
you want to exclude and either not use the key in question, use a
different value or use a placeholder as key.

The property list accepts the following keys and values:

:select and t

Make sure the window that popped up is selected afterwards.
Customize `shackle-select-reused-windows' to make this the
default for windows already displaying the buffer.

:custom and a function name or lambda

Override with a custom action.  Takes a function as argument
which is called with BUFFER-OR-NAME, ALIST and PLIST as argument.
This mode of operation allows you to pick one of the existing
actions, but by your own conditions.

:inhibit-window-quit and t

Modify the behaviour of `quit-window' to not delete the window.
This option is recommended in combination with :same, but can be
used with other keys like :other as well.  Customize
`shackle-inhibit-window-quit-on-same-windows' to make this the
default for every buffer that was displayed by switching to it in
the same window.

:ignore and t

Ignore the request of displaying a buffer completely.  Note that
this does *not* inhibit preceding actions such as creation or
update of the buffer in question.

:other and t

Reuse the other window if there's more than one window open,
otherwise pop up a new window.  Can be used with :frame to do the
equivalent with the other frame and a new frame.

:popup and t

Pop up a new window instead of reusing the current one.

:same and t

Don't pop up any window and reuse the currently active one.

:align and t or either of 'above, 'below, 'left and 'right

Align the popped up window at any of the specified sides or the
default size (see `shackle-default-alignment') by splitting the
root window.

Additionally to that, one can use a function called with zero
arguments that must return any of the above alignments.

:size and a number greater than zero

Use this option to specify a different size than the default
value of 0.5 (see `shackle-default-size').

:frame and t

Pop to a frame instead of window."
  :type '(alist :key-type (choice :tag "Condition"
                                  (symbol :tag "Major mode")
                                  (string :tag "Buffer name")
                                  (repeat (choice
                                           (symbol :tag "Major mode")
                                           (string :tag "Buffer name")))
                                  (list :tag "Custom function"
                                        (const :tag "Custom" :custom) function))
                :value-type (plist :options
                                   (((const :tag "Regexp" :regexp) boolean)
                                    ((const :tag "Select" :select) boolean)
                                    ((const :tag "Custom" :custom) function)
                                    ((const :tag "Inhibit window quit" :inhibit-window-quit) boolean)
                                    ((const :tag "Ignore" :ignore) boolean)
                                    ((const :tag "Other" :other) boolean)
                                    ((const :tag "Same" :same) boolean)
                                    ((const :tag "Popup" :popup) boolean)
                                    ((const :tag "Align" :align)
                                     (choice :tag "Alignment" :value t
                                             (const :tag "Default" t)
                                             (const :tag "Above" 'above)
                                             (const :tag "Below" 'below)
                                             (const :tag "Left" 'left)
                                             (const :tag "Right" 'right)
                                             (function :tag "Function")))
                                    ((const :tag "Size" :size) number)
                                    ((const :tag "Frame" :frame) boolean))))
  :group 'shackle)

(defcustom shackle-default-rule nil
  "Default rule to use when no other matching rule found.
It's a plist with the same keys and values as described in
`shackle-rules'."
  :type '(plist :options (((const :tag "Regexp" :regexp) boolean)
                          ((const :tag "Select" :select) boolean)
                          ((const :tag "Custom" :custom) function)
                          ((const :tag "Inhibit window quit" :inhibit-window-quit) boolean)
                          ((const :tag "Ignore" :ignore) boolean)
                          ((const :tag "Other" :other) boolean)
                          ((const :tag "Same" :same) boolean)
                          ((const :tag "Popup" :popup) boolean)
                          ((const :tag "Align" :align)
                           (choice :value t
                                   (const :tag "Default" t)
                                   (const :tag "Above" 'above)
                                   (const :tag "Below" 'below)
                                   (const :tag "Left" 'left)
                                   (const :tag "Right" 'right)
                                   (function :tag "Function")))
                          ((const :tag "Size" :size) number)
                          ((const :tag "Frame" :frame) boolean)))
  :group 'shackle)

(defun shackle--match (buffer-or-name condition plist)
  "Internal match function.
Used by `shackle-match', when BUFFER-OR-NAME matches CONDITION,
PLIST is returned."
  (let* ((buffer (get-buffer buffer-or-name))
         (buffer-major-mode (buffer-local-value 'major-mode buffer))
         (buffer-name (buffer-name buffer)))
    (when (or (and (symbolp condition)
                   (eq condition buffer-major-mode))
              (and (stringp condition)
                   (or (string= condition buffer-name)
                       (and (plist-get plist :regexp)
                            (string-match condition buffer-name))))
              (and (consp condition)
                   (or (and (eq (car condition) :custom)
                            (funcall (cadr condition) buffer))
                       (cl-some (lambda (c) (shackle--match buffer-or-name
                                                            c plist))
                                condition))))
      plist)))

(defun shackle-match (buffer-or-name)
  "Check whether BUFFER-OR-NAME is any rule match.
Uses `shackle--match' to decide with `shackle-rules' whether
there is a match, if yes it returns a property list which
`shackle-display-buffer-condition' and
`shackle-display-buffer-action' use."
  (cl-loop for (condition . plist) in shackle-rules
           when (shackle--match buffer-or-name condition plist)
           return plist
           finally return shackle-default-rule))

(defun shackle-display-buffer-condition (buffer action)
  "Return key-value pairs when BUFFER match any shackle condition.
Uses `shackle-match'and `shackle-rules', BUFFER and ACTION take
the form `display-buffer-alist' specifies."
  (shackle-match buffer))

(defun shackle-display-buffer-action (buffer alist)
  "Execute an action for BUFFER according to `shackle-rules'.
This uses `shackle-display-buffer' internally, BUFFER and ALIST
take the form `display-buffer-alist' specifies."
  (shackle-display-buffer buffer alist (shackle-match buffer)))

(defun shackle--frame-splittable-p (frame)
  "Return FRAME if it is splittable."
  (when (and (window--frame-usable-p frame)
             (not (frame-parameter frame 'unsplittable)))
    frame))

(defun shackle--splittable-frame ()
  "Return a splittable frame to work on.
This can be either the selected frame or the last frame that's
not displaying a lone minibuffer."
  (let ((selected-frame (selected-frame))
        (last-non-minibuffer-frame (last-nonminibuffer-frame)))
    (or (shackle--frame-splittable-p selected-frame)
        (shackle--frame-splittable-p last-non-minibuffer-frame))))

(defun shackle--split-some-window (frame alist)
  "Return a window if splitting any window was successful.
This function tries using the largest window on FRAME for
splitting, if all windows are the same size, the selected one is
taken, in case this fails, the least recently used window is used
for splitting.  ALIST is passed to `window--try-to-split-window'
internally."
  (or (window--try-to-split-window (get-largest-window frame t) alist)
      (window--try-to-split-window (get-lru-window frame t) alist)))

(defun shackle--inhibit-window-quit (window)
  "Keep `quit-window' in WINDOW from deleting the window."
  (set-window-parameter window 'quit-restore nil))

(defun shackle--display-buffer-reuse (buffer alist)
  "Attempt reusing a window BUFFER is already displayed in.
ALIST is passed to `display-buffer-reuse-window' internally.  If
`shackle-select-reused-windows' is t, select the window
afterwards."
  (let ((window (display-buffer-reuse-window buffer alist)))
    (prog1 window
      (when (and window (window-live-p window)
                 shackle-select-reused-windows)
        (select-window window t)))))

(defun shackle--display-buffer-same (buffer alist)
  "Display BUFFER in the currently selected window.
ALIST is passed to `window--display-buffer' internally."
  (let ((window (window--display-buffer buffer (selected-window)
                                        'window alist)))
    (prog1 window
      (when shackle-inhibit-window-quit-on-same-windows
        (shackle--inhibit-window-quit window)))))

(defun shackle--display-buffer-frame (buffer alist plist)
  "Display BUFFER in a popped up frame.
ALIST is passed to `window--display-buffer' internally.  If PLIST
contains the :other key with t as value, reuse the next available
frame if possible, otherwise pop up a new frame."
  (let* ((params (cdr (assq 'pop-up-frame-parameters alist)))
         (pop-up-frame-alist (append params pop-up-frame-alist))
         (fun pop-up-frame-function))
    (when fun
      (let* ((frame (if (and (plist-get plist :other)
                             (> (length (frames-on-display-list)) 1))
                        (next-frame nil 'visible)
                      (funcall fun)))
             (window (frame-selected-window frame)))
        (prog1 (window--display-buffer
                buffer window 'frame alist
                display-buffer-mark-dedicated)
          (unless (cdr (assq 'inhibit-switch-frame alist))
            (window--maybe-raise-frame frame)))))))

(defvar shackle-last-buffer nil
  "Last buffer displayed with shackle.")

(defvar shackle-last-window nil
  "Last window displayed with shackle.")

(defun shackle--display-buffer-popup-window (buffer alist plist)
  "Display BUFFER in a popped up window.
ALIST is passed to `window--display-buffer' internally.  If PLIST
contains the :other key with t as value, reuse the next available
window if possible."
  (let ((frame (shackle--splittable-frame)))
    (when frame
      (let ((window (if (and (plist-get plist :other) (not (one-window-p)))
                        (next-window nil 'nominibuf)
                      (shackle--split-some-window frame alist))))
        (prog1 (window--display-buffer
                buffer window 'window alist
                display-buffer-mark-dedicated)
          (when window
            (setq shackle-last-window window
                  shackle-last-buffer buffer))
          (unless (cdr (assq 'inhibit-switch-frame alist))
            (window--maybe-raise-frame (window-frame window))))))))

(defun shackle--display-buffer-aligned-window (buffer alist plist)
  "Display BUFFER in an aligned window.
ALIST is passed to `window--display-buffer' internally.
Optionally use a different alignment and/or size if PLIST
contains the :alignment key with an alignment different than the
default one in `shackle-default-alignment' and/or PLIST contains
the :size key with a number value."
  (let ((frame (shackle--splittable-frame)))
    (when frame
      (let* ((alignment-argument (plist-get plist :align))
             (alignments '(above below left right))
             (alignment (cond
                         ((functionp alignment-argument)
                          (funcall alignment-argument))
                         ((memq alignment-argument alignments)
                          alignment-argument)
                         ((functionp shackle-default-alignment)
                          (funcall shackle-default-alignment))
                         (t shackle-default-alignment)))
             (horizontal (when (memq alignment '(left right)) t))
             (old-size (window-size (frame-root-window) horizontal))
             (size (or (plist-get plist :ratio) ; yey, backwards compatibility
                       (plist-get plist :size)
                       shackle-default-size))
             (new-size (round (if (>= size 1)
                                  (- old-size size)
                                (* (- 1 size) old-size)))))
        (if (or (< new-size (if horizontal window-min-width window-min-height))
                (> new-size (- old-size (if horizontal window-min-width
                                          window-min-height))))
            (error "Invalid alignment size %s, aborting" new-size)
          (let ((window (split-window (frame-root-window frame)
                                      new-size alignment)))
            (prog1 (window--display-buffer buffer window 'window alist
                                           display-buffer-mark-dedicated)
              (when window
                (setq shackle-last-window window
                      shackle-last-buffer buffer))
              (unless (cdr (assq 'inhibit-switch-frame alist))
                (window--maybe-raise-frame frame)))))))))

(defun shackle--display-buffer (buffer alist plist)
  "Internal function for `shackle-display-buffer'.
Displays BUFFER according to ALIST and PLIST."
  (cond
   ((plist-get plist :custom)
    (funcall (plist-get plist :custom) buffer alist plist))
   ((plist-get plist :ignore) 'fail)
   ((shackle--display-buffer-reuse buffer alist))
   ((or (plist-get plist :same)
        ;; there is `display-buffer--same-window-action' which things
        ;; like `info' use to reuse the currently selected window, it
        ;; happens to be of the (inhibit-same-window . nil) form and
        ;; should be permitted unless a popup is requested
        (and (not (plist-get plist :popup))
             (and (assq 'inhibit-same-window alist)
                  (not (cdr (assq 'inhibit-same-window alist))))))
    (shackle--display-buffer-same buffer alist))
   ((plist-get plist :frame)
    (shackle--display-buffer-frame buffer alist plist))
   ((plist-get plist :align)
    (shackle--display-buffer-aligned-window buffer alist plist))
   (t
    (shackle--display-buffer-popup-window buffer alist plist))))

(defun shackle-display-buffer (buffer alist plist)
  "Display BUFFER according to ALIST and PLIST.
See `display-buffer-pop-up-window' and
`display-buffer-pop-up-frame' for the basic functionality the
majority of code was lifted from.  Additionally to BUFFER and
ALIST this function takes an optional PLIST argument which allows
it to do useful things such as selecting the popped up window
afterwards and/or inhibiting `quit-window' from deleting the
window."
  (save-excursion
  (let* ((ignore-window-parameters t)
         (window (shackle--display-buffer buffer alist plist)))
    (when (plist-get plist :inhibit-window-quit)
      (shackle--inhibit-window-quit window))
    (when (and (plist-get plist :select) (window-live-p window))
      (select-window window t))
    window)))

;;;###autoload
(define-minor-mode shackle-mode
  "Toggle `shackle-mode'.
This global minor mode allows you to easily set up rules for
popups in Emacs."
  :global t
  (if shackle-mode
      (setq display-buffer-alist
            (cons '(shackle-display-buffer-condition
                    shackle-display-buffer-action)
                  display-buffer-alist))
    (setq display-buffer-alist
          (remove '(shackle-display-buffer-condition
                    shackle-display-buffer-action)
                  display-buffer-alist))))


;; debugging support

(require 'trace)

(defcustom shackle-trace-buffer "*shackle trace*"
  "Name of the buffer for tracing `shackle-traced-functions'."
  :type 'string
  :group 'shackle)

(defcustom shackle-traced-functions
  '(display-buffer
    pop-to-buffer
    pop-to-buffer-same-window
    switch-to-buffer-other-window
    switch-to-buffer-other-frame)
  "List of `display-buffer'-style functions to trace."
  :type '(list function))

(defun shackle-trace-functions ()
  "Enable tracing `shackle-traced-functions'."
  (interactive)
  (dolist (function shackle-traced-functions)
    (trace-function-background function shackle-trace-buffer)))

(defun shackle-untrace-functions ()
  "Enable tracing `shackle-traced-functions'."
  (interactive)
  (dolist (function shackle-traced-functions)
    (untrace-function function shackle-trace-buffer)))

(provide 'shackle)
;;; shackle.el ends here
