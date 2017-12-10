;;; clipmon.el --- Clipboard monitor - watch system clipboard, add changes to kill ring/autoinsert
;;
;; Copyright (c) 2015-2016 Brian Burns
;;
;; Author: Brian Burns <bburns.km@gmail.com>
;; URL: https://github.com/bburns/clipmon
;; Keywords: convenience
;; Version: 20160925
;;
;; This package is NOT part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;
;;; Commentary:
;;
;;;; Description
;; ----------------------------------------------------------------------------
;;
;; Clipmon is a clipboard monitor - it watches the system clipboard and can
;; automatically insert any new text into the current location in Emacs.
;;
;; It also adds changes to the system clipboard to the kill ring, making Emacs
;; into a clipboard manager for text - you can then use a package like
;; browse-kill-ring or helm-ring to view and manage your clipboard history.
;;
;; **Warning (2015-12-24): in an X-windows system with clipmon-mode on, bringing
;;   up a graphical menu (e.g. Shift+Mouse-1) will cause Emacs to hang. See
;;   http://debbugs.gnu.org/cgi/bugreport.cgi?bug=22214.
;;   X-windows starts a timer when checking the contents of the clipboard, which
;;   interferes with the clipmon timer.**
;;
;; Update (2016-01-27): in an X-windows system, Clipmon now uses the clipboard
;; instead of the primary selection - see https://github.com/bburns/clipmon/issues/4.
;;
;; You can use Clipmon for taking notes from a webpage, for example - just copy the
;; text you want to save and it will be added to Emacs. It helps to have an
;; autocopy feature or addon for the browser, e.g. AutoCopy 2 for Firefox - then
;; you can just select text to add it to Emacs.
;;
;; Here's a diagram - text flows from the top to the bottom:
;;
;;                  +---------------------+
;;                  |   Other programs    |+
;;                  +---------------------+|
;;                   +---------------------+
;;                           /
;;                     +-----------+
;;                     |  System   |
;;                     | clipboard |
;;                     +-----------+
;;     OS                /
;;     ---------------------------------------------------
;;     Emacs           /
;;                    /
;;           +--------------+      +---------------+
;;           | clipmon-mode |......|  autoinsert   |
;;           +--------------+      +---------------+
;;                   |                     .
;;             +-----------+               .
;;             | Emacs     ++              .
;;             | kill ring ++       +--------------+
;;             +-----------+|+      |  transforms  |
;;              +-----------+|      +--------------+
;;               +-----------+             .
;;                      |                  .
;;                      | yank             . autoinsert
;;                 +--------------------------+
;;                 |      Emacs buffer        |
;;                 +--------------------------+
;;
;;
;; The solid line is turned on and off with `clipmon-mode', while the dotted
;; line is turned on and off with `clipmon-autoinsert-toggle', usually bound to a key.
;; There are also various transformations you can perform on the text, e.g.
;; adding newlines to the end.
;;
;; (Emacs's kill-ring is like the system clipboard but with multiple items in
;; it. If you copy a bunch of things in another program, Emacs normally only
;; knows about the last one copied, but with clipmon mode on, it will monitor
;; the system clipboard and add any new text it sees to the kill ring.)
;;
;;
;;;; Installation
;; ----------------------------------------------------------------------------
;;
;; It's simplest to use the package manager:
;;
;;     M-: (package-install 'clipmon)
;;
;; It will then be ready to use, and will also be available the next time you
;; start Emacs.
;;
;;
;;;; Usage
;; ----------------------------------------------------------------------------
;;
;; To give it a try, do M-: (clipmon-autoinsert-toggle) - this will turn on
;; autoinsert. Then go to another application and copy some text to the
;; clipboard - clipmon should detect it after a second or two and make a beep.
;; If you switch back to Emacs, the text should be there in your buffer.
;;
;; Note that you can still yank and pull text in Emacs as usual while autoinsert
;; is on, since it only monitors the system clipboard.
;;
;; You can turn off autoinsert with the same command - to add a keybinding to it
;; add something like this to your init file:
;;
;;     (global-set-key (kbd "<M-f2>") 'clipmon-autoinsert-toggle)
;;
;; You can also turn it on and off from the Options menu.
;;
;; Also, if no change is detected after a certain number of minutes, autoinsert will
;; turn itself off automatically with another beep. This is so you don't forget
;; that autoinsert is on and accidentally add text to your buffer.
;;
;; And note: if you happen to copy the same text to the clipboard twice, clipmon
;; won't know about the second time, as it only detects changes. And if you copy
;; text faster than the timer interval is set it may miss some changes, but you
;; can adjust the interval.
;;
;;
;;;; Using as a clipboard manager
;; ----------------------------------------------------------------------------
;;
;; To try out clipmon as a clipboard manager, make sure clipmon-mode is on by
;; doing M-: (clipmon-mode 1) (also accessible from the Options menu) and that
;; autoinsert is off, then copy a few pieces of text from another program (more
;; slowly than the default timer interval of 2 seconds though). Switch back to
;; Emacs, and see that you can yank any of the text back with C-y, M-y, M-y...
;;
;; Note that when you turn on autoinsert, it also turns on clipmon-mode, to
;; capture text to the kill ring, but if you'd like to turn on clipmon-mode
;; automatically, you can add this to your init file:
;;
;;     ;; monitor the system clipboard and add any changes to the kill ring
;;     (add-to-list 'after-init-hook 'clipmon-mode-start)
;;
;; You can also use the package browse-kill-ring to manage the kill ring - you
;; can install it with M-: (package-install 'browse-kill-ring), then call
;; `browse-kill-ring' to see the contents of the kill ring, insert from it,
;; delete items, etc. Helm also has a package called helm-ring, with the
;; function `helm-show-kill-ring'.
;;
;; You can persist the kill ring between sessions if you'd like (though note
;; that this might involve writing sensitive information like passwords to the
;; disk - although you could always delete such text from the kill ring with
;; `browse-kill-ring-delete'). To do so, add this to your init file:
;;
;;     ;; persist the kill ring between sessions
;;     (add-to-list 'after-init-hook 'clipmon-persist)
;;
;; This will use Emacs's savehist library to save the kill ring, both at the end
;; of the session and at set intervals. However, savehist also saves various
;; other settings by default, including the minibuffer history - see
;; `savehist-mode' for more details. To change the autosave interval, add
;; something like this:
;;
;;     (setq savehist-autosave-interval (* 5 60)) ; save every 5 minutes (default)
;;
;; The kill ring has a fixed number of entries which you can set, depending on
;; how much history you want to save between sessions:
;;
;;     (setq kill-ring-max 500) ; default is 60 in Emacs 24.4
;;
;; To see how much space the kill-ring is taking up, you can call this function:
;;
;;     (clipmon-kill-ring-total)
;;     => 29670 characters
;;
;;
;;;; Options
;; ----------------------------------------------------------------------------
;;
;; There are various options you can set with customize:
;;
;;     (customize-group 'clipmon)
;;
;; or set them in your init file - these are the default values:
;;
;;     (setq clipmon-timer-interval 2)       ; check system clipboard every n secs
;;     (setq clipmon-autoinsert-sound t)     ; t for included beep, or path or nil
;;     (setq clipmon-autoinsert-color "red") ; color of cursor when autoinsert is on
;;     (setq clipmon-autoinsert-timeout 5)   ; stop autoinsert after n mins inactivity
;;
;; before inserting the text, transformations are performed on it in this order:
;;
;;     (setq clipmon-transform-trim t)        ; remove leading whitespace
;;     (setq clipmon-transform-remove         ; remove text matching this regexp
;;           "\\[[0-9][0-9]?[0-9]?\\]\\|\\[citation needed\\]\\|\\[by whom?\\]")
;;     (setq clipmon-transform-prefix "")     ; add to start of text
;;     (setq clipmon-transform-suffix "\n\n") ; add to end of text
;;     (setq clipmon-transform-function nil)  ; additional transform function
;;
;;
;;;; Todo
;; ----------------------------------------------------------------------------
;;
;; - Prefix with C-u to set a target point, then allow cut/copy/pasting from
;;   within Emacs, eg to take notes from another buffer, or move text elsewhere.
;;
;;
;;; Code:

;;;; Renamings
;; ----------------------------------------------------------------------------

;; just renaming some things here - must come before defcustoms.
;; could remove after some time though.

(eval-when-compile ; because it's a macro
  (defalias 'clipmon--rename 'define-obsolete-variable-alias))

;; rename old to new
(clipmon--rename 'clipmon-interval      'clipmon-timer-interval     "20150211")
(clipmon--rename 'clipmon-cursor-color  'clipmon-autoinsert-color   "20150211")
(clipmon--rename 'clipmon-sound         'clipmon-autoinsert-sound   "20150211")
(clipmon--rename 'clipmon-timeout       'clipmon-autoinsert-timeout "20150211")
(clipmon--rename 'clipmon-trim          'clipmon-transform-trim     "20150211")
(clipmon--rename 'clipmon-remove-regexp 'clipmon-transform-remove   "20150211")
(clipmon--rename 'clipmon-prefix        'clipmon-transform-prefix   "20150211")
(clipmon--rename 'clipmon-suffix        'clipmon-transform-suffix   "20150211")

;; FIXME how just mark as obsolete/removed?
(clipmon--rename 'clipmon-action        'clipmon-action-obsolete    "20150211")


;;;; Public settings
;; ----------------------------------------------------------------------------

(defgroup clipmon nil
  "Clipboard monitor - add clipboard contents to kill ring and automatically insert."
  :group 'convenience
  :group 'killing)

(defcustom clipmon-timer-interval 2
  "Interval for checking system clipboard for changes, in seconds."
  :group 'clipmon
  :type 'integer)

(defcustom clipmon-autoinsert-color "red"
  "Color to set cursor when clipmon autoinsert is on.  Set to nil for no change."
  :group 'clipmon
  :type 'color)

(defcustom clipmon-autoinsert-sound t
  "Path to sound file to play on autoinsert, t for included file, or nil.
Use t for the included sound file (see
`clipmon--included-sound-file'), nil for no sound, or path to an
audio file - Emacs can play .wav or .au files."
  ; Note: can't use `ding' here because it doesn't make a sound when Emacs
  ; doesn't have focus.
  :group 'clipmon
  :type '(radio
          (string :tag "Audio file (.wav or .au)")
          (boolean :tag "Included sound file")))

(defcustom clipmon-autoinsert-timeout 5
  "Stop autoinsert if no system clipboard activity after this many minutes.
Set to nil for no timeout."
  :group 'clipmon
  :type 'integer)


;; transforms on text - these are performed in this order

(defcustom clipmon-transform-trim t
  "If non-nil, remove leading whitespace from string before autoinserting.
Often it's hard to select text without grabbing a leading space,
so this will remove it."
  :group 'clipmon
  :type 'boolean)

(defcustom clipmon-transform-remove
  "\\[[0-9][0-9]?[0-9]?\\]\\|\\[citation needed\\]\\|\\[by whom?\\]"
  "Any text matching this regexp will be removed before autoinserting.
e.g. Wikipedia-style references with 1-3 digits - [3], [115]."
  :group 'clipmon
  :type 'regexp)

(defcustom clipmon-transform-prefix ""
  "String to add to start of clipboard contents before autoinserting."
  :group 'clipmon
  :type 'string)

(defcustom clipmon-transform-suffix "\n\n"
  "String to add to end of clipboard contents before autoinserting.
Default is two newlines, which leaves a blank line between clips.
\(To add a newline in the customize interface, type \\[quoted-insert] C-j)."
  :group 'clipmon
  :type 'string)

(defcustom clipmon-transform-function nil
  "Function to perform additional transformations on text before autoinserting.
Receives one argument, the clipboard text - should return the changed text.
E.g. to make the text lowercase before pasting,
    (setq clipmon-transform-function (lambda (s) (downcase s)))"
  :group 'clipmon
  :type 'function
  :risky t)


;;;; Initialize
;; ----------------------------------------------------------------------------

; add items to Options menu
;;;###autoload
(define-key-after global-map [menu-bar options clipmon-separator] ; path to new item
  '(menu-item "---")
  'highlight-paren-mode) ; add after this

;;;###autoload
(define-key-after global-map [menu-bar options clipmon-killring] ; path to new item
  '(menu-item "Clipboard Monitor (Add to Kill Ring)"
              clipmon-mode ; function to call on click
              :help "Add changes to the system clipboard to Emacs's kill ring."
              :button (:toggle . clipmon-mode)) ; show checkmark on/off
  'clipmon-separator) ; add after this

;;;###autoload
(define-key-after global-map [menu-bar options clipmon-autoinsert] ; path to new item
  '(menu-item "Clipboard Monitor Autoinsert"
              clipmon-autoinsert-toggle ; function to call on click
              :help "Automatically insert changes to the system clipboard at the current location."
              :button (:toggle . clipmon--autoinsert)) ; show checkmark on/off
  'clipmon-killring) ; add after this


;;;; Private variables
;; ----------------------------------------------------------------------------

(defvar clipmon--timer nil
  "Timer handle for clipboard monitor to watch system clipboard.")

(defvar clipmon--autoinsert nil
  "Non-nil if autoinsert is on.")

(defvar clipmon--autoinsert-timeout-start nil
  "Time that autoinsert timeout timer was started.")

(defvar clipmon--previous-contents nil
  "Last contents of the system clipboard.")

(defvar clipmon--cursor-color-original nil
  "Original cursor color.")

(defconst clipmon--folder
  (file-name-directory (or load-file-name (file-name-directory (buffer-file-name))))
  "Path to clipmon install folder, or current buffer's location.")

(defconst clipmon--included-sound-file
  (expand-file-name "clipmon.wav" clipmon--folder)
  "Path to included audio file.")



;;;; Public functions
;; ----------------------------------------------------------------------------

;;;###autoload
(define-minor-mode clipmon-mode
  "Start/stop clipboard monitor - watch system clipboard, add changes to kill ring.

To also insert the changes to the system clipboard at the current
location, call `clipmon-autoinsert-toggle' to turn autoinsert on
and off. See commentary in source file for more information -
M-: (find-library 'clipmon).

Upgrade note (2015-02-11): you'll need to bind your shortcut key to
`clipmon-autoinsert-toggle' instead of `clipmon-mode'."
  :global t
  :lighter ""
  ; value of clipmon-mode is toggled before this implicitly
  (if clipmon-mode (clipmon-mode-start) (clipmon-mode-stop)))


;;;###autoload
(defun clipmon-mode-start ()
  "Start clipboard monitor - watch system clipboard, add changes to kill ring."
  (interactive)
  (setq clipmon-mode t) ; in case called outside of clipmon-mode fn
  (unless clipmon--timer
    (setq clipmon--previous-contents (clipmon--clipboard-contents))
    (setq clipmon--timer
          (run-at-time nil clipmon-timer-interval 'clipmon--check-clipboard))
    (message "Clipboard monitor started - watching system clipboard, adding changes to kill ring.")
    ))


(defun clipmon-mode-stop ()
  "Stop clipboard monitor and autoinsert modes."
  (interactive)
  (setq clipmon-mode nil) ; in case called outside of clipmon-mode fn
  (when clipmon--timer
    (cancel-timer clipmon--timer)
    (setq clipmon--timer nil)
    (if clipmon--autoinsert (clipmon-autoinsert-stop)) ; turn off autoinsert also
    (message "Clipboard monitor stopped.")
    ))


;;;###autoload
(defun clipmon-autoinsert-toggle ()
  "Turn autoinsert on/off - watch system clipboard and insert changes.
Will change cursor color and play a sound.  Text will be
transformed before insertion according to various settings - see
`clipmon--transform-text'."
  (interactive)
  ;; note: a minor mode would toggle the value here rather than in the fns
  (if clipmon--autoinsert (clipmon-autoinsert-stop) (clipmon-autoinsert-start)))


(defun clipmon-autoinsert-start ()
  "Turn on autoinsert - change cursor color, play sound, insert changes."
  (interactive)
  (if (null clipmon--timer) (clipmon-mode-start)) ; make sure clipmon is on
  (if clipmon--autoinsert
      (message "Clipboard monitor autoinsert already on.")
    (setq clipmon--autoinsert-timeout-start (current-time))
    (when clipmon-autoinsert-color
      (setq clipmon--cursor-color-original (face-background 'cursor))
      (set-face-background 'cursor clipmon-autoinsert-color))
    (message
     "Clipboard monitor autoinsert started with timer interval %g seconds. Stop with %s."
     clipmon-timer-interval
     (substitute-command-keys "\\[clipmon-autoinsert-toggle]")) ; eg "<M-f2>"
    (clipmon--play-sound)
    (setq clipmon--autoinsert t)
    ))


(defun clipmon-autoinsert-stop (&optional msg)
  "Turn off autoinsert - restore cursor color and play sound.
Show optional message MSG, or default message."
  (interactive)
  (if (null clipmon--autoinsert)
      (message "Clipboard monitor autoinsert already off.")
    (if clipmon--cursor-color-original
        (set-face-background 'cursor clipmon--cursor-color-original))
    (message (or msg "Clipboard monitor autoinsert stopped."))
    (clipmon--play-sound)
    (setq clipmon--autoinsert nil)
    ))


;;;###autoload
(defun clipmon-persist ()
  "Persist the kill ring to disk using Emacs's savehist library.
Will save the kill ring at the end of the session and at various
intervals as specified by variable `savehist-autosave-interval'.
Note that savehist also includes various other Emacs settings by
default, including the minibuffer history - see function
`savehist-mode' for more details."
  (require 'savehist)
  (defvar savehist-additional-variables) ; for compiler warning
  (add-to-list 'savehist-additional-variables 'kill-ring)
  (savehist-mode 1))


;;;; Private functions
;; ----------------------------------------------------------------------------

(defun clipmon--check-clipboard ()
  "Check the clipboard and call `clipmon--on-clipboard-change' if changed.
Otherwise check autoinsert idle timer and stop if it's been idle a while."
  (let ((s (clipmon--clipboard-contents))) ; s may actually be nil here
    (if (and s (not (string-equal s clipmon--previous-contents))) ; if not nil, and changed
        (clipmon--on-clipboard-change s) ; add to kill-ring, autoinsert
      ;; otherwise stop autoinsert if clipboard has been idle a while
      (if (and clipmon--autoinsert clipmon-autoinsert-timeout)
          (let ((idle-seconds (clipmon--seconds-since clipmon--autoinsert-timeout-start)))
            (when (>= idle-seconds (* 60 clipmon-autoinsert-timeout))
              (clipmon-autoinsert-stop (format
                  "Clipboard monitor autoinsert stopped after %g minutes of inactivity."
                  clipmon-autoinsert-timeout))
              ))))))


(defun clipmon--on-clipboard-change (s)
  "Clipboard changed - add text S to kill ring, and optionally insert it."
  (setq clipmon--previous-contents s) ; save contents
  (kill-new s) ; add to kill ring
  (when clipmon--autoinsert
    (setq s (clipmon--autoinsert-transform-text s))
    (insert s)
    (undo-boundary) ; mark a boundary between undo units
    (clipmon--play-sound)
    (setq clipmon--autoinsert-timeout-start (current-time)))) ; reset timeout


(defun clipmon--autoinsert-transform-text (s)
  "Apply autoinsert transformations to clipboard text S."
  (if clipmon-transform-trim (setq s (clipmon--trim-left s)))
  (if clipmon-transform-remove
      (setq s (replace-regexp-in-string clipmon-transform-remove "" s)))
  (if clipmon-transform-prefix (setq s (concat clipmon-transform-prefix s)))
  (if clipmon-transform-suffix (setq s (concat s clipmon-transform-suffix)))
  (if clipmon-transform-function (setq s (funcall clipmon-transform-function s)))
  s)


(defun clipmon--play-sound ()
  "Play a user-specified sound file, the included sound file, or nothing."
  (if clipmon-autoinsert-sound
      (if (stringp clipmon-autoinsert-sound)
          ;; play-sound-file can throw an error if no sound device found
          (ignore-errors (play-sound-file clipmon-autoinsert-sound))
          (ignore-errors (play-sound-file clipmon--included-sound-file)))))



;;;; Library functions
;; ----------------------------------------------------------------------------

(defun clipmon-kill-ring-total ()
  "Get total size of kill ring, in characters."
  (let ((sum 0))
    (mapc (lambda (s) (setq sum (+ sum (length s)))) kill-ring) sum))


(defun clipmon--remove-properties (s)
  "Remove formatting properties from string S."
  (if (null s) nil
    (substring-no-properties s)))


(defun clipmon--get-selection ()
  "Get the clipboard contents"
  ;; Note: When the OS is first started these functions will throw
  ;; (error "No selection is available"), so need to ignore errors.
  (cond ((fboundp 'gui-get-selection) ; emacs25
         ; better to (setq selection-coding-system 'utf-8) to handle chinese,
         ; which is the default value for gui-get-selection etc
         ; because windows needs STRING. same below.
         ; (ignore-errors (gui-get-selection 'CLIPBOARD 'UTF8_STRING)))
         (ignore-errors (gui-get-selection 'CLIPBOARD))) ; for windows needs STRING
        ((eq window-system 'w32) ; windows/emacs24
         ;; Note: (x-get-selection 'CLIPBOARD) doesn't work on Windows.
         (ignore-errors (x-get-selection-value))) ; can be nil
        (t ; linux+osx/emacs24
         ; (ignore-errors (x-get-selection 'CLIPBOARD 'UTF8_STRING)))))
         (ignore-errors (x-get-selection 'CLIPBOARD)))))


(defun clipmon--clipboard-contents ()
  "Get current contents of system clipboard - returns a string, or nil."
  ;;. do we really need to remove the text properties?
  (let ((text (clipmon--remove-properties (clipmon--get-selection)))
        (top-of-kill-ring (clipmon--remove-properties (car kill-ring))))
    (cond ((null text) nil)
          ;; don't return the text if user just copied/cut it from emacs
          ((string= text top-of-kill-ring) nil)
          (t text))))


(defun clipmon--trim-left (s)
  "Remove leading spaces from string S."
  (replace-regexp-in-string  "^[ \t]+"  ""  s))


(defun clipmon--seconds-since (time)
  "Return number of seconds elapsed since the given TIME.
TIME should be in Emacs time format (see `current-time').
Includes approximate number of milliseconds also.
Valid for up to 2**16 seconds = 65536 secs ~ 18hrs."
  (let* ((elapsed (time-subtract (current-time) time))
         (seconds (nth 1 elapsed))
         (microseconds (nth 2 elapsed)) ; accurate to milliseconds on my system, anyway
         (total (+ seconds (/ microseconds 1.0e6))))
    total))


;;;; Footer
;; ----------------------------------------------------------------------------

(provide 'clipmon)

;; Local Variables:
;; indent-tabs-mode: nil
;; End:
;;; clipmon.el ends here
