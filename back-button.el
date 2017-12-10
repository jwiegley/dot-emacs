;;; back-button.el --- Visual navigation through mark rings
;;
;; Copyright (c) 2012-2015 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/back-button
;; URL: http://raw.githubusercontent.com/rolandwalker/back-button/master/back-button.el
;; Version: 0.6.8
;; Last-Updated:  4 Aug 2015
;; EmacsWiki: BackButton
;; Keywords: convenience, navigation, interface
;; Package-Requires: ((nav-flash "1.0.0") (smartrep "0.0.3") (ucs-utils "0.7.2") (list-utils "0.4.2") (persistent-soft "0.8.8") (pcache "0.2.3"))
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'back-button)
;;
;;     (back-button-mode 1)
;;
;;     press the plus sign in the toolbar to create a mark
;;
;;     press the arrows in the toolbar to navigate marks
;;
;;     or use C-x C-Space as usual, then try C-x C-<right>
;;     to reverse the operation
;;
;; Explanation
;;
;; Back-button provides an alternative method for navigation by
;; analogy with the "back" button in a web browser.
;;
;; Every Emacs command which pushes the mark leaves behind an
;; invisible record of the location of the point at that moment.
;; Back-button moves the point back and forth over all the positions
;; where some command pushed the mark.
;;
;; This is essentially a replacement for `pop-global-mark', and the
;; default keybindings (when the minor mode is activated) override
;; that command.  The differences with `pop-global-mark' are:
;;
;;    - Visual index showing how far you have traveled in the
;;      mark ring.
;;
;;    - Easy way to move both forward and backward in the ring.
;;
;;    - Pushes a mark on the first of a series of invocations, so you
;;      can always return to where you issued the command.
;;
;;    - Skips duplicate positions, so that the interactive command
;;      always moves the point if possible.
;;
;; Commands and keybindings are also included to give identical
;; semantics for navigating the local (per-buffer) `mark-ring'.  This
;; consistency in navigation comes at the cost of pushing the mark
;; twice, so experienced Emacs users may prefer to unbind these
;; commands and/or set `back-button-never-push-mark' in customize.
;;
;; To use back-button, place the back-button.el library somewhere
;; Emacs can find it, and add the following to your ~/.emacs file:
;;
;;     (require 'back-button)
;;     (back-button-mode 1)
;;
;; Default key bindings:
;;
;;     C-x C-<SPC>    go back in `global-mark-ring', respects prefix arg
;;     C-x C-<left>   go back in `global-mark-ring'
;;     C-x C-<right>  go forward in `global-mark-ring'
;;
;;     C-x <SPC>      go back in (buffer-local) `mark-ring', respects prefix arg
;;     C-x <left>     go back in (buffer-local) `mark-ring'
;;     C-x <right>    go forward in (buffer-local) `mark-ring'
;;
;; When the smartrep package is installed, the C-x prefix need not
;; be used for consecutive back-button commands.
;;
;; When the visible-mark package is installed, marks will be
;; made visible in the current buffer during navigation.
;;
;; See Also
;;
;;     M-x customize-group RET back-button RET
;;     M-x customize-group RET editing-basics RET
;;     M-x customize-group RET visible-mark RET
;;     M-x customize-group RET nav-flash RET
;;
;; Notes
;;
;;     This library depends upon other commands pushing the mark to
;;     provide useful waypoints for navigation.  This is a common
;;     convention, but not universal.
;;
;;     The function `back-button-push-mark-local-and-global' may be
;;     useful to call from Lisp.  It is a replacement for `push-mark'
;;     which unconditionally pushes onto the global mark ring,
;;     functionality which is not possible using vanilla `push-mark'.
;;
;;     Theoretically, `back-button-push-mark-local-and-global' could
;;     cause issues with Lisp code which depends on the convention that
;;     `global-mark-ring' not contain consecutive marks in the same
;;     buffer.  However, no such issues have been observed.
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 24.4-devel     : yes, at the time of writing
;;     GNU Emacs version 24.3           : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.2           : yes, with some limitations
;;     GNU Emacs version 21.x and lower : unknown
;;
;;     Uses if present: smartrep.el, nav-flash.el, visible-mark.el,
;;                      ucs-utils.el
;;
;; Bugs
;;
;;     Pressing the toolbar back-button can navigate to a different
;;     buffer with a different toolbar (and no back-button).
;;
;;     Toolbar button disabling is not dependable.  Logic is left
;;     in place but unused.
;;
;;     Toolbar shift-click does not work in Cocoa Emacs.
;;
;;     Toolbar shift-click is not consistent with keyboard bindings
;;     (control for global ring, unmodified for local ring)
;;
;;     Displaying the index in a popup requires unreleased popup-volatile.el
;;
;; TODO
;;
;;     better toolbar icons
;;
;;     bug in visible-mark bug when mark is on last char of line
;;
;;     integrated delete-mark
;;
;;     could remove smartrep and implement mini-mode that includes
;;     extra commands such as delete-mark and perhaps digits
;;     for visible marks
;;
;;     Used to remember thumb between series, so long as no mark was
;;     pushed, now that does not work b/c these functions themselves
;;     push the mark -- make that an option?  Maybe the right way is
;;     to keep it out-of-band.
;;
;;     this is a crude but general way to force a navigation
;;     command to push the mark:
;;
;;         (defvar push-mark-before-goto-char nil)
;;         (defadvice goto-char (before push-mark-first activate)
;;           (when push-mark-before-goto-char
;;             (back-button-push-mark-local-and-global nil t)))
;;         ;; example use
;;         (defun ido-imenu-push-mark ()
;;           (interactive)
;;           (let ((push-mark-before-goto-char t))
;;             (ido-imenu)))
;;
;;     A better way would be: using a pre-command-hook, track series of
;;     related navigation commands (defined by a property placed on
;;     each command).  Push a global mark for the first of a related
;;     series, don't push for subsequent.  There is already a property
;;     placed on some navigation commands which might be sufficient -
;;     or is that only scroll commands?  There is a package AutoMark
;;     which purports to do this, but it doesn't do the hard part of
;;     classifying all commands.
;;
;;; License
;;
;; Simplified BSD License:
;;
;; Redistribution and use in source and binary forms, with or
;; without modification, are permitted provided that the following
;; conditions are met:
;;
;;    1. Redistributions of source code must retain the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer.
;;
;;    2. Redistributions in binary form must reproduce the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer in the documentation and/or other materials
;;       provided with the distribution.
;;
;; This software is provided by Roland Walker "AS IS" and any express
;; or implied warranties, including, but not limited to, the implied
;; warranties of merchantability and fitness for a particular
;; purpose are disclaimed.  In no event shall Roland Walker or
;; contributors be liable for any direct, indirect, incidental,
;; special, exemplary, or consequential damages (including, but not
;; limited to, procurement of substitute goods or services; loss of
;; use, data, or profits; or business interruption) however caused
;; and on any theory of liability, whether in contract, strict
;; liability, or tort (including negligence or otherwise) arising in
;; any way out of the use of this software, even if advised of the
;; possibility of such damage.
;;
;; The views and conclusions contained in the software and
;; documentation are those of the authors and should not be
;; interpreted as representing official policies, either expressed
;; or implied, of Roland Walker.
;;
;;; Code:
;;

;;; requirements

;; for decf, callf, position
(require 'cl)

(require 'smartrep     nil t)
(require 'nav-flash    nil t)
(require 'visible-mark nil t)
(require 'ucs-utils    nil t)

;;; declarations

(declare-function ucs-utils-char                    "ucs-utils.el")
(declare-function smartrep-define-key               "smartrep.el")
(declare-function visible-mark-initialize-overlays  "visible-mark.el")
(declare-function visible-mark-move-overlays        "visible-mark.el")
(declare-function back-button-push-mark             "back-button.el")

(eval-when-compile
  (defvar visible-mark-mode)
  (defvar visible-mark-overlays))

;;; customizable variables

;;;###autoload
(defgroup back-button nil
  "Visual navigation through mark rings."
  :version "0.6.8"
  :link '(emacs-commentary-link :tag "Commentary" "back-button")
  :link '(url-link :tag "GitHub" "http://github.com/rolandwalker/back-button")
  :link '(url-link :tag "EmacsWiki" "http://emacswiki.org/emacs/BackButton")
  :prefix "back-button-"
  :group 'convenience
  :group 'navigation)

(defcustom back-button-mode-lighter " back"
  "This string appears in the mode-line when `back-button-mode' is active.

Set to nil or the empty string to disable the mode-line
lighter for `back-button-mode'."
  :type 'string
  :group 'back-button)
(put 'back-button-mode-lighter 'risky-local-variable t)

(defcustom back-button-less-feedback nil
  "Give less echo area feedback."
  :type 'boolean
  :group 'back-button)

(defcustom back-button-show-toolbar-buttons t
  "Add buttons to the toolbar."
  :type 'boolean
  :group 'back-button)

(defcustom back-button-show-visible-marks t
  "Temporarily show marks using `visible-mark' when available."
  :type 'boolean
  :group 'back-button)

(defcustom back-button-no-wrap nil
  "Do not wrap around the ring when navigating marks."
  :type 'boolean
  :group 'back-button)

(defcustom back-button-never-push-mark nil
  "Never add a mark while navigating marks.

This option makes the back-button command work more like the
standard `pop-global-mark command', but breaks the functionality
of remembering the start location."
  :type 'boolean
  :group 'back-button)

;;;###autoload
(defgroup back-button-index nil
  "How to display the mark-ring index after interactive commands."
  :group 'back-button)

(defcustom back-button-show-index 'echo
  "How to display the mark-ring index.

This indicator shows progress through the ring after each
command."
  :type '(choice
          (const :tag "Echo Area"  echo)
          (const :tag "Popup"      popup)
          (const :tag "None"       nil))
  :group 'back-button-index)

(defcustom back-button-index-timeout 2
  "How long to display the mark-ring index after each command.

Set to nil or 0 for no timeout."
  :type 'number
  :group 'back-button-index)

(defcustom back-button-index-spacer-ucs-name "Middle Dot"
  "UCS character name for index display spacer."
  :type 'string
  :group 'back-button-index)

(defcustom back-button-index-thumb-ucs-name "Circled Dot Operator"
  "UCS character name for index display thumb."
  :type 'string
  :group 'back-button-index)

;;;###autoload
(defgroup back-button-keys nil
  "Key bindings for `back-button-mode'."
  :group 'back-button)

(defcustom back-button-smartrep-prefix "C-x"
  "Prefix key for smartrep.el bindings.

Smartrep bindings will be installed for all back-button key
bindings which match this prefix.

The format for key sequences is as defined by `kbd'.

Set to nil or the empty string to disable smartrep for
`back-button-mode'."
  :type 'string
  :group 'back-button-keys)

(defcustom back-button-global-keystrokes '("C-x <C-SPC>")
  "List of key sequences to invoke `back-button-global'.

The default binding overrides `pop-global-mark'.

The key bindings are in effect when `back-button-mode' minor mode
is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'back-button-keys)

(defcustom back-button-global-backward-keystrokes '("C-x <C-left>")
  "List of key sequences to invoke `back-button-global-backward'.

The key bindings are in effect when `back-button-mode' minor mode
is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'back-button-keys)

(defcustom back-button-global-forward-keystrokes '("C-x <C-right>")
  "List of key sequences to invoke `back-button-global-forward'.

The key bindings are in effect when `back-button-mode' minor mode
is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'back-button-keys)

(defcustom back-button-local-keystrokes '("C-x <SPC>")
  "List of key sequences to invoke `back-button-local'.

The key bindings are in effect when `back-button-mode' minor mode
is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'back-button-keys)

(defcustom back-button-local-backward-keystrokes '("C-x <left>")
  "List of key sequences to invoke `back-button-local-backward'.

The key bindings are in effect when `back-button-mode' minor mode
is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'back-button-keys)

(defcustom back-button-local-forward-keystrokes '("C-x <right>")
  "List of key sequences to invoke `back-button-local-forward'.

The key bindings are in effect when `back-button-mode' minor mode
is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'back-button-keys)

;;; variables

(defvar back-button-mode                     nil "Whether `back-button-mode' minor-mode is on.")
(defvar back-button-local-marks-copy         nil "A remembered set of local marks.")
(defvar back-button-global-marks-copy        nil "A remembered set of global marks.")
(defvar back-button-global-disable-direction nil "Supplementary info for disabling toolbar buttons.")
(defvar back-button-commands '(
                               back-button-global
                               back-button-global-backward
                               back-button-global-forward
                               back-button-local
                               back-button-local-backward
                               back-button-local-forward
                               )
  "List of back-button interactive navigation commands.")

(defvar back-button-spacer-char     ?.  "Character used to indicate marks available for navigation.")
(defvar back-button-thumb-char      ?o  "Character used to indicate current mark.")

(when (featurep 'ucs-utils)
  (setq back-button-spacer-char (ucs-utils-char back-button-index-spacer-ucs-name back-button-spacer-char 'cdp))
  (setq back-button-thumb-char  (ucs-utils-char back-button-index-thumb-ucs-name  back-button-thumb-char  'cdp)))

(defvar back-button-lighter-menu-mouse-button 1
  "Which mouse button invokes the modeline context menu.")

(defvar back-button-lighter-keymap-property 'keymap
  "Which property sets the lighter keymap")


;;; compatibility functions

(unless (fboundp 'string-match-p)
  ;; added in 23.x
  (defun string-match-p (regexp string &optional start)
    "Same as `string-match' except this function does not change the match data."
    (let ((inhibit-changing-match-data t))
      (string-match regexp string start))))

;;; keymaps

(defvar back-button-mode-map (make-sparse-keymap) "Keymap for `back-button-mode' minor-mode.")

(let ((smart-keys nil))
  (dolist (cmd back-button-commands)
    (dolist (k (symbol-value (intern (concat (symbol-name cmd) "-keystrokes"))))
      (when (and (not (string-match-p "mouse\\|wheel\\|button" k))
                 (not (get cmd :advertised-binding)))
        (put cmd :advertised-binding (read-kbd-macro k)))
      (if (and (featurep 'smartrep)
               (stringp back-button-smartrep-prefix)
               (> (length back-button-smartrep-prefix) 0)
               (string-match-p (concat "\\`" back-button-smartrep-prefix "\\>") k))
          (push (cons (replace-regexp-in-string
                       (concat "\\`" back-button-smartrep-prefix "\\>[ \t]*")
                       ""
                       k)
                      cmd)
                smart-keys)
        ;; else
        (define-key back-button-mode-map (read-kbd-macro k) cmd))))
  (when smart-keys
    (smartrep-define-key back-button-mode-map back-button-smartrep-prefix smart-keys)))

;;; toolbar

(when back-button-show-toolbar-buttons

  (define-key-after tool-bar-map [separator-backb] (if (boundp 'menu-bar-separator) menu-bar-separator "--"))

  (tool-bar-add-item "left-arrow"
                     'back-button-global-backward
                     'back-button
                     :label "Back By Mark"
                     :visible '(and back-button-mode back-button-show-toolbar-buttons))
                     ;; todo why is this not reliable?
                     ;; :enable '(and (not (eq back-button-global-disable-direction 'back))
                     ;;               (> (length global-mark-ring) 0)))

  (tool-bar-add-item "mpc/add"
                     'back-button-push-mark-local-and-global
                     'back-button-push
                     :label "push Mark"
                     :visible '(and back-button-mode back-button-show-toolbar-buttons))

  (tool-bar-add-item "right-arrow"
                     'back-button-global-forward
                     'forward-button
                     :label "Forward By Mark"
                     :visible '(and back-button-mode back-button-show-toolbar-buttons))
                     ;; todo why is this not reliable?
                     ;; :enable '(and (not (eq back-button-global-disable-direction 'forward))
                     ;;               (> (length global-mark-ring) 0)
                     ;;               this-command
                     ;;               (memq this-command back-button-commands)))

  ;; Note, this seems to not work on some platforms, eg Cocoa
  (define-key global-map (kbd "<tool-bar> <S-back-button>")    'back-button-local-backward)
  (define-key global-map (kbd "<tool-bar> <S-forward-button>") 'back-button-local-forward))

;;; lighter

(defvar back-button-lighter-map  (let ((map (make-sparse-keymap))
                                       (menu-map (make-sparse-keymap "Back Button")))
                                   (define-key menu-map [customize]                   '(menu-item "Customize"      (lambda (e) (interactive "e") (customize-group 'back-button))))
                                   (define-key menu-map [turn-off-back-button-mode]   '(menu-item "Turn Off Back Button Mode"  back-button-mode))
                                   (define-key menu-map [separator-1]                 '(menu-item "--"))
                                   (define-key menu-map [local-forward]               (append '(menu-item "Local Forward" back-button-local-forward)
                                                                                              ;; force advertised binding because of smartrep
                                                                                              (when (get 'back-button-local-forward :advertised-binding)
                                                                                                (list :keys
                                                                                                      (format-kbd-macro
                                                                                                       (get 'back-button-local-forward :advertised-binding))))))
                                   (define-key menu-map [local-back]                  (append '(menu-item "Local Back" back-button-local-backward)
                                                                                              (when (get 'back-button-local-backward :advertised-binding)
                                                                                                (list :keys
                                                                                                      (format-kbd-macro
                                                                                                       (get 'back-button-local-backward :advertised-binding))))))
                                   (define-key menu-map [forward]                     (append '(menu-item "Forward" back-button-global-forward)
                                                                                              (when (get 'back-button-global-forward :advertised-binding)
                                                                                                (list :keys
                                                                                                      (format-kbd-macro
                                                                                                       (get 'back-button-global-forward :advertised-binding))))))
                                   (define-key menu-map [back]                        (append '(menu-item "Back" back-button-global-backward)
                                                                                              (when (get 'back-button-global-backward :advertised-binding)
                                                                                                (list :keys
                                                                                                      (format-kbd-macro
                                                                                                       (get 'back-button-global-backward :advertised-binding))))))
                                   (define-key map (kbd "<mode-line> <wheel-up>"     ) 'back-button-global-backward)
                                   (define-key map (kbd "<mode-line> <wheel-down>"   ) 'back-button-global-forward)
                                   (define-key map (kbd "<mode-line> <C-wheel-up>"   ) 'back-button-local-backward)
                                   (define-key map (kbd "<mode-line> <C-wheel-down>" ) 'back-button-local-forward)
                                   (define-key map (kbd "<mode-line> <mouse-4>"      ) 'back-button-global-backward)
                                   (define-key map (kbd "<mode-line> <mouse-5>"      ) 'back-button-global-forward)
                                   (define-key map (kbd "<mode-line> <C-mouse-4>"    ) 'back-button-local-backward)
                                   (define-key map (kbd "<mode-line> <C-mouse-5>"    ) 'back-button-local-forward)
                                   (define-key map (read-kbd-macro (format "<mode-line> <down-mouse-%s>" back-button-lighter-menu-mouse-button)) menu-map)
                                   map) "Keymap for the back-button lighter.")

(when (and (stringp back-button-mode-lighter)
           (> (length back-button-mode-lighter) 0))
  (callf propertize back-button-mode-lighter
                    back-button-lighter-keymap-property back-button-lighter-map
                    'help-echo (format "Back-button: mouse-%s menu\nmouse-wheel and control-mouse-wheel to navigate" back-button-lighter-menu-mouse-button)))

;;; macros

(defmacro back-button-called-interactively-p (&optional kind)
  "A backward-compatible version of `called-interactively-p'.

Optional KIND is as documented at `called-interactively-p'
in GNU Emacs 24.1 or higher."
  (cond
    ((not (fboundp 'called-interactively-p))
     '(interactive-p))
    ((condition-case nil
         (progn (called-interactively-p 'any) t)
       (error nil))
     `(called-interactively-p ,kind))
    (t
     '(called-interactively-p))))

;;; aliases et al

;; this fset is done so that (although it is unused herein) the
;; following construct is legal
;;    (flet ((push-mark (&optional location nomsg activate)
;;                      (back-button-push-mark-local-and-global location nomsg activate)))
;;      ... do something that pushes the mark...)
(fset 'back-button-push-mark (symbol-function 'push-mark))

;;; Lisp interface

;; this function can replace push-mark in many circumstances
;; todo make handling of duplicates consistent btw local and global

;;;###autoload
(defun back-button-push-mark-local-and-global (&optional location nomsg activate consecutives)
  "Push mark at LOCATION, and unconditionally add to `global-mark-ring'.

This function differs from `push-mark' in that `global-mark-ring'
is always updated.

LOCATION is optional, and defaults to the current point.

NOMSG and ACTIVATE are as documented at `push-mark'.

When CONSECUTIVES is set to 'limit and the new mark is in the same
buffer as the first entry in `global-mark-ring', the first entry
in `global-mark-ring' will be replaced.  Otherwise, a new entry
is pushed onto `global-mark-ring'.

When CONSECUTIVES is set to 'allow-dupes, it is possible to push
an exact duplicate of the current topmost mark onto `global-mark-ring'."
  (interactive)
  (callf or location (point))
  (back-button-push-mark location nomsg activate)
  (when (or (eq consecutives 'allow-dupes)
            (not (equal (mark-marker)
                        (car global-mark-ring))))
    (when (and (eq consecutives 'limit)
               (eq (marker-buffer (car global-mark-ring)) (current-buffer)))
      (move-marker (car global-mark-ring) nil)
      (pop global-mark-ring))
    (push (copy-marker (mark-marker)) global-mark-ring)
    (when (> (length global-mark-ring) global-mark-ring-max)
      (move-marker (car (nthcdr global-mark-ring-max global-mark-ring)) nil)
      (setcdr (nthcdr (1- global-mark-ring-max) global-mark-ring) nil))))

;;; utility functions

(defun back-button-pre-command-hook ()
  "Re-enable toolbar buttons and hide visible marks."
  (when (and (featurep 'visible-mark)
             (not visible-mark-mode))
    (dolist (buf (buffer-list))
      (with-current-buffer buf
        (when visible-mark-overlays
          (mapc 'delete-overlay visible-mark-overlays)
          (setq visible-mark-overlays nil)))))
  (setq back-button-global-disable-direction nil))

(defun back-button-visible-mark-show (type)
  "Show marks temporarily using `visible-mark'.

TYPE may be 'global or 'local."
  (when (and (featurep 'visible-mark)
             (not visible-mark-mode))
    (dolist (win (window-list))
      (with-current-buffer (window-buffer win)
        (when (not (minibufferp (current-buffer)))
          (let ((visible-mark-max (length mark-ring)))
            (visible-mark-initialize-overlays)
            (when (fboundp 'visible-mark-initialize-faces)
              (visible-mark-initialize-faces))
            (let ((mark-ring mark-ring))
              (when (eq type 'global)
                (setq mark-ring global-mark-ring))
              (visible-mark-move-overlays))))))))

(defun back-button-find-position (thumb type)
  "Find the position of THUMB in the mark ring.

TYPE may be 'global or 'local."
  (let ((ring global-mark-ring)
        (copy back-button-global-marks-copy)
        (posn nil))
    (when (eq type 'local)
      (setq ring mark-ring)
      (setq copy back-button-local-marks-copy))
    (setq posn (or (position thumb copy) 1))
    ;; scan across duplicates and place visible thumb
    ;; on a consistent boundary; looks more intuitive
    (while (and (> posn 0)
                (equal (nth (1- posn) copy) (nth posn copy)))
      (setq posn (1- posn)))
    posn))

(defun back-button-display-index (msg)
  "Briefly display MSG.

MSG is expected to contain a visual representation of mark-ring
traversal progress."
  (let ((message-log-max nil))
    (cond
      ((and (eq back-button-show-index 'echo)
            (numberp back-button-index-timeout)
            (> back-button-index-timeout 0))
       (with-temp-message msg
         (sit-for back-button-index-timeout)))
    ((eq back-button-show-index 'echo)
     (message msg))
    ((and (eq back-button-show-index 'popup)
          (fboundp 'popup-volatile))
     (popup-volatile msg :box t :around t :delay back-button-index-timeout :face '(:background "Gray20" :foreground "#C0C0C0"))))))

(defun back-button-maybe-record-start (type interactive)
  "Push mark for the first of a series of interactive back-button commands.

TYPE may be 'local or 'global.

INTERACTIVE is a boolean value, noting whether this function was
called from an interactive command."
  (when (and interactive
             (not (memq last-command back-button-commands))
             (not back-button-never-push-mark))
    (cond
      ((eq type 'global)
       (back-button-push-mark-local-and-global (point) t nil))
      ((eq type 'local)
       ;; push twice to get position onto mark-ring
       (back-button-push-mark (point) t nil)
       (back-button-push-mark (point) t nil)))))

;; This totally different approach (compared to pop-mark) is needed in
;; the first case b/c pop-mark creates/destroys markers, breaking the
;; memq tests used in back-button-local and back-button-find-index.
(defun back-button-pop-local-mark ()
  "Pop off local `mark-ring' and jump to the top location.

This differs from `pop-mark' completely, instead following the
semantics of `pop-global-mark', moving the point instead of
setting the mark."
  (when mark-ring
    (let* ((marker (car mark-ring))
           (position (marker-position marker)))
    (setq mark-ring (nconc (cdr mark-ring)
                           (list (car mark-ring))))
    (when (and (>= position (point-min))
               (<= position (point-max)))
      (if widen-automatically
          (widen)
        (error "Local mark position is outside accessible part of buffer")))
    (goto-char position))))

;;; minor-mode setup

;;;###autoload
(define-minor-mode back-button-mode
  "Turn on back-button-mode.

When called interactively with no prefix argument this command
toggles the mode.  With a prefix argument, it enables the mode
if the argument is positive and otherwise disables the mode.

When called from Lisp, this command enables the mode if the
argument is omitted or nil, and toggles the mode if the argument
is 'toggle."
  :lighter back-button-mode-lighter
  :keymap back-button-mode-map
  :group 'back-button
  :global t
  (cond
   (back-button-mode
    (add-hook 'pre-command-hook 'back-button-pre-command-hook)
    (when (and (back-button-called-interactively-p 'interactive) (not back-button-less-feedback))
      (message "back-button mode enabled")))
   (t
    (remove-hook 'pre-command-hook 'back-button-pre-command-hook)
    (when (and (back-button-called-interactively-p 'interactive) (not back-button-less-feedback))
      (message "back-button mode disabled")))))

;;; interactive commands

;;;###autoload
(defun back-button-local (arg)
  "Navigate through `mark-ring', using `back-button-pop-local-mark'.

If the point does not move, continue popping the ring until
motion occurs.

With universal prefix ARG, rotate the ring in the opposite
direction.  (The \"forward\" direction by analogy with a
web browser back-button.)"
  (interactive "P")
  (back-button-maybe-record-start 'local (back-button-called-interactively-p 'any))
  (let ((pos (point))
        (counter (length mark-ring))
        (thumb nil)
        (posn nil)
        (stopper :no-stopper))
    (when (or (not back-button-local-marks-copy)
              (not (car mark-ring))
              (not (memq (car mark-ring) back-button-local-marks-copy)))
      (setq back-button-local-marks-copy (copy-sequence mark-ring)))
    (when back-button-no-wrap
      (if (consp arg)
          (setq stopper (car back-button-local-marks-copy))
        (setq stopper (car (last back-button-local-marks-copy)))))
    (when (consp arg)
      (setq mark-ring (nreverse mark-ring)))
    (when back-button-no-wrap
      (setq thumb (car mark-ring)))
    (while (and (not (eq thumb stopper))
                (eq pos (point))
                (> counter 0))
      (back-button-pop-local-mark)
      (setq thumb (car (last mark-ring)))
      (decf counter))
    (when (consp arg)
      (setq mark-ring (nreverse mark-ring)))
    (when (and (not (eq thumb stopper))
               (eq pos (point)))
      (error (concat "local-mark" (if (consp arg) " forward" " back") " failed")))
    (when (eq thumb stopper)
      (goto-char stopper))
    (setq posn (back-button-find-position thumb 'local))
    (back-button-visible-mark-show 'local)
    (when (fboundp 'nav-flash-show)
      (nav-flash-show))
    (back-button-display-index (concat "local marks "
                                       (make-string (- (length back-button-local-marks-copy) posn 1) back-button-spacer-char)
                                       (string back-button-thumb-char)
                                       (make-string posn back-button-spacer-char)))))


;;;###autoload
(defun back-button-global (arg)
  "Navigate through `global-mark-ring', using `pop-global-mark'.

If the point would not move, continue popping the ring until
motion occurs.

With universal prefix ARG, rotate the ring in the opposite
direction.  (The \"forward\" direction by analogy with a
web browser back-button.)"
  (interactive "P")
  (back-button-maybe-record-start 'global (back-button-called-interactively-p 'any))
  (let ((pos (point))
        (buf (current-buffer))
        (counter (length global-mark-ring))
        (thumb nil)
        (posn nil)
        (stopper :no-stopper))
    (when (or (not back-button-global-marks-copy)
              (not (car global-mark-ring))
              (not (memq (car global-mark-ring) back-button-global-marks-copy)))
      (setq back-button-global-marks-copy (copy-sequence global-mark-ring)))
    (when back-button-no-wrap
      (if (consp arg)
          (setq stopper (car back-button-global-marks-copy))
        (setq stopper (car (last back-button-global-marks-copy)))))
    (when (consp arg)
      (setq global-mark-ring (nreverse global-mark-ring)))
    (when back-button-no-wrap
      (setq thumb (car global-mark-ring)))
    (while (and (not (eq thumb stopper))
                (or (minibufferp (current-buffer))
                    (and (eq pos (point))
                         (eq buf (current-buffer))
                         (> counter 0))))
      (pop-global-mark)
      (setq thumb (car (last global-mark-ring)))
      (decf counter))
    (when (consp arg)
      (setq global-mark-ring (nreverse global-mark-ring)))
    (when (and (not (eq thumb stopper))
               (or (minibufferp (current-buffer))
                   (and (eq pos (point))
                        (eq buf (current-buffer)))))
      (error (concat "global-mark" (if (consp arg) " forward" " back") " failed")))
    (when (eq thumb stopper)
      (setq back-button-global-disable-direction (if (consp arg) 'forward 'back))
      (goto-char stopper))
    (setq posn (back-button-find-position thumb 'global))
    (back-button-visible-mark-show 'global)
    (when (fboundp 'nav-flash-show)
      (nav-flash-show))
    (back-button-display-index (concat "global marks "
                                       (make-string (- (length back-button-global-marks-copy) posn 1) back-button-spacer-char)
                                       (string back-button-thumb-char)
                                       (make-string posn back-button-spacer-char)))))

;;;###autoload
(defun back-button-local-backward ()
  "Run `back-button-local' in the backward direction.

Unlike `back-button-local', ignores any prefix argument.

This command is somewhat like a fancier version of
`pop-to-mark-command', though it leaves the mark and
`mark-ring' in a different state."
  (interactive)
  (back-button-maybe-record-start 'local (back-button-called-interactively-p 'any))
  (back-button-local nil))

;;;###autoload
(defun back-button-local-forward ()
  "Run `back-button-local' in the forward direction.

Unlike `back-button-local', ignores any prefix argument.

This command is somewhat like the reverse of
`pop-to-mark-command'."
  (interactive)
  (back-button-maybe-record-start 'local (back-button-called-interactively-p 'any))
  (back-button-local '(4)))

;;;###autoload
(defun back-button-global-backward ()
  "Run `back-button-global' in the backward direction.

Unlike `back-button-global', ignores any prefix argument.

This command is much like a fancier version of
`pop-global-mark'."
  (interactive)
  (back-button-maybe-record-start 'global (back-button-called-interactively-p 'any))
  (back-button-global nil))

;;;###autoload
(defun back-button-global-forward ()
  "Run `back-button-global' in the forward direction.

Unlike `back-button-global', ignores any prefix argument.

This command is much like the reverse of `pop-global-mark'."
  (interactive)
  (back-button-maybe-record-start 'global (back-button-called-interactively-p 'any))
  (back-button-global '(4)))

(provide 'back-button)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;
;; LocalWords: BackButton smartrep NOMSG CONSECUTIVES fset nomsg
;; LocalWords: callf imenu utils pcache devel flet
;;

;;; back-button.el ends here
