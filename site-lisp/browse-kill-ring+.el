;;; browse-kill-ring+.el --- Extensions to `browse-kill-ring.el'.
;;
;; Filename: browse-kill-ring+.el
;; Description: Extensions to `browse-kill-ring.el'.
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2006-2017, Drew Adams, all rights reserved.
;; Created: Tue May 25 16:35:05 2004
;; Version: 0
;; Package-Requires: ((browse-kill-ring "0"))
;; Last-Updated: Tue Feb 21 07:57:49 2017 (-0800)
;;           By: dradams
;;     Update #: 973
;; URL: https://www.emacswiki.org/emacs/download/browse-kill-ring%2b.el
;; Doc URL: http://www.emacswiki.org/BrowseKillRing
;; Keywords: convenience
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `browse-kill-ring', `second-sel'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Extensions to `browse-kill-ring.el'.
;;
;;  Put this in your init file (~/.emacs):
;;
;;    (require 'browse-kill-ring+)
;;
;;
;;  Option `browse-kill-ring-alternative-ring' is an alternative
;;  selection ring to use, in addition to the `kill-ring'.  You can
;;  customize the value to any ring of strings you like.
;;
;;  `browse-kill-ring' lets you use either ring as the selection ring
;;  to browse and paste.  You can even use both rings, in different
;;  `browse-kill-ring' display buffers.  In such a buffer (in
;;  `browse-kill-ring-mode'), `o' pops to the list for the other ring.
;;
;;  If you have library `second-sel.el' in your `load-path'
;;  (recommended) it is loaded automatically when you load
;;  `browse-kill-ring+.el'.  In this case, by default
;;  `browse-kill-ring-alternative-ring' is the secondary selection
;;  ring.
;;
;;  You can customize the set of commands to be recognized as yank
;;  commands and alternative yank commands - see options
;;  `browse-kill-ring-yank-commands' and
;;  `browse-kill-ring-alternative-yank-commands'.  The alternative
;;  yank commands are commands that yank using a different selection
;;  ring, for example, the secondary yank commands defined by library
;;  `second-sel.el'.
;;
;;  Following a yank command or alternative yank command, `M-y' pops
;;  and yanks the appropriate type of selection.  A prefix arg N
;;  chooses the Nth previous selection in the ring.
;;
;;  Otherwise (not following a yank or alternative yank), `M-y'
;;  browses the current selection ring.  A prefix arg switches to the
;;  other selection ring.  If you are in a `browse-kill-ring' buffer,
;;  then `M-y' switches to the other ring even without a prefix arg.
;;
;;  If there is no alternative selection ring (e.g., you do not use
;;  library `second-sel.el'), then `M-y' either pops (following a
;;  yank) or browses (not following a yank) the `kill-ring'.
;;
;;  FWIW, I customize `browse-kill-ring-quit-action' to be
;;  `browse-kill-ring-quit-deletes-window/frame'.  This is similar to
;;  the default behavior, except that if the window is dedicated, then
;;  the frame is deleted.
;;
;;  Icicles offers an alternative: completion vs browsing.
;;
;;    You might want to use the Icicles (library `icicles.el') binding
;;    of `M-y' as an alternative to the `browse-kill-ring+.el'
;;    behavior of `M-y'.  If you do that you can of course still use
;;    `browse-kill-ring+.el' to browse the selection rings.  Just bind
;;    `browse-kill-ring'.
;;
;;    What Icicles offers is the ability to yank by completing against
;;    the selection rings, instead of browsing them.
;;
;;
;;  Commands defined here:
;;
;;    `browse-kill-ring-copy-to-other-ring',
;;    `browse-kill-ring-switch-to-other-kill-ring',
;;    `toggle-browse-kill-ring-display-style'.
;;
;;  User options defined here:
;;
;;    `browse-kill-ring-alternative-push-function',
;;    `browse-kill-ring-alternative-ring',
;;    `browse-kill-ring-alternative-yank-commands',
;;    `browse-kill-ring-yank-commands'.
;;
;;  Non-interactive functions defined here:
;;
;;    `browse-kill-ring-current-ring',
;;    `browse-kill-ring-quit-deletes-window/frame',
;;    `browse-kill-ring-remove-dups',
;;    `browse-kill-ring-target-overlay-at'.
;;
;;  Internal variables defined here:
;;
;;    `browse-kill-ring-current-ring', `browse-kill-ring-mode-map'.
;;
;;
;;  ***** NOTE: The following functions defined in `browse-kill-ring.el'
;;              have been REDEFINED HERE:
;;
;;    `browse-kill-ring', `browse-kill-ring-append-insert-and-move',
;;    `browse-kill-ring-current-string',
;;    `browse-kill-ring-default-keybindings',
;;    `browse-kill-ring-delete', `browse-kill-ring-do-append-insert',
;;    `browse-kill-ring-do-insert',
;;    `browse-kill-ring-insert-and-move',
;;    `browse-kill-ring-do-prepend-insert', `browse-kill-ring-edit',
;;    `browse-kill-ring-edit-finish', `browse-kill-ring-forward',
;;    `browse-kill-ring-prepend-insert-and-move',
;;    `browse-kill-ring-mode' `browse-kill-ring-setup'.
;;
;;
;;  ***** NOTE: The following functions defined in `second-sel.el'
;;              have been ADVISED HERE:
;;
;;    `add-secondary-to-ring'.
;;
;;  Key bindings defined here for `browse-kill-ring-mode-map':
;;
;;     `t'     - `toggle-browse-kill-ring-display-style'
;;     `TAB'   - `browse-kill-ring-forward'
;;     `S-TAB' - `browse-kill-ring-previous'
;;
;;  NOTE: This library automatically calls
;;  `browse-kill-ring-default-keybindings'.  If you do not want that,
;;  then comment out this call (at the end of the file).
;;
;;
;;  TO DO:
;;
;;  `browse-kill-ring-edit': membership of selection text is not
;;  sufficient, since there can be duplicates.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2012/02/08 dadams
;;     browse-kill-ring-remove-dups: Redefined to use a hash table.
;; 2012/01/15 dadams
;;     browse-kill-ring-mode: Call font-lock-refresh-defaults.
;; 2012/01/07 dadams
;;     Added: browse-kill-ring-copy-to-other-ring.  Bound to c in browser buffer.
;;     Added: browse-kill-ring-current-ring (function).
;;     Added autoload cookies.
;;     browse-kill-ring-delete: Removed extra progn and extra let.
;;     browse-kill-ring, *-delete, *-insert-and-move, *-mode, *-edit(-finish), *-setup:
;;       Use the function, not the var, browse-kill-ring-current-ring.
;; 2011/12/23 dadams
;;     browse-kill-ring-do-insert: Delete active region before inserting, if in delete-seletion-mode.
;; 2011/03/22 dadams
;;     Added: browse-kill-ring(-append|-prepend)-insert-and-move,
;;            browse-kill-ring-alternative-push-function.
;;     Replace advice of kill-new with advice of add-secondary-to-ring.
;;     browse-kill-ring-insert-and-move: Use browse-kill-ring-alternative-push-function.
;;     Soft-require second-sel.el.
;; 2011/03/20 dadams
;;     Added: browse-kill-ring-mode-map (defconst, so could move it out of the mode definition).
;;     Added: browse-kill-ring-target-overlay-at, browse-kill-ring-current-string,
;;            browse-kill-ring-do(-append|-prepend)-insert, browse-kill-ring-forward,
;;            browse-kill-ring-mode, browse-kill-ring-switch-to-other-kill-ring,
;;            browse-kill-ring-kill-number (commented out).
;;     browse-kill-ring-do-insert: Added optional arg, so can factor out common code.
;;       Use with-current-buffer. Use yank-excluded-properties.
;;       (Bug fix) Set window point after inserting.  This makes the inserted text be the region.
;;     browse-kill-ring-do-(append|prepend)-insert: Define using browse-kill-ring-do-insert.
;;     browse-kill-ring-current-string, browse-kill-ring-do-insert, browse-kill-ring-delete,
;;       browse-kill-ring-forward, browse-kill-ring-edit:
;;         Move to bol first, so can use it at eol.
;;     browse-kill-ring-delete, browse-kill-ring-forward, browse-kill-ring-edit:
;;       Use browse-kill-ring-target-overlay-at.
;;     browse-kill-ring-forward: Bug fixes.
;;     browse-kill-ring-mode: Derive from text mode.  Don't define keymap here.  Use the right ring.
;;     browse-kill-ring:
;;       Calling it in b-k-r-mode: Chooses the right ring instead of switching to the other ring.
;;                                 Uses browse-kill-ring-original-window, not selected window.
;;       Removed read-only message.  Changed buffer name: Selection Ring.
;;     Bindings: Bind o to browse-kill-ring-switch-to-other-kill-ring.
;;               Bind 1 to browse-kill-ring-insert-and-move.
;;               Removed bindings at top level - use defconst of browse-kill-ring-mode-map instead.
;;     toggle-browse-kill-ring-display-style: Call browse-kill-ring.
;; 2011/03/17 dadams
;;     browse-kill-ring-quit-deletes-window/frame:
;;       If dedicated window, pass BUF to bury-buffer, to avoid sole-window error.
;; 2009/06/25 dadams
;;     Added: browse-kill-ring-quit-deletes-window/frame.
;;     Added key bindings for TAB, S-TAB.
;;     browse-kill-ring:
;;       select-frame-set-input-focus, for MS Windows workaround.
;;       Don't show an empty buffer (for empty ring).
;; 2009/06/24 dadams
;;     Added: browse-kill-ring(-alternative)-yank-commands, browse-kill-ring-remove-dups,
;;            browse-kill-ring-default-keybindings (redefinition),
;;            browse-kill-ring (redefinition), browse-kill-ring-alternative-ring.
;;     browse-kill-ring-setup:
;;       Don't set browse-kill-ring-current-ring here.  Do it in browse-kill-ring.
;;       Use browse-kill-ring-remove-dups instead of requiring cl.el's delete-duplicates.
;; 2008/??/?? dadams
;;     Added: browse-kill-ring-current-ring, browse-kill-ring-delete,
;;            browse-kill-ring-edit(-finish), browse-kill-ring-setup.
;; 2008/??/?? dadams
;;     Created.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(eval-when-compile (require 'cl)) ;; case
(require 'browse-kill-ring)
(require 'second-sel nil t) ;; (no error if not found)
  ;; add-secondary-to-ring, secondary-selection-ring, secondary-selection-yank-commands,
  ;; secondary-selection-yank-secondary-commands

;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defcustom browse-kill-ring-yank-commands (if (boundp 'secondary-selection-yank-commands)
                                              secondary-selection-yank-commands
                                            '(yank icicle-yank-maybe-completing))
  "*Commands that yank.
Used by `yank-pop' to tell whether the previous command was a yank command.
Used only if `browse-kill-ring-default-keybindings' has been called,
so `yank-pop' is advised."
  :type '(repeat (restricted-sexp :tag "Command that yanks text"
                  :match-alternatives (symbolp commandp) :value ignore))
  :group 'browse-kill-ring :group 'killing)

;;;###autoload
(defcustom browse-kill-ring-alternative-yank-commands
  (and (boundp 'secondary-selection-yank-secondary-commands)
       secondary-selection-yank-secondary-commands)
  "*Commands that yank using the alternative selection ring.
Used by `browse-kill-ring-setup' to tell whether the previous command
yanked from `browse-kill-ring-alternative-ring'."
  :type '(repeat (restricted-sexp :match-alternatives (symbolp commandp) :value ignore))
  :group 'browse-kill-ring :group 'killing)

;;;###autoload
(defcustom browse-kill-ring-alternative-ring
  (and (boundp 'secondary-selection-ring) ; Defined in `second-sel.el'.
       'secondary-selection-ring)
  "*Selection ring to use as an alternative to `kill-ring'.
A value of nil means there is no alternative selection ring; that is,
`kill-ring' is used always."
  :type '(restricted-sexp :tag "Selection ring variable"
          :match-alternatives (symbolp boundp) :value ignore)
  :group 'browse-kill-ring :group 'killing)

;;;###autoload
(defcustom browse-kill-ring-alternative-push-function
  (and (boundp 'secondary-selection-ring) ; Defined in `second-sel.el'.
       'add-secondary-to-ring)
  "*Function that adds item to the front of alternative selection ring.
This is analogous to `kill-new' for the alternative ring.
It must accept the same same arguments as `kill-new'."
  :type 'function
  :group 'browse-kill-ring :group 'killing)

(defvar browse-kill-ring-current-ring 'kill-ring
  "Symbol whose value is the current selection ring for `browse-kill-ring'.")


;; These bindings are additional - not in `browse-kill-ring.el':
;;
;;   `1'     - `browse-kill-ring-insert-and-move'
;;   `t'     - `toggle-browse-kill-ring-display-style'
;;   `TAB'   - `browse-kill-ring-forward'
;;   `S-TAB' - `browse-kill-ring-previous'
;;
;; This binding is a difference from `browse-kill-ring.el':
;;
;;   `o'     - `browse-kill-ring-switch-to-other-kill-ring' instead of
;;             `browse-kill-ring-insert-and-move'
;;
(defconst browse-kill-ring-mode-map
  (let ((map  (make-sparse-keymap)))
    (define-key map (kbd "<tab>")   'browse-kill-ring-forward)
    (define-key map [(control ?i)]  'browse-kill-ring-forward)
    (define-key map (kbd "<S-tab>") 'browse-kill-ring-previous)
    (define-key map (kbd "RET")     'browse-kill-ring-insert-and-quit)
    (define-key map [(mouse-2)]     'browse-kill-ring-mouse-insert)
    (define-key map (kbd "?")       'describe-mode)
    (define-key map (kbd "1")       'browse-kill-ring-insert-and-move)
    (define-key map (kbd "a")       'browse-kill-ring-append-insert)
    (define-key map (kbd "b")       'browse-kill-ring-prepend-insert)
    (define-key map (kbd "c")       'browse-kill-ring-copy-to-other-ring)
    (define-key map (kbd "d")       'browse-kill-ring-delete)
    (define-key map (kbd "e")       'browse-kill-ring-edit)
    (define-key map (kbd "g")       'browse-kill-ring-update)
    (define-key map (kbd "h")       'describe-mode)
    (define-key map (kbd "i")       'browse-kill-ring-insert)
    (define-key map (kbd "l")       'browse-kill-ring-occur)
    (define-key map (kbd "n")       'browse-kill-ring-forward)
    (define-key map (kbd "o")       'browse-kill-ring-switch-to-other-kill-ring)
    (define-key map (kbd "p")       'browse-kill-ring-previous)
    (define-key map (kbd "q")       'browse-kill-ring-quit)
    (define-key map (kbd "r")       'browse-kill-ring-search-backward)
    (define-key map (kbd "s")       'browse-kill-ring-search-forward)
    (define-key map (kbd "t")       'toggle-browse-kill-ring-display-style)
    (define-key map (kbd "u")       'browse-kill-ring-insert-move-and-quit)
    (define-key map (kbd "U")       'browse-kill-ring-undo-other-window)
    (define-key map (kbd "x")       'browse-kill-ring-insert-and-delete)
    (define-key map (kbd "y")       'browse-kill-ring-insert)
    map)
  "Keymap for `browse-kill-ring-mode'.")

(defun browse-kill-ring-current-ring ()
  "Current selection ring (the symbol whose value is the ring).
When in a selection-ring buffer, update variable
`browse-kill-ring-current-ring'.  Return its value, in any case.
Use this instead of the variable, because the user might have switched
to a window showing the buffer for the other ring."
  (if (not (eq major-mode 'browse-kill-ring-mode))
      browse-kill-ring-current-ring
    (setq browse-kill-ring-current-ring ; Use the correct ring for this `browse-kill-ring' buffer.
          (if (or (not browse-kill-ring-alternative-ring)
                  (string= (buffer-name) "*Selection Ring: `kill-ring'*"))
              'kill-ring
            browse-kill-ring-alternative-ring))))


(when (and (fboundp 'cl-puthash) (not (fboundp 'puthash))) ; Emacs 20 with `cl-extra.el' loaded.
  (defalias 'puthash 'cl-puthash))

(if (fboundp 'puthash)                  ; Emacs 21+, or Emacs 20 with `cl-extra.el' loaded.
    (defun browse-kill-ring-remove-dups (sequence &optional test)
      "Copy of SEQUENCE with duplicate elements removed.
Optional arg TEST is the test function.  If nil, test with `equal'.
See `make-hash-table' for possible values of TEST."
      (setq test  (or test #'equal))
      (let ((htable  (make-hash-table :test test)))
        (loop for elt in sequence
              unless (gethash elt htable)
              do     (puthash elt elt htable)
              finally return (loop for i being the hash-values in htable collect i))))

  (defun browse-kill-ring-remove-dups (list &optional use-eq)
    "Copy of LIST with duplicate elements removed.
Test using `equal' by default, or `eq' if optional USE-EQ is non-nil."
    (let ((tail  list)
          new)
      (while tail
        (unless (if use-eq (memq (car tail) new) (member (car tail) new))
          (push (car tail) new))
        (pop tail))
      (nreverse new))))


;; ADVISES ORIGINAL in `second-sel.el'.
;;
(when (fboundp 'add-secondary-to-ring)
  (defadvice add-secondary-to-ring (around bkr-no-second-sel-new-dups)
    "Advice for not adding duplicate elements to the secondary selection ring.
Even after being \"activated\", this advice will modify the behavior
of `add-secondary-to-ring' only if `browse-kill-ring-no-duplicates' is
non-nil."
    (when browse-kill-ring-no-duplicates
      (setq add-secondary-to-ring  (delete (ad-get-arg 0) add-secondary-to-ring)))
    ad-do-it))

(defun browse-kill-ring-target-overlay-at (position)
  "Return overlay at POSITION that has property `browse-kill-ring-target'.
If no such overlay, raise an error."
  (let ((ovs  (overlays-at (point))))
    (catch 'browse-kill-ring-target-overlay-at
      (dolist (ov  ovs)
        (when (overlay-get ov 'browse-kill-ring-target)
          (throw 'browse-kill-ring-target-overlay-at ov)))
      (error "No selection-ring item here"))))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Use `browse-kill-ring-current-ring', not `kill-ring'.
;; 2. Move to bol first, so can use this at eol (after the selection's overlay).
;;
;;;###autoload
(defun browse-kill-ring-delete ()       ; Bound to `d' in selection-ring buffer.
  "Remove all occurrences of selection at point from current selection ring."
  (interactive)
  (forward-line 0)
  (unwind-protect
       (let* ((ov      (browse-kill-ring-target-overlay-at (point)))
              (target  (overlay-get ov 'browse-kill-ring-target)))
         (setq buffer-read-only  nil)
         (delete-region (overlay-start ov) (1+ (overlay-end ov)))
         (set browse-kill-ring-current-ring
              (delete target (symbol-value (browse-kill-ring-current-ring))))
         (when (get-text-property (point) 'browse-kill-ring-extra)
           (let ((prev  (previous-single-property-change (point) 'browse-kill-ring-extra))
                 (next  (next-single-property-change (point) 'browse-kill-ring-extra)))
             (when prev (incf prev))
             (when next (incf next))
             (delete-region (or prev (point-min)) (or next (point-max))))))
    (setq buffer-read-only  t))
  (browse-kill-ring-resize-window)
  (browse-kill-ring-forward 0))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Move to bol first, so can use this at eol (after the selection's overlay).
(defun browse-kill-ring-current-string (buffer position)
  "Selection entry in BUFFER that is nearest POSITION."
  (with-current-buffer buffer
    (save-excursion
      (goto-char position)
      ;; The overlay is at bol but not at eol.  This ensures we can get the string from eol.
      (forward-line 0)
      (overlay-get (browse-kill-ring-target-overlay-at (point)) 'browse-kill-ring-target))))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Put error test first.
;; 2. Added optional arg APPEND/PREPEND, to factor out common code.
;; 3. Move to bol first, so can use this at eol (after the selection's overlay).
;; 4. Just use `with-current-buffer'.  No need for explicit `unwind-protect' etc.
;; 5. Let `yank-excluded-properties' reflect `browse-kill-ring-depropertize'.  Emacs 22+.
;; 6. Delete active region before inserting, if in `delete-seletion-mode'.
;; 7. (Bug fix) Set window point after inserting.
;;
(defun browse-kill-ring-do-insert (bkr-buf sel-pos &optional append/prepend)
  "Insert the selection that is at position SEL-POS in buffer BKR-BUF.
BKR-BUF is a selection-ring buffer, with a list of selections.
Insert the selection at point unless optional arg APPEND/PREPEND is:
 `append'  - insert at eob, not at point
 `prepend' - insert at bob, not at point"
  (unless (window-live-p browse-kill-ring-original-window)
    (error "Window `%s' was deleted.  Use `browse-kill-ring' again"
           browse-kill-ring-original-window))
;;;   ;; Move to bol first, so can use this at eol (after the overlay).
;;;   (forward-line 0)
  (let ((sel-string  (browse-kill-ring-current-string bkr-buf sel-pos)))
    (with-current-buffer (window-buffer browse-kill-ring-original-window)
      (save-excursion
        (let ((yank-excluded-properties  (and browse-kill-ring-depropertize t))
              (insert-pos                (case append/prepend
                                           (append   (point-max))
                                           (prepend  (point-min))
                                           (t        (point)))))
          (goto-char insert-pos)
          (when (and delete-selection-mode (not buffer-read-only) transient-mark-mode mark-active
                     (not (memq append/prepend '(append prepend))))
            (delete-active-region))
          (insert (if browse-kill-ring-depropertize
                      (browse-kill-ring-depropertize-string sel-string)
                    sel-string))
          ;; Put point after insertion (mark is before insertion).
          (set-window-point browse-kill-ring-original-window (point))
          (when browse-kill-ring-highlight-inserted-item
            (let ((ov  (make-overlay insert-pos (point))))
              (overlay-put ov 'face 'highlight)
              (sit-for 0.5)
              (delete-overlay ov))))))))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Use new `browse-kill-ring-do-insert'.
;;
(defun browse-kill-ring-do-prepend-insert (bkr-buf sel-pos)
  "`browse-kill-ring-do-insert', with insertion at bob."
  (browse-kill-ring-do-insert bkr-buf sel-pos 'prepend))
  

;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Use new `browse-kill-ring-do-insert'.
;;
(defun browse-kill-ring-do-append-insert (bkr-buf sel-pos)
  "`browse-kill-ring-do-insert', with insertion at eob."
  (browse-kill-ring-do-insert bkr-buf sel-pos 'append))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Added optional arg APPEND/PREPEND, to factor out common code.
;; 2. Use `browse-kill-ring-current-ring', not `kill-ring'.
;; 3. Use `browse-kill-ring-alternative-push-function' for alternative ring.
;;
;;;###autoload
(defun browse-kill-ring-insert-and-move (&optional quit append/prepend)
                                        ; Bound to `1' in selection-ring buffer.
  "Like `browse-kill-ring-insert', but move selection to front of ring.
Insert the selection at point unless optional arg
APPEND/PREPEND is:
 `append'  - insert at eob, not at point
 `prepend' - insert at bob, not at point"
  (interactive "P")
  (let* ((bkr-buf  (current-buffer))
         (sel-pos  (point))
         (str      (browse-kill-ring-current-string bkr-buf sel-pos)))
    (browse-kill-ring-do-insert bkr-buf sel-pos append/prepend)
    (browse-kill-ring-delete)
    (if (eq 'kill-ring (browse-kill-ring-current-ring))
        (kill-new str)
      (funcall browse-kill-ring-alternative-push-function str)))
  (if quit (browse-kill-ring-quit) (browse-kill-ring-update)))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Use new `browse-kill-ring-do-insert-and-move'.
;;
;;;###autoload
(defun browse-kill-ring-prepend-insert-and-move (&optional quit) ; Not bound.
  "`browse-kill-ring-prepend-insert', but move selection to front of ring."
  (interactive "P")
  (browse-kill-ring-insert-and-move quit 'prepend))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Use new `browse-kill-ring-do-insert-and-move'.
;;
;;;###autoload
(defun browse-kill-ring-append-insert-and-move (&optional quit) ; Not bound.
  "`browse-kill-ring-append-insert', but move selection to front of ring."
  (interactive "P")
  (browse-kill-ring-insert-and-move quit 'append))
  

;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Move to bol first, so can use this at eol (after the selection's overlay).
;; 2. Bug fixes.
;; 
;;;###autoload
(defun browse-kill-ring-forward (&optional arg) ; Bound to `TAB', `n' in selection-ring buffer.
  "Move forward by ARG selection-ring entries."
  (interactive "p")
  (forward-line 0)
  (while (not (zerop arg))
    (if (< arg 0)
	(progn (incf arg)
               (if (overlays-at (point))
                   (progn
                     (goto-char (overlay-start (browse-kill-ring-target-overlay-at (point))))
                     (goto-char (previous-overlay-change (point)))
                     (goto-char (previous-overlay-change (point))))
                 (goto-char (previous-overlay-change (point)))
                 (goto-char (previous-overlay-change (point)))
                 (when (and (overlays-at (point)) (not (bobp)))
                   (goto-char (overlay-start (browse-kill-ring-target-overlay-at (point))))))
               (forward-line 0))
      (decf arg)
      (if (overlays-at (point))
          (progn (goto-char (overlay-end (browse-kill-ring-target-overlay-at (point))))
                 (goto-char (next-overlay-change (point)))
                 ;; Don't let, for example, overlay from `show-paren-mode' interfere here.
                 (while (not (bolp)) (goto-char (next-overlay-change (point)))))
        (goto-char (next-overlay-change (point)))
        (unless (eobp) (goto-char (overlay-start (browse-kill-ring-target-overlay-at (point))))))))
  (when (and browse-kill-ring-highlight-current-entry  (overlays-at (point)))
    (let ((ovs         (overlay-lists))
	  (current-ov  (browse-kill-ring-target-overlay-at (point))))
      (mapcar #'(lambda (ov) (overlay-put ov 'face nil)) (nconc (car ovs) (cdr ovs)))
      (overlay-put current-ov 'face 'highlight)))
  (when browse-kill-ring-recenter (recenter 1)))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Derive from Text Mode, so typical movement keys, search keys, etc. work as expected.
;; 2. Don't define the keymap here, just use it.
;; 3. Use the appropriate ring for this `browse-kill-ring' buffer.  Update
;;    `browse-kill-ring-current-ring'.
;;
(define-derived-mode browse-kill-ring-mode text-mode
    "Selection-Ring"
  "Major mode for browsing selection rings such as the `kill-ring'.
Do not call `browse-kill-ring-mode' directly - use `browse-kill-ring'.

\\{browse-kill-ring-mode-map}"
  (set (make-local-variable 'font-lock-defaults)
       '(nil t nil nil nil (font-lock-fontify-region-function . browse-kill-ring-fontify-region)))
  (when (fboundp 'font-lock-refresh-defaults) (font-lock-refresh-defaults))
  (use-local-map browse-kill-ring-mode-map)
  (browse-kill-ring-current-ring))      ; Use the correct ring for this `browse-kill-ring' buffer.


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Use `browse-kill-ring-yank-commands', not necessarily `yank'.
;;
;;;###autoload
(defun browse-kill-ring-default-keybindings () ; Not bound.
  "Set up `M-y' so that it can invoke `browse-kill-ring'.
See also option `browse-kill-ring-yank-commands'."
  (interactive)
  (defadvice yank-pop (around kill-ring-browse-maybe (arg))
    "If last action was not a yank, run `browse-kill-ring' instead."
    ;; `yank-pop' has (interactive "*p"), which does not allow it to run in a read-only buffer.
    ;; `browse-kill-ring' needs to work in read-only buffers also, so we change the
    ;; interactive form here.  But we `barf-if-buffer-read-only' when invoking original `yank-pop'.
    (interactive "p")
    (if (not (memq last-command browse-kill-ring-yank-commands))
	(call-interactively #'browse-kill-ring)
      (barf-if-buffer-read-only)
      ad-do-it))
  (ad-activate 'yank-pop))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Move to bol first, so can use this at eol (after the selection's overlay).
;; 2. Use `browse-kill-ring-current-ring', not `kill-ring'.
;;
;;;###autoload
(defun browse-kill-ring-edit ()         ; Bound to `e' in selection-ring buffer.
  "Edit the current selection ring entry at point."
  (interactive)
  (forward-line 0)
  (let ((ovs  (overlays-at (point))))
    ;; $$$$$$ FIXME - membership of the text is not a sufficient test, to get the correct cell.
    (let* ((target       (overlay-get (browse-kill-ring-target-overlay-at (point))
                                      'browse-kill-ring-target))
	   (target-cell  (member target (symbol-value (browse-kill-ring-current-ring)))))
      (unless target-cell (error "Item deleted from the current selection ring"))
      (switch-to-buffer (get-buffer-create "*Kill Ring Edit*"))
      (setq buffer-read-only  nil)
      (erase-buffer)
      (insert target)
      (goto-char (point-min))
      (browse-kill-ring-resize-window)
      (browse-kill-ring-edit-mode)
      (message (substitute-command-keys "Use `\\[browse-kill-ring-edit-finish]' to finish editing."))
      (setq browse-kill-ring-edit-target  target-cell))))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; Use `browse-kill-ring-current-ring', not `kill-ring'.
;;
;;;###autoload
(defun browse-kill-ring-edit-finish ()  ; Bound to `C-c C-c' in `browse-kill-ring-edit-mode-map'
  "Commit the changes to the current selection ring."
  (interactive)
  (if browse-kill-ring-edit-target
      (setcar browse-kill-ring-edit-target (buffer-string))
    (when (y-or-n-p "The item has been deleted; add to front? ")
      (push (buffer-string) (symbol-value (browse-kill-ring-current-ring)))))
  (bury-buffer)
  (when (eq major-mode 'browse-kill-ring-mode) ; The user might have rearranged the windows
    (browse-kill-ring-setup (current-buffer) browse-kill-ring-original-window nil
			    browse-kill-ring-original-window-config)
    (browse-kill-ring-resize-window)))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Use `browse-kill-ring-current-ring', not `kill-ring'.
;; 2. Don't require `cl.el' - use local function `browse-kill-ring-remove-dups'.
;;
(defun browse-kill-ring-setup (bkr-buf window &optional regexp window-config)
  "Set up buffer BKR-BUF as the selection-ring display buffer.
Turn on `browse-kill-ring-mode'.
Record `browse-kill-ring-original-window' and
 `browse-kill-ring-original-window-config'.
Fill buffer with items from current selection ring, respecting REGEXP, 
 `browse-kill-ring-display-duplicates', and
 `browse-kill-ring-display-style'."
  (with-current-buffer bkr-buf
    (unwind-protect
         (progn
           (browse-kill-ring-mode)
           (setq buffer-read-only  nil)
           (when (eq browse-kill-ring-display-style 'one-line) (setq truncate-lines  t))
           (let ((inhibit-read-only  t))  (erase-buffer))
           (setq browse-kill-ring-original-window         window
                 browse-kill-ring-original-window-config  (or window-config
                                                              (current-window-configuration)))
           (let ((items  (mapcar (if browse-kill-ring-depropertize
                                     #'browse-kill-ring-depropertize-string
                                   #'copy-sequence)
                                 (symbol-value (browse-kill-ring-current-ring))))
                 (browse-kill-ring-maximum-display-length
                  (if (and browse-kill-ring-maximum-display-length
                           (<= browse-kill-ring-maximum-display-length 3))
                      4
                    browse-kill-ring-maximum-display-length)))
             (unless browse-kill-ring-display-duplicates
               (setq items  (browse-kill-ring-remove-dups items)))
             (when (stringp regexp)
               (setq items  (delq nil (mapcar #'(lambda (item) (and (string-match regexp item) item))
                                              items))))
             (funcall (or (cdr (assq browse-kill-ring-display-style browse-kill-ring-display-styles))
                          (error "Invalid `browse-kill-ring-display-style': %s"
                                 browse-kill-ring-display-style))
                      items)
             (message (let* ((len    (length (symbol-value browse-kill-ring-current-ring)))
                             (entry  (if (= 1 len) "entry" "entries")))
                        (concat
                         (if (and (not regexp) browse-kill-ring-display-duplicates)
                             (format "%s %s in `%s'" len entry browse-kill-ring-current-ring)
                           (format "%s (of %s) %s in `%s' shown" (length items) len entry
                                   browse-kill-ring-current-ring))
                         (substitute-command-keys "    Use `\\[browse-kill-ring-quit]' to quit, \
`\\[describe-mode]' for help"))))
             (set-buffer-modified-p nil)
             (goto-char (point-min))
             (browse-kill-ring-forward 0)
             (when regexp (setq mode-name  (concat "Selection-Ring [" regexp "]")))
             (run-hooks 'browse-kill-ring-hook)
             (when (and (featurep 'xemacs) font-lock-mode)
               (browse-kill-ring-fontify-region (point-min) (point-max)))))
      (setq buffer-read-only  t))))


;; REPLACES ORIGINAL in `browse-kill-ring.el'.
;;
;; 1. Added prefix arg.
;; 2. Added current ring name to name of buffer: *Selection Ring: `<NAME>'*.
;; 3. Choose right ring if buffer already in `browse-kill-ring-mode'.
;; 4. Use `browse-kill-ring-original-window' if already in `browse-kill-ring-mode'.
;; 5. Removed unused `let' binding of `orig-buf'.
;; 6. Message if ring is empty.
;; 7. Updated doc string to mention `browse-kill-ring-alternative-ring'.
;;
;;;###autoload
(defun browse-kill-ring (&optional other-ring-p)
  "Browse the current selection ring.
With a prefix arg, browse the alternative selection ring instead.

\(If `browse-kill-ring-alternative-ring' is nil, then a prefix arg has
no effect.)"
  (interactive "P")
  (browse-kill-ring-current-ring)       ; If a selection-ring buffer, use its ring by default.
  ;; Respect prefix arg to change to other ring, if there is one.
  (when (and other-ring-p  browse-kill-ring-alternative-ring)
    (setq browse-kill-ring-current-ring  (if (eq browse-kill-ring-current-ring 'kill-ring)
                                             browse-kill-ring-alternative-ring
                                           'kill-ring)))
  (let ((bkr-buf  (get-buffer-create (format "*Selection Ring: `%s'*"
                                             browse-kill-ring-current-ring))))
    ;; $$$$$$ Should I do something special if only one selection in ring?
    (unless (symbol-value browse-kill-ring-current-ring)
      (message "`%s' is empty" browse-kill-ring-current-ring))
    (browse-kill-ring-setup bkr-buf (if (eq major-mode 'browse-kill-ring-mode)
                                        browse-kill-ring-original-window ; Keep same dest window.
                                      (selected-window)))
    (pop-to-buffer bkr-buf)
    (select-frame-set-input-focus (window-frame (selected-window))) ; MS Windows workaround
    (browse-kill-ring-resize-window))
  nil)

;;;###autoload
(defun browse-kill-ring-switch-to-other-kill-ring () ; Bound to `o' in selection-ring buffer.
  "Browse the other selection ring.
If the current ring is `kill-ring' then browse the alternative ring
\(e.g. `secondary-selection-ring'), and vice versa.  The alternative
ring is the value of `browse-kill-ring-alternative-ring'."
  (interactive)
  (unless browse-kill-ring-alternative-ring  (error "No alternative selection ring"))
  (browse-kill-ring 'OTHER))

(defun browse-kill-ring-quit-deletes-window/frame ()
  "Bury buffer.  Delete window or, if dedicated, frame.
Useful as customized value of `browse-kill-ring-quit-action'."
  (let ((buf            (current-buffer))
        (sole-window-p  (eq (selected-window) (frame-root-window))))
    (cond ((and sole-window-p (window-dedicated-p (selected-window)))
           (delete-frame)
           (bury-buffer buf))
          (t
           (unless sole-window-p (delete-window))
           ;; Avoid BUF as explicit arg to `bury-buffer', since we want to undisplay it.
           (with-current-buffer buf (bury-buffer))))))

;;;###autoload
(defun toggle-browse-kill-ring-display-style () ; Bound to `t' in selection-ring buffer.
  "Toggle browse-kill-ring-display-style between `separated' and `one-line'."
  (interactive)
  (setq browse-kill-ring-display-style  (case browse-kill-ring-display-style
                                          (separated 'one-line)
                                          (otherwise 'separated)))
  (browse-kill-ring)
  (browse-kill-ring-update)
  (message "Display style is now %s" (upcase (symbol-name browse-kill-ring-display-style))))


;;;###autoload
(defun browse-kill-ring-copy-to-other-ring (&optional movep) ; Bound to `c' in selection-ring buffer.
  "Copy the selection at point from current selection ring to other ring.
With a prefix arg, move it instead of copying it.
If the other ring is also displayed, then its displayed is updated."
  (interactive "P")
  (forward-line 0)
  (unwind-protect
       (let* ((ov    (browse-kill-ring-target-overlay-at (point)))
              (seln  (overlay-get ov 'browse-kill-ring-target)))
         (setq buffer-read-only  nil)
         (when browse-kill-ring-depropertize
           (setq seln  (browse-kill-ring-depropertize-string seln)))
         ;; Add selection to the front of the other ring.
         (if (eq 'kill-ring (browse-kill-ring-current-ring))
             (funcall browse-kill-ring-alternative-push-function seln)
           (kill-new seln))
         (when movep                    ; Delete selection from this ring.
           (delete-region (overlay-start ov) (1+ (overlay-end ov)))
           (set browse-kill-ring-current-ring
                (delete seln (symbol-value browse-kill-ring-current-ring)))
           (when (get-text-property (point) 'browse-kill-ring-extra)
             (let ((prev  (previous-single-property-change (point) 'browse-kill-ring-extra))
                   (next  (next-single-property-change (point) 'browse-kill-ring-extra)))
               (when prev (incf prev))
               (when next (incf next))
               (delete-region (or prev (point-min)) (or next (point-max)))))))
    (setq buffer-read-only  t))
  (browse-kill-ring-resize-window)
  (browse-kill-ring-forward 0)
  (let* ((other-ring  (if (eq browse-kill-ring-current-ring 'kill-ring)
                          browse-kill-ring-alternative-ring
                        'kill-ring))
         (other-buf   (and other-ring  (format "*Selection Ring: `%s'*" other-ring))))
    (when (and other-buf  (get-buffer-window other-buf 0))
      (with-current-buffer other-buf  (browse-kill-ring-update)))))

;;; ----------------------------------------------------
;;;
;;; Currently not used for anything.
;;; (defun browse-kill-ring-kill-number (pos)
;;;   "Return the selection-ring index to use for this selection."
;;;   (save-excursion
;;;     (goto-char pos)
;;;     (if (= (point-min) (previous-overlay-change (point)))
;;;         0
;;;       (let ((count  1))
;;;         (while (and (condition-case nil (progn (browse-kill-ring-forward -1) t) (error nil))
;;;                     (not (bobp)))
;;;           (setq count  (1+ count)))
;;;         count))))


;;; Key Bindings

(browse-kill-ring-default-keybindings)

;;;;;;;;;;;;;;;;;;;;;

(provide 'browse-kill-ring+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; browse-kill-ring+.el ends here
