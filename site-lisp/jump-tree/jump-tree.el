;;; jump-tree.el --- Treat position history as a tree  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Free Software Foundation, Inc

;; Author: Wen Yang <yangwen0228@foxmail.com>
;; Maintainer: Wen Yang <yangwen0228@foxmail.com>
;; Package-Version: 20170803.1
;; URL: https://github.com/yangwen0228/jump-tree
;; Keywords: convenience, position, jump, tree

;; This file is NOT part of GNU Emacs.

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
;;
;; Emacs has a powerful position system.  Unlike the standard
;; jump-prev/jump-next system in most software, it allows you to jump to the
;; position of anywhere you have gone.
;;
;; Standard jump-prev/jump-next treat position history as a linear sequence
;; of jump, that may lead to loss of position.
;;
;; This's not.  The `jump-tree-mode' provided by this package provide a
;; system that treats position history as what it is: a branching tree of
;; positions.  This simple idea allows the more intuitive behaviour of the
;; standard jump-prev/jump-next system to be combined with the power of
;; never losing any history.
;;
;; This package is inspired by and a combination of undo-tree and jumplist,
;; and copy a lot of codes from them.  ^_^
;;
;; Installation
;; ============
;;
;; This package has only been tested with Emacs versions 25.  It should
;; work in Emacs earlier versions, but not tested.
;;
;; To install `jump-tree-mode', make sure this file is saved in a directory in
;; your `load-path', and add the line:
;;
;;   (require 'jump-tree)
;;
;; to your .emacs file.  Byte-compiling jump-tree.el is recommended (e.g. using
;; "M-x byte-compile-file" from within Emacs).
;;
;; If you want to enable it globally, you can add:
;;
;;   (global-jump-tree-mode)
;;
;; to your .emacs file.
;;
;;
;; Quick-Start
;; ===========
;;
;; If you're the kind of person who likes to jump in the car and drive,
;; without bothering to first figure out whether the button on the left dips
;; the headlights or operates the ejector seat (after all, you'll soon figure
;; it out when you push it), then here's the minimum you need to know:
;;
;; Support several kinds of skipping methods. The priority is higher than that of recording:
;; 1. skip command in `jump-tree-pos-list-skip-commands`.
;; 2. skip when buffer in `jump-tree-pos-list-skip-buffers`.
;; 3. skip the commands whose prefix is "jump-tree".
;;
;; Support several kinds of recording methods. The priorities are:
;; 1. record when command in `jump-tree-pos-list-record-commands`.
;; 2. record when offset exceeding threshold.
;; 3. record when switch-buffer.
;;
;; The default `jump-tree-pos-list-skip-commands` value is as follows:
;; ```
;; '(self-insert-command)
;; ```
;;
;; The default `jump-tree-pos-list-skip-buffers` value is as follows(this may be changed to use regexp in the future.):
;; ```
;; '(*Messages*)'
;; ```
;;
;; The record of the jump node is decided by the `jump-tree-pos-list-record-commands` variable. The default value is as follows:
;; ```
;; '(beginning-of-buffer
;;   end-of-buffer backward-up-list
;;   beginning-of-defun end-of-defun
;;   unimacs-move-beginning-of-line unimacs-move-end-of-line
;;   unimacs-move-beginning-of-window unimacs-move-end-of-window
;;   helm-swoop helm-imenu helm-find-files helm-multi-files
;;   helm-projectile-switch-project helm-projectile-find-file
;;   helm-gtags-find-pattern helm-gtags-find-tag-adapter
;;   helm-gtags-find-rtag-adapter helm-ag-select-directory
;;   find-function find-variable
;;   mark-defun mark-whole-buffer
;;   avy-goto-char avy-goto-char-2
;;   ensime-edit-definition
;;   ensime-edit-definition-with-fallback
;;   isearch-forward)
;; ```
;;
;; We can support the record the position, when the movement or offset is exceeding the threshold. The default threshold points `jump-tree-pos-list-offset-threshold` is:
;; ```
;; 200
;; ```
;;
;; Besides, we support to record the position when switch to another buffer or file. Whether this feature is enabled is determined by `jump-tree-pos-list-switch-buffer`. The default value is enabled:
;; ```
;; t
;; ```

;; `jump-tree-mode' and `global-jump-tree-mode'
;;   Enable jump-tree mode (either in the current buffer or globally).
;;
;; M-, (`jump-tree-jump-prev')
;;   Jump-Prev positions.
;;
;; C-? (`jump-tree-jump-next')
;;   Jump-Next positions.
;;
;; `jump-tree-switch-branch'
;;   Switch jump-tree branch.
;;   (What does this mean? Better press the button and see!)
;;
;; C-x j  (`jump-tree-visualize')
;;   Visualize the position tree.
;;   (Better try pressing this button too!)
;;
;; C-x r u  (`jump-tree-save-state-to-register')
;;   Save current buffer state to register.
;;
;; C-x r U  (`jump-tree-restore-state-from-register')
;;   Restore buffer state from register.
;;
;;
;;
;; In the jump-tree visualizer:
;;
;; <up>  p  C-p  (`jump-tree-visualize-jump-prev')
;;   Jump-Prev positions.
;;
;; <down>  n  C-n  (`jump-tree-visualize-jump-next')
;;   Jump-Next positions.
;;
;; <left>  b  C-b  (`jump-tree-visualize-switch-branch-left')
;;   Switch to previous jump-tree branch.
;;
;; <right>  f  C-f  (`jump-tree-visualize-switch-branch-right')
;;   Switch to next jump-tree branch.
;;
;; C-<up>  M-{  (`jump-tree-visualize-jump-prev-to-x')
;;   Jump-Prev changes up to last branch point.
;;
;; <down>  n  C-n  (`jump-tree-visualize-jump-next')
;;   Jump-Next positions.
;;
;; <mouse-1>  (`jump-tree-visualizer-mouse-set')
;;   Set state to node at mouse click.
;;
;; t  (`jump-tree-visualizer-toggle-timestamps')
;;   Toggle display of time-stamps.
;;
;; d  (`jump-tree-visualizer-toggle-diff')
;;   Toggle diff display.
;;
;; s  (`jump-tree-visualizer-selection-mode')
;;   Toggle keyboard selection mode.
;;
;; q  (`jump-tree-visualizer-quit')
;;   Quit jump-tree-visualizer.
;;
;; C-q  (`jump-tree-visualizer-abort')
;;   Abort jump-tree-visualizer.
;;
;; ,  <
;;   Scroll left.
;;
;; .  >
;;   Scroll right.
;;
;; <pgup>  M-v
;;   Scroll up.
;;
;; <pgdown>  C-v
;;   Scroll down.
;;
;;
;;
;; In visualizer selection mode:
;;
;; <up>  p  C-p  (`jump-tree-visualizer-select-previous')
;;   Select previous node.
;;
;; <down>  n  C-n  (`jump-tree-visualizer-select-next')
;;   Select next node.
;;
;; <left>  b  C-b  (`jump-tree-visualizer-select-left')
;;   Select left sibling node.
;;
;; <right>  f  C-f  (`jump-tree-visualizer-select-right')
;;   Select right sibling node.
;;
;; <pgup>  M-v
;;   Select node 10 above.
;;
;; <pgdown>  C-v
;;   Select node 10 below.
;;
;; <enter>  (`jump-tree-visualizer-set')
;;   Set state to selected node and exit selection mode.
;;
;; s  (`jump-tree-visualizer-mode')
;;   Exit selection mode.
;;
;; t  (`jump-tree-visualizer-toggle-timestamps')
;;   Toggle display of time-stamps.
;;
;; q  (`jump-tree-visualizer-quit')
;;   Quit jump-tree-visualizer.
;;
;; C-q  (`jump-tree-visualizer-abort')
;;   Abort jump-tree-visualizer.
;;
;; ,  <
;;   Scroll left.
;;
;; .  >
;;   Scroll right.
;;
;;
;;
;; Persistent position history:
;;
;; Note: Requires Emacs version 24.3 or higher.
;;
;; Jump-Prev Systems
;; ============
;;
;; To understand the different position systems, it's easiest to consider an
;; example.  Imagine you make a few edits in a buffer.  As you edit, you
;; accumulate a history of changes, which we might visualize as a string of
;; past buffer states, growing downwards:
;;
;;                                o  (initial buffer state)
;;                                |
;;                                |
;;                                o  (first edit)
;;                                |
;;                                |
;;                                o  (second edit)
;;                                |
;;                                |
;;                                x  (current buffer state)
;;
;;
;; Now imagine that you position the last two positions.  We can visualize
;; this as rewinding the current state back two steps:
;;
;;                                o  (initial buffer state)
;;                                |
;;                                |
;;                                x  (current buffer state)
;;                                |
;;                                |
;;                                o
;;                                |
;;                                |
;;                                o
;;
;;
;; However, this isn't a good representation of what Emacs' position system
;; does.  Instead, it treats the jump-prevs as *new* changes to the buffer,
;; and adds them to the history:
;;
;;                                o  (initial buffer state)
;;                                |
;;                                |
;;                                o  (first edit)
;;                                |
;;                                |
;;                                o  (second edit)
;;                                |
;;                                |
;;                                x  (buffer state before position)
;;                                |
;;                                |
;;                                o  (first position)
;;                                |
;;                                |
;;                                x  (second position)
;;
;;
;; Actually, since the buffer returns to a previous state after an position,
;; perhaps a better way to visualize it is to imagine the string of changes
;; turning back on itself:
;;
;;        (initial buffer state)  o
;;                                |
;;                                |
;;                  (first edit)  o  x  (second position)
;;                                |  |
;;                                |  |
;;                 (second edit)  o  o  (first position)
;;                                | /
;;                                |/
;;                                o  (buffer state before position)
;;
;; Treating jump-prevs as new changes might seem a strange thing to do.  But
;; the advantage becomes clear as soon as we imagine what happens when you
;; edit the buffer again.  Since you've jump-prevne a couple of changes, new
;; edits will branch off from the buffer state that you've rewound to.
;; Conceptually, it looks like this:
;;
;;                                o  (initial buffer state)
;;                                |
;;                                |
;;                                o
;;                                |\
;;                                | \
;;                                o  x  (new edit)
;;                                |
;;                                |
;;                                o
;;
;; The standard jump-prev/jump-next system only lets you go backwards and
;; forwards linearly.  So as soon as you make that new edit, it discards the
;; old branch.  Emacs' position just keeps adding changes to the end of the
;; string.  So the position history in the two systems now looks like this:
;;
;;            Jump-Prev/Jump-Next:                      Emacs' position
;;
;;               o                                o
;;               |                                |
;;               |                                |
;;               o                                o  o
;;               .\                               |  |\
;;               . \                              |  | \
;;               .  x  (new edit)                 o  o  |
;;   (discarded  .                                | /   |
;;     branch)   .                                |/    |
;;               .                                o     |
;;                                                      |
;;                                                      |
;;                                                      x  (new edit)
;;
;; Now, what if you change your mind about those jump-prevs, and decide you
;; did like those other changes you'd made after all? With the standard
;; jump-prev/jump-next system, you're lost.  There's no way to recover them,
;; because that branch was discarded when you made the new edit.
;;
;; However, in Emacs' position system, those old buffer states are still
;; there in the position history.  You just have to rewind back through the
;; new edit, and back through the changes made by the jump-prevs, until you
;; reach them.  Of course, since Emacs treats jump-prevs (even jump-prevs of
;; jump-prevs!) as new changes,
;; you're really weaving backwards and forwards through the history, all the
;; time adding new changes to the end of the string as you go:
;;
;;                       o
;;                       |
;;                       |
;;                       o  o     o  (position new edit)
;;                       |  |\    |\
;;                       |  | \   | \
;;                       o  o  |  |  o  (position the position)
;;                       | /   |  |  |
;;                       |/    |  |  |
;;      (trying to get   o     |  |  x  (position the position)
;;       to this state)        | /
;;                             |/
;;                             o
;;
;; So far, this is still reasonably intuitive to use.  It doesn't behave so
;; differently to standard jump-prev/jump-next, except that by going back far
;; enough you can access changes that would be lost in standard
;; jump-prev/jump-next.
;;
;; However, imagine that after jump-preving as just described, you decide you
;; actually want to rewind right back to the initial state.  If you're lucky,
;; and haven't invoked any command since the last position, you can just keep
;; on jump-preving until you get back to the start:
;;
;;      (trying to get   o              x  (got there!)
;;       to this state)  |              |
;;                       |              |
;;                       o  o     o     o  (keep jump-preving)
;;                       |  |\    |\    |
;;                       |  | \   | \   |
;;                       o  o  |  |  o  o  (keep jump-preving)
;;                       | /   |  |  | /
;;                       |/    |  |  |/
;;      (already undid   o     |  |  o  (got this far)
;;       to this state)        | /
;;                             |/
;;                             o
;;
;; But if you're unlucky, and you happen to have moved the point (say) after
;; getting to the state labelled "got this far", then you've "broken the
;; position chain".  Hold on to something solid, because things are about to
;; get hairy.  If you try to position now, Emacs thinks you're trying to
;; position the jump-prevs! So to get back to the initial state you now have
;; to rewind through *all* the changes, including the jump-prevs you just did:
;;
;;      (trying to get   o                          x  (finally got there!)
;;       to this state)  |                          |
;;                       |                          |
;;                       o  o     o     o     o     o
;;                       |  |\    |\    |\    |\    |
;;                       |  | \   | \   | \   | \   |
;;                       o  o  |  |  o  o  |  |  o  o
;;                       | /   |  |  | /   |  |  | /
;;                       |/    |  |  |/    |  |  |/
;;      (already undid   o     |  |  o<.   |  |  o
;;       to this state)        | /     :   | /
;;                             |/      :   |/
;;                             o       :   o
;;                                     :
;;                             (got this far, but
;;                              broke the position chain)
;;
;; Confused?
;;
;; In practice you can just hold down the position key until you reach the
;; buffer state that you want.  But whatever you do, don't move around in the
;; buffer to *check* that you've got back to where you want! Because you'll
;; break the position chain, and then you'll have to traverse the entire
;; string of jump-prevs again, just to get back to the point at which you
;; broke the chain.
;;
;;
;; So what does `jump-tree-mode' do? Remember the diagram we drew to represent
;; the history we've been discussing (make a few edits, position a couple of
;; them, and edit again)? The diagram that conceptually represented our
;; position history, before we started discussing specific position systems?
;; It looked like this:
;;
;;                                o  (initial buffer state)
;;                                |
;;                                |
;;                                o
;;                                |\
;;                                | \
;;                                o  x  (current state)
;;                                |
;;                                |
;;                                o
;;
;; Well, that's *exactly* what the position history looks like to
;; `jump-tree-mode'.  It doesn't discard the old branch (as standard
;; jump-prev/jump-next does), nor does it treat jump-prevs as new changes to
;; be added to the end of a linear string of buffer states (as Emacs'
;; position does).  It just keeps track of the tree of branching changes that
;; make up the entire position history.
;;
;; If you position from this point, you'll rewind back up the tree to the
;; previous state:
;;
;;                                o
;;                                |
;;                                |
;;                                x  (position)
;;                                |\
;;                                | \
;;                                o  o
;;                                |
;;                                |
;;                                o
;;
;; If you were to position again, you'd rewind back to the initial state.
;; If on the other hand you jump-next the change, you'll end up back at the
;; bottom of the most recent branch:
;;
;;                                o  (position takes you here)
;;                                |
;;                                |
;;                                o  (start here)
;;                                |\
;;                                | \
;;                                o  x  (jump-next takes you here)
;;                                |
;;                                |
;;                                o
;;
;; So far, this is just like the standard jump-prev/jump-next system.
;; But what if you want to return to a buffer state located on a previous
;; branch of the history? Since `jump-tree-mode' keeps the entire history,
;; you simply need to tell it to switch to a different branch, and then
;; jump-next the changes you want:
;;
;;                                o
;;                                |
;;                                |
;;                                o  (start here, but switch
;;                                |\  to the other branch)
;;                                | \
;;                        (jump-next)  o  o
;;                                |
;;                                |
;;                        (jump-next)  x
;;
;; Now you're on the other branch, if you position and jump-next changes
;; you'll stay on that branch, moving up and down through the buffer states
;; located on that branch.  Until you decide to switch branches again, of
;; course.
;;
;; Real position trees might have multiple branches and sub-branches:
;;
;;                                o
;;                            ____|______
;;                           /           \
;;                          o             o
;;                      ____|__         __|
;;                     /    |  \       /   \
;;                    o     o   o     o     x
;;                    |               |
;;                   / \             / \
;;                  o   o           o   o
;;
;; Trying to imagine what Emacs' position would do as you move about such a
;; tree will likely frazzle your brain circuits! But in `jump-tree-mode',
;; you're just moving around this position history tree.  Most of the time,
;; you'll probably only need to stay on the most recent branch, in which case
;; it behaves like standard jump-prev/jump-next, and is just as simple to
;; understand.  But if you ever need to recover a buffer state on a different
;; branch, the possibility of switching between branches and accessing the
;; full position history is still there.
;;
;;
;;
;; The Jump-Tree Visualizer
;; ========================
;;
;; Actually, it gets better.  You don't have to imagine all these tree
;; diagrams, because `jump-tree-mode' includes an jump-tree visualizer which
;; draws them for you! In fact, it draws even better diagrams: it highlights
;; the node representing the current buffer state, it highlights the current
;; branch, and you can toggle the display of time-stamps (by hitting "t") and
;; a diff of the position changes (by hitting "d").  (There's one other tiny
;; difference: the visualizer puts the most recent branch on the left rather
;; than the right.)
;;
;; Bring up the position tree visualizer whenever you want by hitting "C-x u".
;;
;; In the visualizer, the usual keys for moving up and down a buffer instead
;; move up and down the position history tree (e.g. the up and down arrow keys, or
;; "C-n" and "C-p"). The state of the "parent" buffer (the buffer whose position
;; history you are visualizing) is updated as you move around the position tree in
;; the visualizer.  If you reach a branch point in the visualizer, the usual
;; keys for moving forward and backward in a buffer instead switch branch
;; (e.g. the left and right arrow keys, or "C-f" and "C-b").
;;
;; Clicking with the mouse on any node in the visualizer will take you
;; directly to that node, resetting the state of the parent buffer to the
;; state represented by that node.
;;
;; You can also select nodes directly using the keyboard, by hitting "s" to
;; toggle selection mode.  The usual motion keys now allow you to move around
;; the tree without changing the parent buffer.  Hitting <enter> will reset the
;; state of the parent buffer to the state represented by the currently
;; selected node.
;;
;; It can be useful to see how long ago the parent buffer was in the state
;; represented by a particular node in the visualizer.  Hitting "t" in the
;; visualizer toggles the display of time-stamps for all the nodes.  (Note
;; that, because of the way `jump-tree-mode' works, these time-stamps may be
;; somewhat later than the true times, especially if it's been a long time
;; since you last undid any positions.)

;;; Code:

(require 'jump-tree-visualizer)


;;; =================================================================
;;;                          Default keymaps

(defvar jump-tree-map nil
  "Keymap used in command `jump-tree-mode'.")

(unless jump-tree-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "M-,") 'jump-tree-jump-prev)
    (define-key map (kbd "M-.") 'jump-tree-jump-next)
    ;; we use "C-x j" for the jump-tree visualizer
    (define-key map (kbd "\C-x j") 'jump-tree-visualize)
    ;; set keymap
    (setq jump-tree-map map)))


;;; =====================================================================
;;;                        jump-tree commands

;;;###autoload
(define-minor-mode jump-tree-mode
  "Toggle jump-tree mode.
With no argument, this command toggles the mode.
A positive prefix argument turns the mode on.
A negative prefix argument turns it off.
jump-tree-mode replaces Emacs' standard position feature with a more
powerful yet easier to use version, that treats the position history
as what it is: a tree.
The following keys are available in `jump-tree-mode':
  \\{jump-tree-map}
Within the jump-tree visualizer, the following keys are available:
  \\{jump-tree-visualizer-mode-map}"
  nil                       ; init value
  jump-tree-mode-lighter    ; lighter
  jump-tree-map             ; keymap
  (if jump-tree-mode
      (progn
        (add-hook 'pre-command-hook  'jump-tree-pos-list-pre-command)
        (add-hook 'post-command-hook 'jump-tree-pos-list-post-command))
    (remove-hook 'pre-command-hook  'jump-tree-pos-list-pre-command)
    (remove-hook 'post-command-hook 'jump-tree-pos-list-post-command)
    (setq jump-tree-pos-list nil)
    (setq jump-tree-pos-tree nil)))

(defun turn-on-jump-tree-mode ()
  "Enable command `jump-tree-mode' in the current buffer.
Set the keybindings in global map."
  (interactive "p")
  (jump-tree-mode 1)
  (jump-tree-overridden-jump-bindings))

(defun jump-tree-overridden-jump-bindings ()
  "Override global keybindings `C-x j' `M-,' and `M-.'."
  (global-set-key (kbd "C-x j") 'jump-tree-visualize)
  (global-set-key [?\M-,] 'jump-tree-jump-prev)
  (global-set-key [?\M-.] 'jump-tree-jump-next))

;;;###autoload
(define-globalized-minor-mode global-jump-tree-mode
  jump-tree-mode turn-on-jump-tree-mode)

(provide 'jump-tree)
;;; jump-tree.el ends here
