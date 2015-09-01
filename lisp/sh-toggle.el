;;; sh-toggle --- toggle to and from the *shell* buffer

;; Copyright (C) 1997, 1998, 2000, 2001 Mikael Sjödin (mic@docs.uu.se)

;; Author: Mikael Sjödin <mic@docs.uu.se>
;;         John Wiegley <johnw@gnu.org>
;; Created: 19 Nov 1998
;; Version: 2.0
;; Keywords: processes
;; X-URL: http://www.gci-net.com/users/j/johnw/shell.html

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Provides the command shell-toggle which toggles between the
;; *shell* buffer and whatever buffer you are editing.
;;
;; This is done in an "intelligent" way.  Features are:
;;
;;  - Starts a shell if non is existing.
;;
;;  - Minimum distortion of your window configuration.
;;
;;  - When done in the shell-buffer you are returned to the same
;;    window configuration you had before you toggled to the shell.
;;
;;  - If you desire, you automagically get a "cd" command in the
;;    shell to the directory where your current buffers file exists;
;;    just call shell-toggle-cd instead of shell-toggle.
;;
;;  - You can convinently choose if you want to have the shell in
;;    another window or in the whole frame.  Just invoke shell-toggle
;;    again to get the shell in the whole frame.
;;
;; This file has been tested under Emacs 20.2.
;;
;; To use, call the functions `shell-toggle' or `shell-toggle-cd'.
;; It's most helpful to bind these to a key.

;;; Thanks to:

;; Christian Stern <Christian.Stern@physik.uni-regensburg.de> for
;; helpful sugestions.

;;; User Variables:

(defvar shell-toggle-goto-eob t
  "*If non-nil `shell-toggle' moves point to end of Shell buffer.
When `shell-toggle-cd' is called the point is always moved to the
end of the shell-buffer")

(defvar shell-toggle-automatic-cd t
  "*If non-nil `shell-toggle-cd' will send a \"cd\" to Shell.
If nil `shell-toggle-cd' will only insert the \"cd\" command in the
shell-buffer.  Leaving it to the user to press RET to send the
command to the shell.")

;;; User Functions:

;;;###autoload
(defun shell-toggle-cd ()
  "Calls `shell-toggle' with a prefix argument.
See the command `shell-toggle'"
  (interactive)
  (shell-toggle t))

;;;###autoload
(defun shell-toggle (make-cd)
  "Toggles between the *shell* buffer and the current buffer.
With a prefix ARG also insert a \"cd DIR\" command into the shell,
where DIR is the directory of the current buffer.

Call twice in a row to get a full screen window for the *shell*
buffer.

When called in the *shell* buffer returns you to the buffer you were
editing before caling the first time.

Options: `shell-toggle-goto-eob'"
  (interactive "P")
  ;; Try to descide on one of three possibilities:
  ;; 1. If not in shell-buffer, switch to it.
  ;; 2. If in shell-buffer and called twice in a row, delete other
  ;;    windows
  ;; 3. If in shell-buffer and not called twice in a row, return to
  ;;    state before going to the shell-buffer
  (if (eq major-mode 'shell-mode)
      (if (and (or (eq last-command 'shell-toggle)
		   (eq last-command 'shell-toggle-cd))
	       (not (eq (count-windows) 1)))
	  (delete-other-windows)
	(shell-toggle-buffer-return-from-shell))
    (shell-toggle-buffer-goto-shell make-cd)))

;;; Internal Functions:

(defvar shell-toggle-pre-shell-win-conf nil
  "Contains window config before the *shell* buffer was selected")

(defun shell-toggle-buffer-return-from-shell ()
  "Restores window config used before switching the *shell* buffer.
If no configuration has been stored, just bury the *shell* buffer."
  (if (window-configuration-p shell-toggle-pre-shell-win-conf)
      (progn
	(set-window-configuration shell-toggle-pre-shell-win-conf)
	(setq shell-toggle-pre-shell-win-conf nil)
	(bury-buffer (get-buffer "*shell*")))
    (bury-buffer)))

(defun shell-toggle-buffer-goto-shell (make-cd)
  "Switches other window to the *shell* buffer.
If no *shell* buffer exists start a new shell and switch to it in
other window.  If argument MAKE-CD is non-nil, insert a \"cd DIR\"
command into the shell, where DIR is the directory of the current
buffer.
Stores the window cofiguration before creating and/or switching window."
  (setq shell-toggle-pre-shell-win-conf (current-window-configuration))
  (let ((shell-buffer (get-buffer "*shell*"))
	(cd-command
	 ;; Find out which directory we are in (the method differs for
	 ;; different buffers)
	 (or (and make-cd
		  (buffer-file-name)
		  (file-name-directory (buffer-file-name))
		  (concat "cd " (file-name-directory (buffer-file-name))))
	     (and make-cd
		  list-buffers-directory
		  (concat "cd " list-buffers-directory)))))
    ;; Switch to an existin shell if one exists, otherwise switch to
    ;; another window and start a new shell
    (if shell-buffer
	(switch-to-buffer-other-window shell-buffer)
      (shell-toggle-buffer-switch-to-other-window)
      ;; Sometimes an error is generated when I call `shell' (it has
      ;; to do with my shell-mode-hook which inserts text into the
      ;; newly created shell-buffer and thats not allways a good
      ;; idea).
      (condition-case the-error
	  (shell)
	(error (switch-to-buffer "*shell*"))))
    (if (or cd-command shell-toggle-goto-eob)
	(goto-char (point-max)))
    (if cd-command
	(progn
	  (insert cd-command)
	  (if shell-toggle-automatic-cd
	      (comint-send-input))))))

(defun shell-toggle-buffer-switch-to-other-window ()
  "Switches to other window.
If the current window is the only window in the current frame, create
a new window and switch to it.  (This is less intrusive to the current
window configuration then `switch-buffer-other-window')"
  (let ((this-window (selected-window)))
    (other-window 1)
    ;; If we did not switch window then we only have one window and
    ;; need to create a new one.
    (if (eq this-window (selected-window))
	(progn
	  (split-window-vertically)
	  (other-window 1)))))

(provide 'sh-toggle)

;;; sh-toggle.el ends here
