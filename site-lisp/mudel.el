;;; mudel.el --- The Mudel MUD Client

;; Copyright (C) 2004, 2005  Jorgen Schaefer

;; Author: Jorgen Schaefer
;; Keywords: application, games

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
;; 02111-1307, USA.

;;; Commentary:

;; This is a simple comint-based MUD client that provides an
;; appropriate interface for scripting. See the documentation of
;; `mudel-output-filter-functions', `mudel-command-sender',
;; `mudel-output-fill', `mudel-truncate-buffer' and
;; `mudel-add-scroll-to-bottom' for more information.

;;; Code:

(require 'comint)

(defgroup mudel nil
  "The Mudel MUD Client"
  :prefix "mudel-"
  :group 'games)

(defcustom mudel-mode-hook nil
  "Hook being run after `mudel-mode' has completely set up the buffer."
  :type 'hook
  :options '(mudel-add-scroll-to-bottom)
  :group 'mudel)

(defcustom mudel-output-filter-functions nil
  "Functions being run for each complete line of output from the
server. Each function is passed the line from the server as an
argument, and point is also in the displayed line from the server.

You probably often will want to set this buffer-local from
`mudel-mode-hook', and only if you're in the right `mudel-world'."
  :type 'hook
  :group 'mudel)

(defcustom mudel-interpret-commands t
  "Mudel will interpret user-defined commands when this is non-nil.
Usually, this is used to disable command parsing from within
user-defined commands to prevent infinite loops, but can also be used
to completely disable command sending."
  :type 'boolean
  :group 'mudel)

(defvar mudel-world nil
  "The name of the current world.")

(defvar mudel-mode-map
  (let ((map (make-sparse-keymap)))
    (if (functionp 'set-keymap-parent)
        (set-keymap-parent map comint-mode-map)        ; Emacs
      (set-keymap-parents map (list comint-mode-map))) ; XEmacs
    (when (functionp 'set-keymap-name)
      (set-keymap-name map 'mudel-mode-map))    ; XEmacs
    (define-key map (kbd "TAB") 'dabbrev-expand)
    map)
  "The map for the Mudel MUD client.")

(defun mudel (world host service)
  "Open a MUD connection to WORLD on HOST, port SERVICE.

To see how to add commands, see `mudel-command-sender'."
  (interactive "sWorld name: \nsHost: \nsPort: ")
  (let ((buf (make-comint world (cons host service))))
    (display-buffer buf)
    (with-current-buffer buf
      (mudel-mode world))
    buf))

(defun mudel-mode (world)
  "A mode for your MUD experience.

\\{mudel-mode-map}"
  (unless (and (eq major-mode 'comint-mode)
               (comint-check-proc (current-buffer)))
    (error "This buffer is not a comint buffer!"))
  (setq major-mode 'mudel-mode
        mode-name (format "Mudel/%s" world)
        mudel-world world)
  (use-local-map mudel-mode-map)
  (set (make-local-variable 'comint-input-sender)
       'mudel-command-sender)
  (add-hook 'comint-output-filter-functions
            'mudel-output-filter
            nil t)
  ;; User stuff.
  (run-hooks 'mudel-mode-hook))
(put 'mu-connection-mode 'mode-class 'special)

(defun mudel-send (str)
  "Send STR to the current MUD server."
  (funcall comint-input-sender
           (get-buffer-process (current-buffer))
           str))

(defun mudel-send-input (str)
  "Send STR as input to the comint process."
  (let* ((pmark (process-mark (get-buffer-process (current-buffer))))
         (old-input (buffer-substring pmark (point-max)))
         (idx (- (point) pmark)))
    (delete-region pmark (point-max))
    (goto-char pmark)
    (insert str)
    (comint-send-input)
    (goto-char pmark)
    (insert old-input)
    (goto-char (+ pmark idx))))

(defun mudel-insert (str)
  "Insert STR as if it where output in the mudel buffer."
  (save-excursion
    (let ((pmark (process-mark (get-buffer-process (current-buffer)))))
      (goto-char pmark)
      (forward-line 0)
      (insert str)
      (if comint-last-prompt-overlay
          (move-overlay comint-last-prompt-overlay
                        (point)
                        (overlay-end comint-last-prompt-overlay))
        (set-marker pmark (point))))))

(defun mudel-command-sender (proc str)
  "This is the function used as `comint-input-sender'. It extracts
commands and aliases from the string, and handles them off to the
appropriate function.

Let FOO be the first word in STR. If mudel-cmd-FOO exists, call it
with PROC and all words in STR as the arguments. If mudel-cmd-FOO has
the property 'do-not-parse-args set, pass the arguments (including any
leading space) verbatim as a single argument. If the symbol is not
bound to a function, send STR unmodified to the server."
  (if (zerop (length str))
      (comint-simple-send proc str)
    (mapc (lambda (line)
            (if (and mudel-interpret-commands
                     (string-match "^ *\\(\\w+\\)" line))
                (let* ((name (match-string 1 line))
                       (args (substring line (match-end 0)))
                       (cmd (intern (format "mudel-cmd-%s" (upcase name)))))
                  (if (fboundp cmd)
                      (if (get cmd 'do-not-parse-args)
                          (funcall cmd 
                                   (replace-regexp-in-string
                                    "^ *" ""
                                    args))
                        (apply cmd (split-string args)))
                    (comint-simple-send proc line)))
              (comint-simple-send proc line)))
          (split-string str "\n"))))

(defun mudel-output-filter (string)
  "Filter STRING that was inserted into the current buffer. This runs
`mudel-output-filter-functions', and should be in
`comint-output-filter-functions'."
  (when (string-match "\n" string)
    (save-excursion
      (goto-char comint-last-output-start)
      (while (search-forward "" nil t)
	(replace-match "'"))
      (forward-line 0)
      (while (< (point-at-eol)
                (process-mark (get-buffer-process (current-buffer))))
        (run-hook-with-args 'mudel-output-filter-functions
                            (buffer-substring-no-properties (point-at-bol) (point-at-eol)))
        (forward-line 1)))))

(defun mudel-output-fill (string)
  "Fill the region between `comint-last-output-start' and the
process-mark.

Don't forget to set `fill-column' when you use this."
  (fill-region (point-at-bol) (point-at-eol) nil t))

(defcustom mudel-truncate-buffer-size 100000
  "The maximum size of the buffer. If it ever exceeds that,
`mudel-truncate-buffer' will truncate old data."
  :type 'integer
  :group 'mudel)

(defun mudel-truncate-buffer (string)
  "Truncate the current buffer if it's size exceeds
`mudel-truncate-buffer-size' bytes.

This should be added to `comint-output-filter-functions'."
  (when (> (buffer-size) mudel-truncate-buffer-size)
    (buffer-disable-undo)
    (delete-region (point-min)
                   (- (buffer-size) mudel-truncate-buffer-size))
    (buffer-enable-undo)))

(defun mudel-add-scroll-to-bottom ()
  "Add this to `mudel-mode-hook' to recenter output at the bottom of
the window.

This works whenever scrolling happens, so it's added to
`window-scroll-functions'."
  (add-hook 'window-scroll-functions 'mudel-scroll-to-bottom nil t))

(defun mudel-scroll-to-bottom (window display-start)
  "Recenter WINDOW so that point is on the last line.

This is added to `window-scroll-functions' by
`mudel-add-scroll-to-bottom'.

The code is shamelessly taken (but adapted) from ERC."
  (when (and window
             (window-live-p window)
             (comint-check-proc (current-buffer))
             (>= (point)
                 (process-mark (get-buffer-process (current-buffer)))))
    (let ((resize-mini-windows nil))
      (save-selected-window
        (select-window window)
        (save-restriction
          (widen)
          (when (>= (point)
                    (process-mark (get-buffer-process (current-buffer))))
            (save-excursion
              (recenter -1)
              (sit-for 0))))))))

(provide 'mudel)
;;; mudel.el ends here
