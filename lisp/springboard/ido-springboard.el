;;; ido-springboard.el --- Temporarily change default-directory for one command

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 13 Jun 2012
;; Version: 1.0
;; Keywords: ido
;; X-URL: https://github.com/jwiegley/springboard

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

;; How many times have you wanted to fire off a quick command, such as M-!,
;; but the directory you want to run the command in isn't the same as the
;; directory of the current buffer?  In those situations, you want a quick way
;; to change the default-directory *for only the next command*.  That is what
;; Ido-Springboard aims to solve.
;;
;; It overrides command keys in ido-mode so that they use the
;; default-directory of the current viable completion, rather than the
;; default-directory of the buffer where you started the ido command.

(require 'ido)

(defgroup ido-springboard nil
  "Change default-directory for commands invoked at `ido-switch-buffer'."
  :group 'ido)

(defcustom ido-springboard-ignored-commands
  '(self-insert-command
    delete-backward-char
    abort-recursive-edit
    exit-minibuffer
    switch-to-buffer
    backward-char
    forward-char
    kill-line
    move-beginning-of-line
    move-end-of-line
    backward-kill-word
    forward-kill-word)
  "Commands that will not be trapped by Ido-Springboard."
  :type '(repeat command)
  :group 'ido-springboard)

(eval-when-compile
  (defvar ido-springboard-trapped nil))

(defun ido-springboard-match-directory ()
  (let ((item (or (let ((buf (get-buffer (car ido-matches))))
                    (and buf
                         (with-current-buffer buf
                           default-directory)))
                  (and ido-use-virtual-buffers ido-virtual-buffers
                       (cdr (assoc (car ido-matches)
                                   ido-virtual-buffers))))))
    (cond ((file-directory-p item)
           item)
          ((file-exists-p item)
           (file-name-directory item))
          (t
           nil))))

(defun ido-springboard-add-trap ()
  (add-hook 'pre-command-hook 'ido-springboard-trap-command t t))

(defun ido-springboard-remove-trap ()
  (remove-hook 'pre-command-hook 'ido-springboard-trap-command t))

(defun ido-springboard-trap-command ()
  (unless ido-springboard-trapped
    (condition-case err
        (unless (or (memq this-command ido-springboard-ignored-commands)
                    (string-match "\\`ido-" (symbol-name this-command)))
          (let ((dir (ido-springboard-match-directory)))
            (when dir
              ;; (message "Trapped command: %s" this-command)
              (loop for buf in (buffer-list)
                    when (minibufferp buf)
                    do (with-current-buffer buf
                         (ido-springboard-remove-trap)))
              (setq ido-springboard-trapped t)
              (throw 'abort dir))))
      (error
       (message "Error occurred: %s" err)))))

;;;###autoload
(defadvice ido-switch-buffer (around ido-springboard-ido-switch-buffer activate)
  "Adds ability to set `default-directory' for commands at ido minibuffer."
  (interactive)
  (add-hook 'minibuffer-setup-hook 'ido-springboard-add-trap)
  (add-hook 'minibuffer-exit-hook 'ido-springboard-remove-trap)
  (unwind-protect
      (let* (ido-springboard-trapped
             ido-springboard-already-trapped
             (default-directory (catch 'abort (ignore ad-do-it))))
        (if default-directory
            (call-interactively this-command)))
    (remove-hook 'minibuffer-setup-hook 'ido-springboard-add-trap)
    (remove-hook 'minibuffer-exit-hook 'ido-springboard-remove-trap)))

(provide 'ido-springboard)

;;; ido-springboard.el ends here
