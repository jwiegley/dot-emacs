;;; esh-buf-stack.el --- Add a buffer stack feature to Eshell

;; Copyright (C) 2013, 2014  by Tomoya Tanjo

;; Author: Tomoya Tanjo <ttanjo@gmail.com>
;; Keywords: eshell, extensions

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

;; This library adds a buffer stack feature to Eshell.
;; It is inspired by the buffer stack in Zsh.
;;
;; To use this package, add these lines to your .emacs file:
;;     (require 'esh-buf-stack)
;;     (setup-eshell-buf-stack)
;;     (add-hook 'eshell-mode-hook
;;               (lambda ()
;;                 (local-set-key
;;                  (kbd "M-q") 'eshell-push-command)))
;; You can push the current command to the buffer stack by using M-q,
;; and after executing another command, you can see the top of the stack poped.

;;; Code:
(require 'em-prompt)
(require 'esh-mode)

;;;###autoload
(defun setup-eshell-buf-stack ()
  "Setup the buffer stack for Eshell."
  (interactive)
  (add-hook 'eshell-after-prompt-hook
            'eshell-pop-stack))

(defvar-local *eshell-buffer-stack* nil
  "The buffer stack for Eshell")

;;;###autoload
(defun eshell-pop-stack ()
  "Pop a command from the buffer stack."
  (interactive)
  (when *eshell-buffer-stack*
    (insert (pop *eshell-buffer-stack*))))

;;;###autoload
(defun eshell-push-command (cmd)
  "Push CMD to the buffer stack."
  (interactive
   (let ((str (progn
                (eshell-bol)
                (buffer-substring (point) (point-max)))))
     (delete-region (point) (point-max))
     (list str)))
  (unless (equal cmd "")
    (push cmd *eshell-buffer-stack*)))

(provide 'esh-buf-stack)
;;; esh-buf-stack.el ends here
