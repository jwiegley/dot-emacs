;;; multi-eshell.el --- Create and manage multiple shells within Emacs

;; Author: Chris Stucchio
;; URL: http://cims.nyu.edu/~stucchio
;; Version: 0.0.1

;;     This program is free software: you can redistribute it and/or modify
;;     it under the terms of the GNU General Public License as published by
;;     the Free Software Foundation, either version 3 of the License, or
;;     (at your option) any later version.

;;     This program is distributed in the hope that it will be useful,
;;     but WITHOUT ANY WARRANTY; without even the implied warranty of
;;     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;     GNU General Public License for more details.

;;     You should have received a copy of the GNU General Public License
;;     along with this program.  If not, see <http://www.gnu.org/licenses/>.

;; This file is written by Chris Stucchio, and the latest version is available at
;;
;; http://cims.nyu.edu/~stucchio
;;
;; This file makes it easier to use multiple shells within emacs. Features:
;;
;; multi-eshell -- Creates a NEW shell, even if one already exists.
;; multi-eshell-switch -- If not in a shell buffer, return to the last EXISTING
;;                        shell buffer. Otherwise, switch to the next buffer in
;;                        the shell ring.
;; multi-eshell-go-back -- Switch to the previous buffer in the shell ring.
;;
;; The customizable function multi-eshell-shell-function is user customizable, and lets the user
;; pick the particular shell to use (e.g. *ansi-term*, *shell*, *eshell*, etc).

(defun if-void (arg default)
  (if (boundp arg)
      (eval arg)
    default
      )
)

(defgroup multi-eshell nil
  "Simple support for having multiple shells open."
  :group 'languages)

(defcustom multi-eshell-shell-function '(shell)
  "Command called to create shell"
  :group 'multi-eshell)

(defcustom multi-eshell-name "*shell*" "The name of the buffer opened by the shell command."
  :type 'string
  :group 'multi-eshell)

(defun multi-eshell-function () "This function opens the appropriate shell." (eval multi-eshell-shell-function) )
;;;(defvar multi-eshell-function `(shell) ) ;;; Defines the shell. ('shell) or ('eshell)
;(defvar multi-eshell-name "*eshell*") ;;; Name of default shell or eshell buffer

(defvar multi-eshell-ring (make-ring 100) "This stores a bunch of buffers, which are shells created by multi-eshell." )
(setq multi-eshell-index 0 )
(defvar multi-eshell-last-buffer nil)

(defun multi-eshell-is-current-buffer-current-multi-eshell (&optional ignored)
  "Checks if current buffer is the current multi-eshell."
  (eq (current-buffer) (ring-ref multi-eshell-ring multi-eshell-index))
)

(defun multi-eshell-switch-to-current-shell (&optional ignored)
  "Switch to shell buffer."
  (if (buffer-live-p (ring-ref multi-eshell-ring multi-eshell-index))
      (switch-to-buffer (ring-ref multi-eshell-ring multi-eshell-index))
    )
)

(defun multi-eshell-current-shell (&optional ignored)
  "Returns the current multi-eshell."
  (ring-ref multi-eshell-ring multi-eshell-index)
)

(defun multi-eshell-switch-to-next-live-shell (&optional ignored)
  "Switches to the next live shell. Creates one if none exists."
  (interactive "p")
  (let ((still-looking t)
        (empty nil))
    (while (and still-looking (not empty))
      (if (ring-empty-p multi-eshell-ring)
          (progn
            (setq empty t)
            (multi-eshell 1)
            )
        (progn
          (if (buffer-live-p (ring-ref multi-eshell-ring multi-eshell-index))
              (progn
                (setq multi-eshell-index (+ multi-eshell-index 1))
                (switch-to-buffer (ring-ref multi-eshell-ring multi-eshell-index))
                (setq still-looking nil)
                )
            (ring-remove multi-eshell-ring multi-eshell-index)
            )
          )
        )
      )
    )
)

;;;###autoload
(defun multi-eshell-go-back (&optional ignored)
  "Switch to buffer multi-eshell-last-buffer."
  (interactive "p")
  (if (buffer-live-p multi-eshell-last-buffer)
      (switch-to-buffer multi-eshell-last-buffer)
    (message "Last buffer visited before multi-eshell is gone. Nothing to go back to..")
     ))


;;;###autoload
(defun multi-eshell-switch (&optional ignored)
  "If current buffer is not an multi-eshell, switch to current multi-eshell buffer. Otherwise, switch to next multi-eshell buffer."
  (interactive "p")
  (progn
    (setq multi-eshell-last-buffer (current-buffer))
    (let ((still-looking t)
          (empty nil))
      (if (ring-empty-p multi-eshell-ring)
          (multi-eshell 1)
        (if (and (buffer-live-p (multi-eshell-current-shell) )
             (not (eq (multi-eshell-current-shell) (current-buffer))))
        (switch-to-buffer (multi-eshell-current-shell))
      (multi-eshell-switch-to-next-live-shell)
      )
    )
  )))

;;;###autoload
(defun multi-eshell (&optional numshells)
  "Creates a shell buffer. If one already exists, this creates a new buffer, with the name '*shell*<n>', where n is chosen by the function generate-new-buffer-name."
  (interactive "p")
  (progn
    (setq multi-eshell-last-buffer (current-buffer))
    (dotimes (i (if-void 'numshells 1) nil)
      (let ( (tempname (generate-new-buffer-name "*tempshell*"))
             (new-buff-name (generate-new-buffer-name multi-eshell-name))
             (localdir default-directory)
             )
        (if (eq (get-buffer multi-eshell-name) nil) ;If a
            (progn
              (multi-eshell-function)
              ;(process-send-string (get-buffer-process new-buff-name) (concat "cd " localdir "\n"))
              (ring-insert multi-eshell-ring (current-buffer) )
              (setq multi-eshell-index (+ multi-eshell-index 1))
              )
          (progn
            (interactive)
            (multi-eshell-function)
            (rename-buffer tempname)
            (multi-eshell-function)
            (rename-buffer new-buff-name )
            (switch-to-buffer tempname)
            (rename-buffer multi-eshell-name)
        (switch-to-buffer new-buff-name)
        ;(process-send-string (get-buffer-process new-buff-name) (concat "cd " localdir "\n"))
        (ring-insert multi-eshell-ring (current-buffer) )
        (setq multi-eshell-index (+ multi-eshell-index 1))
        )
          )
        )
      )
    )
  )

(defun shell-with-name (name)
  "Creates a shell with name given by the first argument, and switches to it. If a buffer with name already exists, we simply switch to it."
  (let ((buffer-of-name (get-buffer name))
        (tempname (generate-new-buffer-name "*tempshell*") ) )
    (cond ((bufferp buffer-of-name) ;If the buffer exists, switch to it (assume it is a shell)
           (switch-to-buffer name))
          ( (bufferp (get-buffer multi-eshell-name))
          (progn
            (multi-eshell-function)
            (rename-buffer tempname)
            (multi-eshell-function)
            (rename-buffer name)
            (switch-to-buffer tempname)
            (rename-buffer multi-eshell-name)
            (switch-to-buffer name)))
          ( t
            (progn
              (multi-eshell-function)
              (rename-buffer name)
              )
            )
          )
    )
  )

(provide 'multi-eshell)

;;; multi-eshell.el ends here
