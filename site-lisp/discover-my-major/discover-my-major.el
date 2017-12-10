;;; discover-my-major.el --- Discover key bindings and their meaning for the current Emacs major mode

;; Copyright (C) 2014, Steckerhalter

;; Author: steckerhalter
;; Package-Requires: ((makey "0.2"))
;; URL: https://github.com/steckerhalter/discover-my-major
;; Keywords: discover help major-mode keys

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
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

;; Discover key bindings and their meaning for the current Emacs major mode

;;; Code:

(require 'makey)

(defun dmm/major-mode-actions (&optional buffer)
  "Returns a formatted list of major mode actions in BUFFER.
If BUFFER is not specified then use the current buffer."
  (delq nil (mapcar 'dmm/format-binding (dmm/major-mode-bindings buffer))))

(defun dmm/mode-actions (mode &optional buffer)
  "Return a formatted list of actions for MODE in BUFFER.
If BUFFER is not specified then use the current buffer."
  (delq nil (mapcar 'dmm/format-binding (dmm/mode-bindings mode buffer))))

(defun dmm/mode-bindings (mode &optional buffer)
  "Return a list with the bindings of MODE in BUFFER.
If BUFFER is not specified then use the current buffer."
  (let* ((buffer (or buffer (current-buffer)))
         (mode-name (if (symbolp mode)
                        (symbol-name mode)
                      mode))
         (mode-string (dmm/mode-string mode-name)))
    (cdr (assoc mode-string (dmm/descbinds-all-sections (current-buffer))))))

(defun dmm/major-mode-bindings (&optional buffer)
  "Return a list with the bindings of BUFFER.
If BUFFER is not specified then use the current buffer."
  (let ((buffer (or buffer (current-buffer))))
    (dmm/mode-bindings major-mode)))

(defun dmm/mode-string (mode)
  "Return the string describing MODE.
This string is at the start of the section describing MODE in the
output of `describe-buffer-bindings'."
  (let* ((mode-name (if (symbolp mode)
                        (symbol-name mode)
                      mode))
         (mode-string (if (eq mode-name (symbol-name major-mode))
                          "Major Mode Bindings:"
                        (format "`%s' Minor Mode Bindings:" mode-name))))
    mode-string))

(defun dmm/mode-has-bindings-p (mode &optional buffer)
  "Returns t if MODE has bindings defined in BUFFER.
If BUFFER is nil, checks for bindings in `current-buffer'. Returns nil
if MODE is not a mode symbol or mode name or if MODE has no actions in
BUFFER."
  (let* ((mode-symbol (if (symbolp mode)
                          mode
                        (intern mode))))
    (> (safe-length (dmm/mode-bindings mode-symbol (current-buffer))) 0)))

(defun dmm/doc-summary (f)
  "Return the docstring for function F.

If F is not a function, return nil.

If F is is not documented, return a string indicating it is
undocumented."
  (when (functionp f)
    (let ((doc (documentation f)))
      (if doc
          (let* ((docstring (cdr (help-split-fundoc doc nil)))
                 (get-summary (lambda (str)
                                (string-match "^\\(.*\\)$" str)
                                (match-string 0 str))))
            (funcall get-summary (if docstring docstring doc)))
        (format "`%s' (not documented)" f)))))

(defun dmm/format-binding (item)
  "Check if ITEM has documention and return the formatted action for ITEM."
  (let* ((key (car item))
         (str (cdr item))
         (sym (intern-soft str))
         (doc (dmm/doc-summary sym)))
    (when doc
      (list key doc sym))))

(defun dmm/descbinds-all-sections (buffer &optional prefix menus)
  "Get the output from `describe-buffer-bindings' and parse the
result into a list with sections."
  (with-temp-buffer
    (let ((indent-tabs-mode t))
      (describe-buffer-bindings buffer prefix menus))
    (goto-char (point-min))
    (let ((header-p (not (= (char-after) ?\f)))
          sections header section)
      (while (not (eobp))
        (cond
         (header-p
          (setq header (buffer-substring-no-properties
                        (point)
                        (line-end-position)))
          (setq header-p nil)
          (forward-line 3))
         ((= (char-after) ?\f)
          (push (cons header (nreverse section)) sections)
          (setq section nil)
          (setq header-p t))
         ((looking-at "^[ \t]*$")
          ;; ignore
          )
         (t
          (let ((binding-start (save-excursion
                                 (and (re-search-forward "\t+" nil t)
                                      (match-end 0))))
                key binding)
            (when binding-start
              (setq key (buffer-substring-no-properties (point) binding-start)
                    key (replace-regexp-in-string"^[ \t\n]+" "" key)
                    key (replace-regexp-in-string"[ \t\n]+$" "" key))
              (goto-char binding-start)
              (setq binding (buffer-substring-no-properties
                             binding-start
                             (line-end-position)))
              (unless (member binding '("self-insert-command"))
                (push (cons key binding) section))))))
        (forward-line))
      (push (cons header (nreverse section)) sections)
      (nreverse sections))))

(defun dmm/get-makey-func (group-name)
  "If a makey function for GROUP-NAME is defind return the symbol, otherwise nil."
  (intern-soft (concat "makey-key-mode-popup-" (symbol-name group-name))))

;;;###autoload
(defun discover-my-major (arg)
  "Create a makey popup listing all major-mode keys with their description.
If ARG is non-nil recreate the makey popup function even if it is already defined."
  (interactive "P")
  (let* ((group-name major-mode))
    (when (or (not (dmm/get-makey-func group-name)) arg)
      (makey-initialize-key-groups
       (list `(,major-mode
               (description ,(format
                              "Discover my Major: `%s' --- %s"
                              major-mode
                              (replace-regexp-in-string
                               "[\e\r\n\t]+" " "
                               (documentation major-mode))))
               (actions ,(cons major-mode (dmm/major-mode-actions (current-buffer))))))))
    (funcall (dmm/get-makey-func group-name))))

(defvar dmm/discover-my-mode-history nil
  "History list for `dmm/discover-my-mode'.")

;;;###autoload
(defun discover-my-mode (mode)
  "Create a makey popup listing all MODE keys with their description."
  (interactive
   (let* ((active-modes (dmm/list-active-modes)))
     (list
      (completing-read "Discover mode: " active-modes (lambda (_) t) t nil 'dmm/discover-my-mode-history nil))))
  (let* ((mode-name (if (symbolp mode)
                        (symbol-name mode)
                      mode))
         (mode-symbol
          (if (symbolp mode)
              mode
            (intern mode))))
    (if (dmm/mode-has-bindings-p mode-symbol)
        (makey-initialize-key-groups
         (list `(,mode-symbol
                 (description ,(format
                                "Discover my Mode: `%s' --- %s"
                                mode-symbol
                                (replace-regexp-in-string
                                 "[\e\r\n\t]+" " "
                                 (documentation mode-symbol))))
                 (actions ,(cons mode-symbol (dmm/mode-actions mode-symbol (current-buffer)))))))
      (error "Mode `%s' has no bindings in the current buffer." mode-name))
    (funcall (dmm/get-makey-func mode-symbol))))

(defun dmm/list-active-modes ()
  "Returns a list of the active modes in the current buffer."
  (let ((active-modes))
    (mapc (lambda (mode) (condition-case nil
                        (if (and (symbolp mode) (symbol-value mode))
                            (add-to-list 'active-modes (prin1-to-string mode)))
                      (error nil) ))
          minor-mode-list)
    active-modes))

(provide 'discover-my-major)

;;; discover-my-major.el ends here
