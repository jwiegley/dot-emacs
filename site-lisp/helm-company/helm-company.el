;;; helm-company.el --- Helm interface for company-mode

;; Copyright (C) 2013 Yasuyuki Oka <yasuyk@gmail.com>

;; Author: Yasuyuki Oka <yasuyk@gmail.com>
;; Version: 0.1.1
;; URL: https://github.com/yasuyk/helm-company
;; Package-Requires: ((helm "1.5.9") (company "0.6.13"))

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

;; Add the following to your Emacs init file:
;;
;; (autoload 'helm-company "helm-company") ;; Not necessary if using ELPA package
;; (eval-after-load 'company
;;   '(progn
;;      (define-key company-mode-map (kbd "C-:") 'helm-company)
;;      (define-key company-active-map (kbd "C-:") 'helm-company)))

;;; Code:

(require 'helm)
(require 'helm-match-plugin)
(require 'helm-files)
(require 'helm-elisp) ;; For with-helm-show-completion
(require 'company)

(defgroup helm-company nil
  "Helm interface for company-mode."
  :prefix "helm-company-"
  :group 'helm)

(defcustom helm-company-candidate-number-limit 300
  "Limit candidate number of `helm-company'.

Set it to nil if you don't want this limit."
  :group 'helm-company
  :type '(choice (const :tag "Disabled" nil) integer))

(defvar helm-company-help-window nil)
(defvar helm-company-backend nil)

(defun helm-company-init ()
  "Prepare helm for company."
  (helm-attrset 'company-candidates company-candidates)
  (helm-attrset 'company-prefix company-prefix)
  (setq helm-company-help-window nil)
  (if (<= (length company-candidates) 1)
      (helm-exit-minibuffer)
    (setq helm-company-backend company-backend))
  (company-abort))

(defun helm-company-action-insert (candidate)
  "Insert CANDIDATE."
  (delete-char (- (length (helm-attr 'company-prefix))))
  (insert candidate)
  ;; for GC
  (helm-attrset 'company-candidates nil))

(defun helm-company-action-show-document (candidate)
  "Show the documentation of the CANDIDATE."
  (interactive)
  (let ((buffer (funcall helm-company-backend 'doc-buffer candidate)))
    (when buffer
      (display-buffer buffer))))

(defun helm-company-show-doc-buffer (candidate)
  "Temporarily show the documentation buffer for the CANDIDATE."
  (interactive)
  (let ((buffer (funcall helm-company-backend 'doc-buffer candidate)))
    (when buffer
      (if (and helm-company-help-window
               (window-live-p helm-company-help-window))
          (with-selected-window helm-company-help-window
            (helm-company-display-document-buffer buffer))
        (setq helm-company-help-window
              (helm-company-display-document-buffer buffer))))))

(defun helm-company-find-location (candidate)
  "Find location of CANDIDATE."
  (interactive)
    (let* ((location (save-excursion (funcall helm-company-backend 'location candidate)))
           (pos (or (cdr location) (error "No location available")))
           (buffer (or (and (bufferp (car location)) (car location))
                       (find-file-noselect (car location) t))))
      (with-selected-window (display-buffer buffer t)
        (save-restriction
          (widen)
          (if (bufferp (car location))
              (goto-char pos)
            (goto-char (point-min))
            (forward-line (1- pos))))
        (set-window-start nil (point)))))

(defun helm-company-display-document-buffer (buffer)
  "Temporarily show the documentation BUFFER."
  (with-current-buffer buffer
    (goto-char (point-min)))
  (display-buffer buffer
                  '((display-buffer-same-window . t)
                    (display-buffer-reuse-window . t))))

(defmacro helm-company-run-action (&rest body)
  `(with-helm-window
    (save-selected-window
      (with-helm-display-same-window
        ,@body))))

(defun helm-company-run-show-doc-buffer ()
  "Run showing douctment action from `helm-company'."
  (interactive)
  (helm-company-run-action
   (helm-company-show-doc-buffer (helm-get-selection))))

(defun helm-company-run-show-location ()
  "Run showing location action from `helm-company'."
  (interactive)
  (helm-company-run-action
   (helm-company-find-location (helm-get-selection))))

(defvar helm-company-map
  (let ((keymap (make-sparse-keymap)))
    (set-keymap-parent keymap helm-map)
    (define-key keymap (kbd "M-s") 'helm-company-run-show-location)
    (define-key keymap (kbd "C-s") 'helm-company-run-show-doc-buffer)
    (delq nil keymap))
  "Keymap used in Company sources.")

(defvar helm-company-actions
  '(("Insert" . helm-company-action-insert)
    ("Show douctment (If available)" . helm-company-action-show-document)
    ("Find location (If available)" . helm-company-find-location))
  "Actions for `helm-company'.")

(defvar helm-source-company
  `((name . "Company")
    (init . helm-company-init)
    (candidates . (lambda () (helm-attr 'company-candidates)))
    (action . ,helm-company-actions)
    (persistent-action . helm-company-show-doc-buffer)
    (persistent-help . "Show document (If available)")
    (keymap . ,helm-company-map)
    (company-candidates)))

;;;###autoload
(defun helm-company ()
  "Select `company-complete' candidates by `helm'.
It is useful to narrow candidates."
  (interactive)
  (unless company-candidates
    (company-complete))
  (when company-point
    (helm :sources 'helm-source-company
          :buffer  "*helm company*"
          :candidate-number-limit helm-company-candidate-number-limit)))

(provide 'helm-company)

;; Local Variables:
;; coding: utf-8
;; eval: (setq byte-compile-not-obsolete-vars '(display-buffer-function))
;; eval: (checkdoc-minor-mode 1)
;; End:

;;; helm-company.el ends here
