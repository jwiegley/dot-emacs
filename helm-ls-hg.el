;;; helm-ls-hg.el --- List hg files in hg project. -*- lexical-binding: t -*-

;; Copyright (C) 2012 ~ 2014 Thierry Volpiatto <thierry.volpiatto@gmail.com>

;; Package-Requires: ((helm "1.5"))

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

;;; Code

(require 'cl-lib)
(require 'vc)
(require 'helm-locate)
(require 'helm-files)

(defvaralias 'helm-c-source-hg-list-files 'helm-source-hg-list-files)
(make-obsolete-variable 'helm-c-source-hg-list-files 'helm-source-hg-list-files "1.5.1")
(defvaralias 'helm-c-source-ls-hg-status 'helm-source-ls-hg-status)
(make-obsolete-variable 'helm-c-source-ls-hg-status 'helm-source-ls-hg-status "1.5.1")

(defvar helm-ls-hg-default-directory nil)
(defvar helm-ls-hg-status-command 'vc-dir)

;; Append visited files from `helm-source-hg-list-files' to `file-name-history'.
(add-to-list 'helm-file-completion-sources "Hg files list")

(cl-defun helm-hg-root (&optional (directory default-directory))
  (let ((root (locate-dominating-file directory ".hg")))
    (and root (file-name-as-directory root))))

(defun helm-hg-root-p (candidate)
  ;; Check for file existence in case of creation
  ;; of file or directory.
  (when (or (file-exists-p candidate)
            (file-directory-p candidate))
  (let ((default-directory (if (file-directory-p candidate)
                               (file-name-as-directory candidate)
                               (file-name-as-directory
                                helm-ff-default-directory))))
    (stringp (helm-hg-root)))))

(defun helm-hg-list-files ()
  (let ((dir (helm-hg-root)))
    (if (and dir (file-directory-p dir))
        (with-temp-buffer
          (process-file "hg" nil t nil "manifest")
          (cl-loop with ls = (split-string (buffer-string) "\n" t)
                   for f in ls
                   collect (concat dir f)))
        (error "Error: Not an hg repo (no .hg found)"))))

(defvar helm-source-hg-list-files
  `((name . "Hg files list")
    (init . (lambda ()
              (helm-init-candidates-in-buffer
               'global (helm-hg-list-files))))
    (keymap . ,helm-generic-files-map)
    (candidates-in-buffer)
    (filtered-candidate-transformer . helm-ls-hg-transformer)
    (action . ,(cdr (helm-get-actions-from-type helm-source-locate)))))

(defun helm-ls-hg-transformer (candidates _source)
  (cl-loop for i in candidates
           for abs = (expand-file-name i)
           for disp = (if (and helm-ff-transformer-show-only-basename
                               (not (string-match "[.]\\{1,2\\}$" i)))
                          (helm-basename i) abs)
           collect
           (cons (propertize disp 'face 'helm-ff-file) abs)))

(defun helm-ff-hg-find-files (_candidate)
  (with-helm-default-directory helm-default-directory
      (helm-run-after-quit
       #'(lambda (d)
           (let ((default-directory d))
             (helm-hg-find-files-in-project)))
       default-directory)))

(defun helm-ls-hg-status ()
  (with-output-to-string
      (with-current-buffer standard-output
        (apply #'process-file
               "hg"
               nil t nil
               (list "status")))))

(defvar helm-source-ls-hg-status
  '((name . "Hg status")
    (init . (lambda ()
              (helm-init-candidates-in-buffer
               'global
               (helm-ls-hg-status))))
    (candidates-in-buffer)
    (filtered-candidate-transformer . helm-ls-hg-status-transformer)
    (action-transformer . helm-ls-hg-status-action-transformer)
    (persistent-action . helm-ls-hg-diff)
    (persistent-help . "Diff")
    (action . (("Find file" . helm-find-many-files)
               ("Hg status" . (lambda (_candidate)
                                 (funcall helm-ls-hg-status-command
                                          (helm-hg-root))))))))

(defun helm-ls-hg-status-transformer (candidates _source)
  (cl-loop with root = (helm-hg-root helm-default-directory)
           for i in candidates
           collect
           (cond ((string-match "^\\(M \\)\\(.*\\)" i)
                  (cons (propertize i 'face '((:foreground "yellow")))
                        (expand-file-name (match-string 2 i) root)))
                 ((string-match "^\\([?] \\{1\\}\\)\\(.*\\)" i)
                  (cons (propertize i 'face '((:foreground "red")))
                        (expand-file-name (match-string 2 i) root)))
                 ((string-match "^\\([ARC] ?+\\)\\(.*\\)" i)
                  (cons (propertize i 'face '((:foreground "green")))
                        (expand-file-name (match-string 2 i) root)))
                 ((string-match "^\\([!] \\)\\(.*\\)" i)
                  (cons (propertize i 'face '((:foreground "Darkgoldenrod3")))
                        (expand-file-name (match-string 2 i) root)))
                 (t i))))

(defvar helm-ls-vc-delete-buffers-list nil)
(defun helm-ls-vc-commit (_candidate backend)
  (let* ((marked (helm-marked-candidates))
         (default-directory
          (file-name-directory (car marked))))
    (cl-loop for f in marked
             unless (or (find-buffer-visiting f)
                        (not (file-exists-p f)))
             do (push (find-file-noselect f)
                      helm-ls-vc-delete-buffers-list))
    (add-hook 'vc-checkin-hook 'helm-vc-checkin-hook)
    (vc-checkin marked backend)))

(defun helm-vc-checkin-hook ()
  (when helm-ls-vc-delete-buffers-list
    (cl-loop for b in helm-ls-vc-delete-buffers-list
             do (kill-buffer b)
             finally (setq helm-ls-vc-delete-buffers-list nil))))

(defun helm-ls-hg-commit (candidate)
  (helm-ls-vc-commit candidate 'Hg))

(defun helm-ls-hg-status-action-transformer (actions _candidate)
  (let ((disp (helm-get-selection nil t)))
    (cond ((string-match "^[?]\\{1\\}" disp)
           (append actions
                   (list '("Add file(s)"
                           . (lambda (candidate)
                               (let ((default-directory
                                      (file-name-directory candidate))
                                     (marked (helm-marked-candidates)))
                                 (vc-hg-register marked)))))))
          ((string-match "^M" disp)
           (append actions (list '("Diff file" . helm-ls-hg-diff)
                                 '("Commit file(s)" . helm-ls-hg-commit)
                                 '("Revert file" . vc-hg-revert))))
          ((string-match "^[!]" disp)
           (append actions (list '("Hg delete"
                                   . (lambda (candidate)
                                       (let ((default-directory
                                              (file-name-directory candidate))
                                             (marked (helm-marked-candidates)))
                                         (cl-loop for f in marked
                                                  do (vc-hg-delete-file f))))))))
          (t actions))))

(defun helm-ls-hg-diff (candidate)
  (with-current-buffer (find-file-noselect candidate)
    (call-interactively #'vc-diff)))

;;;###autoload
(defun helm-hg-find-files-in-project ()
  (interactive)
  (setq helm-ls-hg-default-directory default-directory)
  (unwind-protect
       (helm :sources '(helm-source-ls-hg-status
                        helm-source-hg-list-files)
             :buffer "*helm hg files*")
    (setq helm-ls-hg-default-directory nil)))

(provide 'helm-ls-hg)

;;; helm-ls-hg.el ends here
