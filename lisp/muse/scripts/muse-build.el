(add-to-list 'load-path "../contrib")
(add-to-list 'load-path "../experimental")
(add-to-list 'load-path "../lisp")

;; Avoid interference from VC.el
(setq vc-handled-backends nil)

(defun muse-elint-files ()
  (require 'elint)
  (elint-initialize)

  (defvar nomessage t)
  (load "muse" nil nomessage)
  (dolist (dir '("../lisp" "../contrib" "../experimental"))
    (dolist (file (directory-files dir nil "\\.el$"))
      (setq file (substring file 0 (string-match "\\.el$" file)))
      (load file nil nomessage)))

  (add-to-list 'elint-standard-variables 'current-prefix-arg)
  (add-to-list 'elint-standard-variables 'command-line-args-left)
  (add-to-list 'elint-standard-variables 'buffer-file-coding-system)
  (add-to-list 'elint-standard-variables 'save-some-buffers-action-alist)
  (add-to-list 'elint-standard-variables 'emacs-major-version)
  (add-to-list 'elint-standard-variables 'emacs-minor-version)
  (add-to-list 'elint-standard-variables 'emacs-version)
  (add-to-list 'elint-standard-variables 'window-system)
  (add-to-list 'elint-standard-variables 'muse-mode-abbrev-table)
  (dolist (file command-line-args-left)
    (find-file file)
    (message "Checking %s ..." file)
    (elint-current-buffer)
    (with-current-buffer (elint-get-log-buffer)
      (goto-char (point-min))
      (forward-line 2)
      (while (not (or (eobp)
                      (looking-at "^Linting complete")))
        (message (buffer-substring (muse-line-beginning-position)
                                   (muse-line-end-position)))
        (forward-line 1)))
    (kill-buffer (current-buffer))))

(defun muse-generate-autoloads ()
  (interactive)
  (defvar autoload-package-name)
  (defvar command-line-args-left)
  (defvar generated-autoload-file)
  (require 'autoload)
  (setq backup-inhibited t)
  (setq generated-autoload-file (expand-file-name "muse-autoloads.el"))
  (setq command-line-args-left (mapcar #'expand-file-name
                                       command-line-args-left))
  (if (featurep 'xemacs)
      (progn
          (setq autoload-package-name "muse")
          (batch-update-autoloads))
    (find-file generated-autoload-file)
    (delete-region (point-min) (point-max))
    (insert ";;; muse-autoloads.el --- autoloads for Muse
;;
;;; Code:
")
    (save-buffer 0)
    (batch-update-autoloads)
    (find-file generated-autoload-file)
    (goto-char (point-max))
    (insert ?\n)
    (insert "(provide 'muse-autoloads)
;;; muse-autoloads.el ends here
;;
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; End:
")
    (insert ?\n)
    (save-buffer 0)
    (kill-buffer (current-buffer))))
