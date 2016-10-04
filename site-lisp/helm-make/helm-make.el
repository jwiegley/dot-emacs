;;; helm-make.el --- Select a Makefile target with helm

;; Copyright (C) 2014 Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/helm-make
;; Version: 0.2.0
;; Package-Requires: ((helm "1.5.3") (projectile "0.11.0"))
;; Keywords: makefile

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; A call to `helm-make' will give you a `helm' selection of this directory
;; Makefile's targets.  Selecting a target will call `compile' on it.

;;; Code:

(require 'helm)
(require 'helm-multi-match)

(declare-function ivy-read "ext:ivy")

(defgroup helm-make nil
  "Select a Makefile target with helm."
  :group 'convenience)

(defcustom helm-make-do-save nil
  "If t, save all open buffers visiting files from Makefile's directory."
  :type 'boolean
  :group 'helm-make)

(defcustom helm-make-build-dir ""
  "Specify a build directory for an out of source build.
The path should be relative to the project root.

When non-nil `helm-make-projectile' will first look in that directory for a
makefile."
  :type '(string)
  :group 'helm-make)
(make-variable-buffer-local 'helm-make-build-dir)

(defcustom helm-make-sort-targets nil
  "Whether targets shall be sorted.
If t, targets will be sorted as a final step before calling the
completion method.

HINT: If you are facing performance problems set this to nil.
This might be the case, if there are thousand of targets."
  :type 'boolean
  :group 'helm-make)

(defcustom helm-make-cache-targets nil
  "Whether to cache the targets or not.

If t, cache targets of Makefile. If `helm-make' or `helm-make-projectile'
gets called for the same Makefile again, and the Makefile hasn't changed
meanwhile, i.e. the modification time is `equal' to the cached one, reuse
the cached targets, instead of recomputing them. If nil do nothing.

You can reset the cache by calling `helm-make-reset-db'."
  :type 'boolean
  :group 'helm-make)

(defcustom helm-make-executable "make"
  "Store the name of make executable."
  :type 'string
  :group 'helm-make)

(defcustom helm-make-require-match t
  "When non-nil, don't allow selecting a target that's not on the list."
  :type 'boolean)

(defcustom helm-make-named-buffer nil
  "When non-nil, name compilation buffer based on make target."
  :type 'boolean)

(defcustom helm-make-comint nil
  "When non-nil, run helm-make in Comint mode instead of Compilation mode."
  :type 'boolean)

(defvar helm-make-command nil
  "Store the make command.")

(defvar helm-make-target-history nil
  "Holds the recently used targets.")

(defvar helm-make-makefile-names '("Makefile" "makefile" "GNUmakefile")
  "List of Makefile names which make recognizes.
An exception is \"GNUmakefile\", only GNU make unterstand it.")

(defun helm--make-action (target)
  "Make TARGET."
  (let* ((make-command (format helm-make-command target))
         (compile-buffer (compile make-command helm-make-comint)))
    (when helm-make-named-buffer
      (helm--make-rename-buffer compile-buffer target))))

(defun helm--make-rename-buffer (buffer target)
  "Rename the compilation BUFFER based on the make TARGET."
  (let ((buffer-name (format "*compilation (%s)*" target)))
    (when (get-buffer-window buffer-name)
      (delete-window (get-buffer-window buffer-name)))
    (when (get-buffer buffer-name)
      (kill-buffer buffer-name))
    (with-current-buffer buffer
      (rename-buffer buffer-name))))

(defcustom helm-make-completion-method 'helm
  "Method to select a candidate from a list of strings."
  :type '(choice
          (const :tag "Helm" helm)
          (const :tag "Ido" ido)
          (const :tag "Ivy" ivy)))

;;;###autoload
(defun helm-make (&optional arg)
  "Call \"make -j ARG target\". Target is selected with completion."
  (interactive "p")
  (setq helm-make-command (format "%s -j%d %%s" helm-make-executable arg))
  (let ((makefile (helm--make-makefile-exists default-directory)))
    (if makefile
        (helm--make makefile)
      (error "No Makefile in %s" default-directory))))

(defun helm--make-target-list-qp (makefile)
  "Return the target list for MAKEFILE by parsing the output of \"make -nqp\"."
  (let ((default-directory (file-name-directory
                            (expand-file-name makefile)))
        targets target)
    (with-temp-buffer
      (insert
       (shell-command-to-string
        "make -nqp __BASH_MAKE_COMPLETION__=1 .DEFAULT 2>/dev/null"))
      (goto-char (point-min))
      (unless (re-search-forward "^# Files" nil t)
        (error "Unexpected \"make -nqp\" output"))
      (while (re-search-forward "^\\([^%$:#\n\t ]+\\):\\([^=]\\|$\\)" nil t)
        (setq target (match-string 1))
        (unless (or (save-excursion
		      (goto-char (match-beginning 0))
		      (forward-line -1)
		      (looking-at "^# Not a target:"))
                    (string-match "^\\([/a-zA-Z0-9_. -]+/\\)?\\." target))
          (push target targets))))
    targets))

(defun helm--make-target-list-default (makefile)
  "Return the target list for MAKEFILE by parsing it."
  (let (targets)
    (with-temp-buffer
      (insert-file-contents makefile)
      (goto-char (point-min))
      (while (re-search-forward "^\\([^: \n]+\\):" nil t)
        (let ((str (match-string 1)))
          (unless (string-match "^\\." str)
            (push str targets)))))
    targets))

(defcustom helm-make-list-target-method 'default
  "Method of obtaining the list of Makefile targets."
  :type '(choice
          (const :tag "Default" default)
          (const :tag "make -qp" qp)))

(defun helm--make-makefile-exists (base-dir &optional dir-list)
  "Check if one of `helm-make-makefile-names' exist in BASE-DIR.

Returns the absolute filename to the Makefile, if one exists,
otherwise nil.

If DIR-LIST is non-nil, also search for `helm-make-makefile-names'."
  (let* ((default-directory (file-truename base-dir))
         (makefiles
          (progn
            (unless (and dir-list (listp dir-list))
              (setq dir-list (list "")))
            (let (result)
              (dolist (dir dir-list)
                (dolist (makefile helm-make-makefile-names)
                  (push (expand-file-name makefile dir) result)))
              (reverse result)))))
    (cl-find-if 'file-exists-p makefiles)))

(defvar helm-make-db (make-hash-table :test 'equal)
  "An alist of Makefile and corresponding targets.")

(cl-defstruct helm-make-dbfile
  targets
  modtime
  sorted)

(defun helm--make-cached-targets (makefile)
  "Return cached targets of MAKEFILE.

If there are no cached targets for MAKEFILE, the MAKEFILE modification
time has changed, or `helm-make-cache-targets' is nil, parse the MAKEFILE,
and cache targets of MAKEFILE, if `helm-make-cache-targets' is t."
  (let* ((att (file-attributes makefile 'integer))
         (modtime (if att (nth 5 att) nil))
         (entry (gethash makefile helm-make-db nil))
         (new-entry (make-helm-make-dbfile))
         (targets (cond
                   ((and helm-make-cache-targets
                         entry
                         (equal modtime (helm-make-dbfile-modtime entry))
                         (helm-make-dbfile-targets entry))
                    (helm-make-dbfile-targets entry))
                   (t
                    (delete-dups (if (eq helm-make-list-target-method 'default)
                                     (helm--make-target-list-default makefile)
                                   (helm--make-target-list-qp makefile)))))))
    (when helm-make-sort-targets
      (unless (and helm-make-cache-targets
                   entry
                   (helm-make-dbfile-sorted entry))
        (setq targets (sort targets 'string<)))
      (setf (helm-make-dbfile-sorted new-entry) t))

    (when helm-make-cache-targets
      (setf (helm-make-dbfile-targets new-entry) targets
            (helm-make-dbfile-modtime new-entry) modtime)
      (puthash makefile new-entry helm-make-db))
    targets))

;;;###autoload
(defun helm-make-reset-cache ()
  "Reset cache, see `helm-make-cache-targets'."
  (interactive)
  (clrhash helm-make-db))

(defun helm--make (makefile)
  "Call make for MAKEFILE."
  (when helm-make-do-save
    (let* ((regex (format "^%s" default-directory))
           (buffers
            (cl-remove-if-not
             (lambda (b)
               (let ((name (buffer-file-name b)))
                 (and name
                      (string-match regex (expand-file-name name)))))
             (buffer-list))))
      (mapc
       (lambda (b)
         (with-current-buffer b
           (save-buffer)))
       buffers)))
  (let ((targets (helm--make-cached-targets makefile))
        (default-directory (file-name-directory makefile)))
    (delete-dups helm-make-target-history)
    (cl-case helm-make-completion-method
      (helm
       (helm :sources
             `((name . "Targets")
               (candidates . ,targets)
               (action . helm--make-action))
             :history 'helm-make-target-history
             :preselect (when helm-make-target-history
                          (format "^%s$" (car helm-make-target-history)))))
      (ivy
       (ivy-read "Target: "
                 targets
                 :history 'helm-make-target-history
                 :preselect (car helm-make-target-history)
                 :action 'helm--make-action
                 :require-match helm-make-require-match))
      (ido
       (let ((target (ido-completing-read
                      "Target: " targets
                      nil nil nil
                      'helm-make-target-history)))
         (when target
           (helm--make-action target)))))))

;;;###autoload
(defun helm-make-projectile (&optional arg)
  "Call `helm-make' for `projectile-project-root'.
ARG specifies the number of cores.

By default `helm-make-projectile' will look in `projectile-project-root'
followed by `projectile-project-root'/build, for a makefile.

You can specify an additional directory to search for a makefile by
setting the buffer local variable `helm-make-build-dir'."
  (interactive "p")
  (require 'projectile)
  (setq helm-make-command (format "%s -j%d %%s" helm-make-executable arg))
  (let ((makefile (helm--make-makefile-exists
                   (projectile-project-root)
                   (if (and (stringp helm-make-build-dir)
                            (not (string-match-p "\\`[ \t\n\r]*\\'" helm-make-build-dir)))
                       `(,helm-make-build-dir "" "build")
                     `(,@helm-make-build-dir "" "build")))))
    (if makefile
        (helm--make makefile)
      (error "No Makefile found for project %s" (projectile-project-root)))))

(provide 'helm-make)

;;; helm-make.el ends here
