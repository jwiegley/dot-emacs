;;; dired-async --- Copy/move/delete asynchronously in dired

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 14 Jun 2012
;; Version: 1.0
;; Keywords: dired async network
;; X-URL: https://github.com/jwiegley/dired-async

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

;; Copy/move/delete files asynchronously when TRAMP is not needed.

(require 'dired-aux)

(defgroup dired-async nil
  "Copy/move/delete asynchronously in dired"
  :group 'dired)

(defun start-process-and-kill-buffer (&rest args)
  (set-process-sentinel
   (apply #'start-process args)
   (lambda (proc change)
     (if (and (eq 'exit (process-status proc))
              (= 0 (process-exit-status proc)))
         (kill-buffer (process-buffer proc))))))

(defun dired-async-translate-for-rsync (path)
  (unless (string-match ":" path)
    (setq path (expand-file-name path)))
  (replace-regexp-in-string "/rsyncc:" "" (shell-quote-argument path)))

(defun rsync-file-asynchronously (from to)
  (let ((args (list "-avHy" "--delete-during" "--force-delete")))
    (nconc args
           (list (dired-async-translate-for-rsync from)
                 (dired-async-translate-for-rsync to)))
    (apply #'start-process-and-kill-buffer "rsync"
           (generate-new-buffer "*rsync*")
           (executable-find "rsync") args)))

(defun copy-file-asynchronously (from to ok-flag)
  (let ((args (list "-pvR")))
    (if ok-flag
        (nconc args (list "-i")))
    (nconc args (list (expand-file-name from) (expand-file-name to)))
    (apply #'start-process-and-kill-buffer "cp"
           (generate-new-buffer "*cp*")
           (executable-find "cp") args)))

(defun dired-copy-file (from to ok-flag)
  (dired-handle-overwrite to)
  (if (and (string-match ":" from) (string-match ":" to))
      (dired-copy-file-recursive from to ok-flag
                                 dired-copy-preserve-time t
                                 dired-recursive-copies)
    (if (or (string-match ":" from) (string-match ":" to)
            (file-exists-p to))
        (rsync-file-asynchronously from to)
      (copy-file-asynchronously from to ok-flag))))

(defun move-file-asynchronously (file newname ok-flag)
  (let ((args (list "-v")))
    (nconc args (list (expand-file-name file) (expand-file-name newname)))
    (apply #'start-process-and-kill-buffer "mv"
           (generate-new-buffer "*mv*")
           (executable-find "mv") args)))

(defun dired-rename-file (file newname ok-if-already-exists)
  (dired-handle-overwrite newname)
  (if (and (string-match ":" file) (string-match ":" newname))
      (rename-file file newname ok-if-already-exists)
    (if (or (string-match ":" file) (string-match ":" newname)
            (file-exists-p newname))
        (progn
          (rsync-file-asynchronously file newname)
          (delete-file-asynchronously file (file-directory-p file)))
      (move-file-asynchronously file newname ok-if-already-exists)))
  (and (get-file-buffer file)
       (with-current-buffer (get-file-buffer file)
         (set-visited-file-name newname nil t)))
  (dired-remove-file file)
  (dired-rename-subdir file newname))

(defun delete-file-asynchronously (file &optional recursive)
  (let ((args (list "-f")))
    (if recursive
        (nconc args (list "-r")))
    (nconc args (list (expand-file-name file)))
    (apply #'start-process-and-kill-buffer "rm"
           (generate-new-buffer "*rm*")
           (executable-find "rm") args)))

(defun dired-delete-file (file &optional recursive trash)
  (if (not (eq t (car (file-attributes file))))
      (if (string-match ":" file)
          (delete-file file trash)
        (delete-file-asynchronously file))
    (if (and recursive
             (directory-files file t dired-re-no-dot) ; Not empty.
             (or (eq recursive 'always)
                 (yes-or-no-p
                  (format "Recursively %s %s? "
                          (if (and trash
                                   delete-by-moving-to-trash)
                              "trash"
                            "delete")
                          (dired-make-relative file)))))
        (if (eq recursive 'top) (setq recursive 'always))
      (setq recursive nil))
    (if (string-match ":" file)
        (delete-directory file recursive trash)
      (delete-file-asynchronously file t))))

(provide 'dired-async)

;;; dired-async.el ends here
