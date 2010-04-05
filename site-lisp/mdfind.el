;;; mdfind.el --- Interface to OS X's mdfind command

;; Copyright (C) 2007  Jose Antonio Ortega

;; Author: Jose Antonio Ortega <jao@gnu.org>
;; Keywords: data

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; A quick and dirty major mode for displaying results of OS X's
;; `mdfind' command. Put this file in your load path and require
;; `mdfind': an interactive function of the same name will be
;; available. When invoked, it will ask you for a directory and a
;; query string that will be passed to the OS X mfind command. The
;; results of the query are then displayed on a special, read-only
;; buffer, whose mode derives from `org-mode' (so that links to files
;; are nicely displayed and clickable). In that buffer the following
;; key shortcuts are available:
;;   - n : go to next link
;;   - p : go to previous link
;;   - RET, o : follow link
;;   - q : bury buffer
;;   - m : perform new query

;; The latest version of this file is available at
;; http://hacks-galore.org/darcs?r=mdfind-el;a=tree

;;; Code:

(require 'org)

(defvar mdfind-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(control ?a)] 'beginning-of-line)
    (define-key map [(control ?e)] 'end-of-line)
    (define-key map [(control ?n)] 'next-line)
    (define-key map [(control ?p)] 'previous-line)
    (define-key map [??] 'describe-mode)
    (define-key map [?q] 'bury-buffer)
    (define-key map [?n] 'org-next-link)
    (define-key map [?p] 'org-previous-link)
    (define-key map (kbd "TAB") 'org-next-link)
    (define-key map (kbd "RET") 'org-open-at-point)
    (define-key map [?o] 'org-open-at-point)
    (define-key map [?m] 'mdfind)
    map)
  "Keymap for `mdfind-mode'.")

(define-derived-mode mdfind-mode org-mode "mdfind"
  "mdfind results browser"
  (use-local-map mdfind-mode-map)
  (set (make-local-variable 'org-startup-folded) nil)
  (toggle-read-only 1))

(defun mdfind--headline (qr dir)
  (let ((rn (count-lines (point-min) (point-max))))
    (goto-char (point-min))
    (insert (format "* %d results for \"%s\" in %s\n" rn qr dir))
    rn))

(defun mdfind--entries ()
  (let ((kill-whole-line nil)
        (pt (point)))
    (while (not (eobp))
      (beginning-of-line)
      (kill-line)
      (let* ((f (current-kill 0))
             (is-dir (file-directory-p f))
             (fn (file-name-nondirectory f))
             (ln (concat (file-name-sans-extension fn)
                         " (" (if is-dir "dir" (file-name-extension fn)) ")")))
        (insert "** " (org-make-link-string (concat "file:" f) ln)))
      (next-line))
    (sort-lines nil pt (point))))

(defun mdfind ()
  (interactive)
  (let ((dir (expand-file-name (read-file-name "Directory: ")))
        (qr (read-string "Query: "))
        (bf (get-buffer-create "*mdfind*")))
    (with-current-buffer bf
      (mdfind-mode)
      (message "Searching ...")
      (toggle-read-only -1)
      (delete-region (point-min) (point-max))
      (insert (shell-command-to-string (format "mdfind -onlyin %s %s" dir qr)))
      (let ((no (mdfind--headline qr dir)))
        (when (> no 0)
          (save-excursion (mdfind--entries))
          (pop-to-buffer bf)
          (goto-line 2) ; for some reason, next-link doesn't work at bob
          (org-next-link))
        (message "%d results found" no))
      (toggle-read-only 1))))

(provide 'mdfind)
;;; mdfind.el ends here
