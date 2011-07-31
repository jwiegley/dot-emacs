;;; find-library.el --- a library finder with completion capability.

;; Author: Takeshi Morishima <tm@interaccess.com>
;; Version: 0.1
;; Date: Mar 15, 2000
;; Keywords: file, lisp

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA

;;; Commentary:

;; This module can be used to find an Emacs Lisp library with
;; completion capability. This may be useful when coding an elisp
;; program on Emacs and want to view another library file. M-x
;; find-function is probably the most commonly used command, but
;; sometimes a library name is more convenient, especially if
;; completion is available.
;;
;; This command lists shadow libraries as well in the completion list.
;; Shadow libraries will have suffix "<number>" to the library name as
;; completion string. This provides a convenient way to check the
;; existence of a shadow, and can proceed to open to see what it is.
;;
;; A completion table cache is maintained to avoid unnecessary library
;; scan. Its validity is checked against load-path and modification
;; time of each directory listed in load-path each time the command is
;; invoked.
;;
;;
;; To install, place this file in your load-path (and byte compile if
;; you like), and add the following in .emacs.
;;
;;   (autoload 'find-library "find-library" "find-library" t)
;;
;; To use, type M-x find-library, then it prompts for a library name
;; to open. It automatically generates a completion table for all
;; library files in load-path. It also cache the last entry so that it
;; will not generate completion list everytime the command is
;; invoked. The timestamp info of each load-path directory is used to
;; detect the change in library file listings.
;;
;; Library loading command is also defined in this module. M-x
;; find-and-load-library is the command for this. Please add the
;; following to .emacs for autoload setup.
;;
;;   (autoload 'find-and-load-library "find-library" "find-library" t)
;;

;;; Code:

(defvar find-library-history nil
  "Input history ring pointer for `find-library' function.")

(defvar find-library-load-path-snap nil
  "A cons cell that holds a list of load-path in the CAR part and a
list of modification time of each corresponding library path in the
CDR part, which is a snapshot at the time of completion table
creation.")

(defvar find-library-completion-table-cache nil
  "A variable that holds the created completion table for
`find-library' function.")

;;;###autoload
(defun find-library ()
  "Find a library file with completion."
  (interactive)
  (let ((lib-dir (find-library-completion "Find library: "))
 library directory absolute-path)
    (if lib-dir
 (progn
   (setq absolute-path (apply 'expand-file-name lib-dir))
   (if (file-regular-p absolute-path)
       (find-file absolute-path)
     (if (file-regular-p (concat absolute-path ".el"))
  (find-file (concat absolute-path ".el"))
       (if (file-regular-p (concat absolute-path ".elc"))
    (find-file (concat absolute-path ".elc"))
  (error (format "No such library: (%s)" (car lib-dir))))))))))

;;;###autoload
(defun find-and-load-library ()
  "Find a library file with completion."
  (interactive)
  (let ((lib-dir (find-library-completion "Load library: ")))
    (if lib-dir
 (let ((load-path (cdr lib-dir)))
   (load (car lib-dir))))))

(defun find-library-completion (prompt)
  "Prompts the user using PROMPT string for a library name with
completion, and returns a list of actual library name and the
directory where it locates, or nil if user does not enter any library
name. This function should be called from an interactive command
function."
  (let ((lp load-path) library-string)
    (if (not (find-library-cache-valid-p lp))
 (progn
   (message "Listing libraries")
   (find-library-update-cache lp)))
    (setq library-string
   (completing-read prompt find-library-completion-table-cache
      nil t nil 'find-library-history))
    (and (not (= (length library-string) 0))
  (cdr (assoc library-string find-library-completion-table-cache)))))

(defun find-library-cache-valid-p (lp)
  "Returns t if the completion table cache is valid. LP is a list of
directories to be used as library search paths."
  (and find-library-load-path-snap
       (equal (car find-library-load-path-snap) lp)
       (equal (cdr find-library-load-path-snap)
       (mapcar '(lambda (dir) (elt (file-attributes dir) 5)) lp))))

(defun find-library-update-cache (lp)
  "Rescan library and renew the completion table cache. LP is a list
of directories to be used as library search paths."
  (setq find-library-completion-table-cache
 (find-library-make-completion-table lp))
  (setq find-library-load-path-snap
 (cons (apply 'list lp)
       (mapcar '(lambda (dir) (elt (file-attributes dir) 5)) lp))))

(defun find-library-make-completion-table (lp)
  "Walk thrugh load-path and gather library information and return a
completion table of the library files. LP is a list of directories to
be used as library search paths."
  (let (completion-table path library libraries reduced-list
    table-entry result-list count)
    (while lp
      (setq path (car lp))
      (setq lp (cdr lp))
      (if (file-directory-p path)
   (progn
     (setq libraries (directory-files path nil nil t))
     (setq reduced-list nil)
     (while libraries
       (setq library (car libraries))
       (setq libraries (cdr libraries))
       ;; For faster processing, assume that a file with ".el"
       ;; or ".elc" suffix is a regular file.
       (if (or (and (string-match "^\\(.+\\)\\.\\(elc\\|el\\)$" library)
      (setq library (match-string 1 library)))
	(file-regular-p (expand-file-name library path)))
    (if (not (member library reduced-list))
	(setq reduced-list (cons library reduced-list)))))
     (while reduced-list
       (setq library (car reduced-list))
       (setq table-entry (list library path))
       (setq reduced-list (cdr reduced-list))
       (if (member library result-list)
    (progn
      (setq count 1)
      (while (member
       (concat library "<" count ">")
       result-list)
	(setq count (1+ count)))
      (setq library (concat library "<" count ">"))))
       (setq result-list (cons library result-list))
       (setq completion-table
      (cons (cons library table-entry)
     completion-table))))))
    completion-table))

(provide 'find-library)
