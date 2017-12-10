;;; makefile-runner.el --- Searches for Makefile and fetches targets

;; Copyright (C) 2009-2012 Dan Amlund Thomsen

;; Author: Dan Amlund Thomsen <dan@danamlund.dk>
;; URL: http://danamlund.dk/emacs/make-runner.html
;; Version: 1.2.0
;; Created: 2009-01-01
;; By: Dan Amlund Thomsen
;; Keywords: makefile, make, ant, build

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; An easy method of running different makefiles. The function searches current
;; and parent directories for a makefile, fetches targets, and asks
;; the user which of the targets to run.

;; The function is `makefile-runner'.

;; By default it supports make's Makefiles and ant's build.xml files.

;;; Installation:

;; Save makefile-runner.el to your load path and add the following to
;; your .emacs file:
;;
;; (require 'makefile-runner)

;; You can add a keybinding to run the function, for example:
;;
;; (global-set-key (kbd "F11") 'makefile-runner)

;;; Customization:

;; M-x customize-group makefile-runner
;;
;; You can add further build systems by changing
;; `makefile-runner--makefiles'.
;;
;; And you can set a specific Makefile to use by changing
;; `makefile-runner--makefile'. A better method is to add a
;; file-variable to the affected files. For example, add to following
;; to the start of foo/src/foo.c:
;;
;; /* -*- makefile-runner--makefile: "../Makefile" -*- */

;;; Changelog:
;; (2017-07-29) 1.2.0: Add GPL license
;; (2012-09-29) 1.1.2: Now also searches for makefiles next to the current file
;; (2012-09-29) 1.1.1: Better handles no-makefile-found.
;; (2012-09-29) 1.1.0: Added ant support. minibuffer now shows
;;                     makefile filename and its directory-name.

;;; Code:

;;;###autoload
(defcustom makefile-runner--makefile nil
  "Use this Makefile instead of searching for one. Intended to be
  used as a local variable (e.g. as a file variable: 
  -*- makefile-runner--makefile: \"../../Makefile\" -*-)"
  :type 'file
  :group 'makefile-runner)

;;;###autoload

(defcustom makefile-runner--makefiles
  '(("Makefile"  makefile-runner--get-targets-make "cd \"%s\"; make %s")
    ("build.xml" makefile-runner--get-targets-ant "cd \"%s\"; ant %s"))
  "A list of (MAKEFILE-FILENAME FIND-TARGETS-PROCEDURE MAKEFILE-RUN-STRING)."
  :type 'sexp
  :group 'makefile-runner)

(defvar makefile-runner--last-target nil
  "Remembers the last target")

(defvar makefile-runner--hist nil
  "History of makefile targets")

(defun makefile-runner--find-makefile ()
  "Search current buffer's directory for makefiles. If no
makefiles exists, continue searching in the directory's parent. If
no makefiles exists in any directory parents return nil."
  (when (buffer-file-name)
    (let* ((path (substring (file-name-directory (buffer-file-name)) 0 -1))
           (makefile nil)
           (path-up (function 
                     (lambda ()
                       (setq path (expand-file-name ".." path))
                       (and (> (length path) 2) 
                            (not (equal ".." (substring path -2)))))))
           (find-makefile 
            (function 
             (lambda ()
               (let ((makefiles (mapcar 'car makefile-runner--makefiles)))
                 (while (and (not makefile) (not (null makefiles)))
                   (let ((makefile-path (concat path "/" (car makefiles))))
                     (when (file-exists-p makefile-path)
                       (setq makefile makefile-path)))
                   (setq makefiles (cdr makefiles)))
                 makefile)))))
      (while (and (not (funcall find-makefile)) (funcall path-up)) nil)
      makefile)))

(defun makefile-runner--get-targets-make (file)
  "Search FILE for Makefile targets and return them as a list of
strings. Does not add targets that match the regular expression
in \"\\(^\\.\\)\\|[\\$\\%]\"."
  (let ((target-exclude-regexp "\\(^\\.\\)\\|[\\$\\%]"))
    (with-temp-buffer
      (insert-file-contents file)
      (goto-char (point-max))
      (let ((targets nil))
        (while (re-search-backward "^\\([^:\n#[:space:]]+?\\):" 
                                   (not 'bound) 'noerror)
          (unless (string-match target-exclude-regexp
                                (match-string 1))
            (setq targets (cons (match-string 1) targets))))
        targets))))

(defun makefile-runner--get-targets-ant (file)
  "Search the ant file 'build.xml' in FILE and return a list of
targets."
  (delq nil
        (mapcar (lambda (e) (if (and (listp e) (equal (car e) 'target))
                                (cdr (assoc 'name (cadr e)))
                              nil))
                (with-temp-buffer
                  (insert-file-contents file)
                  (libxml-parse-xml-region (point-min) (point-max))))))
  

(defun makefile-runner--get-targets (file)
  "Find appropiate get-targets procedure from
`makefile-runner--makefiles' and execute it on file. Returns a
list of targets."
  (let ((get-targets (cadr (assoc (file-name-nondirectory file) 
                                  makefile-runner--makefiles))))
    (funcall get-targets file)))

;;;###autoload
(defun makefile-runner (target &optional makefile)
  "Run nearest makefile with TARGET.

When calling interactively. The targets from the nearest makefile
is extracted and the user is asked which target to use.

Closest Makefile means first Makefile found when seacrching
upwards from the directory of the current buffer.

Set `makefile-runner--makefile' to use a specific Makefile rather
than search for one.

By default it searches for 'Makefile' and 'build.xml' files. To
add more makefiles or change the priority ordering see
`makefile-runner--makefiles'."
  (interactive
   (let* ((makefile (or makefile-runner--makefile
                        (makefile-runner--find-makefile)))
          (makefile-path (and makefile
                              (concat (file-name-nondirectory 
                                       (substring (file-name-directory makefile) 
                                                  0 -1))
                                      "/" (file-name-nondirectory makefile)))))
     (if makefile
         (list (completing-read (concat makefile-path ": ")
                                (makefile-runner--get-targets makefile)
                                nil nil makefile-runner--last-target
                                'makefile-runner--hist "")
               makefile)
       (progn (message "No makefile found.")
              (list nil nil)))))
  (when target
    (setq makefile-runner--last-target target)
    (let ((makefile-runstring (car (cddr (assoc (file-name-nondirectory makefile) 
                                                makefile-runner--makefiles)))))
      (compile (concat (format makefile-runstring 
                               (file-name-directory makefile)
                               target)
                       "\n")))))

(provide 'makefile-runner)

;;; makefile-runner.el ends here
