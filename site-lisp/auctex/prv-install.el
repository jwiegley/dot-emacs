;;; prv-install.el --- Complicated install-time magic for preview-latex.

;; Copyright (C) 2002, 2005, 2014  Free Software Foundation, Inc.

;; Author: David Kastrup
;; Keywords: convenience, tex, wp

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This contains package-building stuff and other install-time magic.
;; It may well contain Emacs-version-specific code, but certain
;; functions here should be *callable* from any Emacs version.

;;; Code:

(defun preview-make-package ()
  "Do anything required to make a package in this version of Emacs,
other than actually copying the Lisp files.

Takes arguments on the comamnd line: the package directory and any
number of Lisp files to generate autoloads from.

Does nothing in Emacsen that do not support a package system."
  (if (featurep 'xemacs)
      (preview-make-package-xemacs))
  (setq command-line-args-left nil))

(defun preview-make-package-xemacs ()
  "Do anything required to make a package in XEmacs,
other than actually copying the Lisp files.

Generates auto-autoloads, custom-loads, and package metadata file
in the right locations.  Takes from the command line the package directory,
package name, and version (to be evaluated), followed by a file to append."
  (let* ((package-dir (pop command-line-args-left))
	 (package-name (pop command-line-args-left))
	 (release-version (eval (read (pop command-line-args-left))))
	 (author-version (eval (read (pop command-line-args-left))))
	 append-file
         (lisp-dir (expand-file-name (format "lisp/%s/" package-name)
				     package-dir))
         (metadata (expand-file-name "_pkg.el" lisp-dir))
         (custom-load (expand-file-name "custom-load.el" lisp-dir))
         (generated-autoload-file (expand-file-name "auto-autoloads.el"
                                                    lisp-dir))
         (si:message (symbol-function 'message))
	 make-backup-files noninteractive)
    ;; Delete and regenerate the custom-load file.
    (when (file-exists-p custom-load)
      (delete-file custom-load))
    (when (file-exists-p (concat custom-load "c"))
      (delete-file (concat custom-load "c")))
    (Custom-make-dependencies lisp-dir)
    (when (file-exists-p custom-load)
      (require 'cus-load)
      (byte-compile-file custom-load))
    ; Delete and regenerate the package metadata file.
    ; There is no compiled form of this file.
    (message "Updating metadata for the directory %s..." lisp-dir)
    (with-temp-file metadata
      (insert
       (concat ";;;###autoload\n"
               "(package-provide '" package-name "\n"
               "                 :version "
	       release-version "\n"
	       "                 :author-version "
	       "\"" author-version "\"\n"
               "                 :type 'regular)\n")))
    ; Delete and regenerate the auto-autoloads file.
    (message "Updating autoloads for the directory %s..." lisp-dir)
    (when (file-exists-p generated-autoload-file)
      (delete-file generated-autoload-file))
    (when (file-exists-p (concat generated-autoload-file "c"))
      (delete-file (concat generated-autoload-file "c")))
    (defun message (fmt &rest args)
      "Ignore useless messages while generating autoloads."
      (cond ((and (string-equal "Generating autoloads for %s..." fmt)
                  (file-exists-p (file-name-nondirectory (car args))))
             (funcall si:message
                      fmt (file-name-nondirectory (car args))))
            ((string-equal "No autoloads found in %s" fmt))
            ((string-equal "Generating autoloads for %s...done" fmt))
            (t (apply si:message fmt args))))
    (unwind-protect
	(cond ((fboundp 'update-autoloads-from-directory)
	       (update-autoloads-from-directory lisp-dir))
	      ((fboundp 'update-autoload-files)
	       (update-autoload-files (list lisp-dir) "auctex"))
	      (t (error "Failed to generate autoloads.")))
      (fset 'message si:message))
    (while (setq append-file (pop command-line-args-left))
      (when (file-exists-p generated-autoload-file)
	(with-temp-buffer (insert-file-contents append-file)
			  (append-to-file (point-min) (point-max)
					  generated-autoload-file))))
    (byte-compile-file generated-autoload-file)))


;;; prv-install.el ends here
