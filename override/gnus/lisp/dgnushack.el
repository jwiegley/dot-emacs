;;; dgnushack.el --- a hack to set the load path for byte-compiling
;; Copyright (C) 1994-2014 Free Software Foundation, Inc.

;; Author: Lars Magne Ingebrigtsen <larsi@gnus.org>
;; Version: 4.19
;; Keywords: news, path

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(defvar dgnushack-default-load-path (copy-sequence load-path))

(unless (fboundp 'declare-function)
  (defmacro declare-function (&rest r)))

(defalias 'facep 'ignore)

(require 'cl)
(require 'iswitchb)

(condition-case nil
    (require 'org-entities)
  (error nil))

(defvar srcdir (or (getenv "srcdir") "."))
(defvar loaddir (and load-file-name (file-name-directory load-file-name)))

(defun my-getenv (str)
  (let ((val (getenv str)))
    (if (equal val "no") nil val)))

(if (my-getenv "lispdir")
    (push (my-getenv "lispdir") load-path))

;(push "/usr/share/emacs/site-lisp" load-path)

;; If we are building Gnus in a different directory than the source
;; directory, we must read *.el from source directory and write *.elc
;; into the building directory.  For that, we define this function
;; before loading bytecomp.  Bytecomp doesn't overwrite this function.
(defun byte-compile-dest-file (filename)
  "Convert an Emacs Lisp source file name to a compiled file name.
 In addition, remove directory name part from FILENAME."
  (setq filename (byte-compiler-base-file-name filename))
  (setq filename (file-name-sans-versions filename))
  (setq filename (file-name-nondirectory filename))
  (if (eq system-type 'windows-nt)
      (setq filename (downcase filename)))
  (cond ((eq system-type 'vax-vms)
	 (concat (substring filename 0 (string-match ";" filename)) "c"))
	((string-match emacs-lisp-file-regexp filename)
	 (concat (substring filename 0 (match-beginning 0)) ".elc"))
	(t (concat filename ".elc"))))

(require 'bytecomp)
;; To avoid having defsubsts and inlines happen.
;(if (featurep 'xemacs)
;    (require 'byte-optimize)
;  (require 'byte-opt))
;(defun byte-optimize-inline-handler (form)
;  "byte-optimize-handler for the `inline' special-form."
;  (cons 'progn (cdr form)))
;(defalias 'byte-compile-file-form-defsubst 'byte-compile-file-form-defun)

;; Work around for an incompatibility (XEmacs 21.4 vs. 21.5), see the
;; following threads:
;;
;; http://thread.gmane.org/gmane.emacs.gnus.general/56414
;; Subject: attachment problems found but not fixed
;;
;; http://thread.gmane.org/gmane.emacs.gnus.general/56459
;; Subject: Splitting mail -- XEmacs 21.4 vs 21.5
;;
;; http://thread.gmane.org/gmane.emacs.xemacs.beta/20519
;; Subject: XEmacs 21.5 and Gnus fancy splitting.
;;
;; Should be fixed in XEmacs (March 2007).
;; http://thread.gmane.org/gmane.emacs.xemacs.patches/8124
;; When should we remove this workaround?
;;
(when (and (featurep 'xemacs)
	   (let ((table (copy-syntax-table emacs-lisp-mode-syntax-table)))
	     (modify-syntax-entry ?= " " table)
	     (with-temp-buffer
	       (with-syntax-table table
		 (insert "foo=bar")
		 (goto-char (point-min))
		 (forward-sexp 1)
		 (eolp)))))
  ;; The original `with-syntax-table' uses `copy-syntax-table' which
  ;; doesn't seem to copy modified syntax entries in old XEmacs 21.5.
  (defmacro with-syntax-table (syntab &rest body)
    "Evaluate BODY with the SYNTAB as the current syntax table."
    `(let ((stab (syntax-table)))
       (unwind-protect
	   (progn
	     ;;(set-syntax-table (copy-syntax-table ,syntab))
	     (set-syntax-table ,syntab)
	     ,@body)
	 (set-syntax-table stab)))))

(push srcdir load-path)
(push loaddir load-path)
(load (expand-file-name "lpath.el" loaddir) nil t)

(defalias 'device-sound-enabled-p 'ignore)
(defalias 'play-sound-file 'ignore)
(defalias 'efs-re-read-dir 'ignore)
(defalias 'ange-ftp-re-read-dir 'ignore)
(defalias 'define-mail-user-agent 'ignore)
(defalias 'debbugs-gnu-summary-mode 'ignore)
(defvar debbugs-gnu-bug-number nil)

(eval-and-compile
  (unless (featurep 'xemacs)
    (defalias 'get-popup-menu-response 'ignore)
    (defalias 'event-object 'ignore)
    (autoload 'iswitchb-read-buffer "iswitchb")
    (autoload 'netrc-credentials "netrc")
    (defalias 'x-defined-colors 'ignore)
    (defalias 'read-color 'ignore)))

(eval-and-compile
  (when (featurep 'xemacs)
    (defvar window-point-insertion-type nil)
    (unless (fboundp 'defadvice)
      (autoload 'defadvice "advice" nil nil 'macro))
    (unless (boundp 'help-echo-owns-message)
      (defvar help-echo-owns-message))
    (unless (boundp 'gnus-registry-enabled)
      (defvar gnus-registry-enabled nil))
    (unless (boundp 'mail-dont-reply-to-names)
      (defvar mail-dont-reply-to-names nil))
    (unless (fboundp 'url-retrieve-synchronously)
      (defalias 'url-retrieve-synchronously 'url-retrieve))
    (unless (fboundp 'url-queue-retrieve)
      (defun url-queue-retrieve (url callback &optional cbargs silent
				     inhibit-cookies)
	(url-retrieve url callback cbargs)))
    (unless (boundp 'w3-configuration-directory)
      (setq w3-configuration-directory "~/.w3/"))
    (autoload 'Info-directory "info" nil t)
    (autoload 'Info-index "info" nil t)
    (autoload 'Info-index-next "info" nil t)
    (autoload 'Info-menu "info" nil t)
    (autoload 'ad-add-advice "advice")
    (unless (and (emacs-version>= 21 5)
		 (not (featurep 'sxemacs)))
      ;; calendar/auto-autoloads.el provides it.
      (autoload 'add-to-invisibility-spec "dummy"))
    (autoload 'annotations-at "annotations")
    (autoload 'apropos "apropos" nil t)
    (autoload 'apropos-command "apropos" nil t)
    (autoload 'bbdb-complete-name "bbdb-com" nil t)
    (autoload 'browse-url "browse-url" nil t)
    (autoload 'browse-url-of-file "browse-url" nil t)
    (autoload 'c-mode "cc-mode" nil t)
    (autoload 'customize-apropos "cus-edit" nil t)
    (autoload 'customize-group "cus-edit" nil t)
    (autoload 'customize-save-variable "cus-edit" nil t)
    (autoload 'customize-set-variable "cus-edit" nil t)
    (autoload 'customize-variable "cus-edit" nil t)
    (autoload 'debug "debug" nil t)
    (autoload 'sha1 "sha1")
    (if (featurep 'mule)
	(unless (locate-library "mule-ccl")
	  (autoload 'define-ccl-program "ccl" nil nil 'macro))
      (defalias 'define-ccl-program 'ignore))
    (autoload 'delete-annotation "annotations")
    (autoload 'dolist "cl-macs" nil nil 'macro)
    (autoload 'enriched-decode "enriched")
    (autoload 'eudc-expand-inline "eudc" nil t)
    (autoload 'executable-find "executable")
    (autoload 'font-lock-fontify-buffer "font-lock" nil t)
    (when (and (emacs-version>= 21 5)
	       (not (featurep 'sxemacs)))
      (autoload 'get-display-table "disp-table")
      (autoload 'put-display-table "disp-table"))
    (autoload 'info "info" nil t)
    (autoload 'mail-extract-address-components "mail-extr")
    (autoload 'mail-fetch-field "mail-utils")
    (autoload 'make-annotation "annotations")
    (autoload 'make-display-table "disp-table")
    (autoload 'pp "pp")
    (autoload 'ps-despool "ps-print" nil t)
    (autoload 'ps-spool-buffer "ps-print" nil t)
    (autoload 'ps-spool-buffer-with-faces "ps-print" nil t)
    (autoload 'read-passwd "passwd")
    (autoload 'regexp-opt "regexp-opt")
    (autoload 'reporter-submit-bug-report "reporter")
    (if (condition-case nil
	    (progn
	      (require 'rot13)
	      (not (fboundp 'rot13-string)))
	  (error nil))
	(defmacro rot13-string (string)
	  "Return ROT13 encryption of STRING."
	  `(let ((string ,string))
	     (with-temp-buffer
	       (insert string)
	       (translate-region (point-min) (point-max) ,rot13-display-table)
	       (buffer-string)))))
    (if (and (emacs-version>= 21 5)
	     (not (featurep 'sxemacs)))
	(autoload 'setenv "process" nil t)
      (autoload 'setenv "env" nil t))
    (autoload 'sgml-mode "psgml" nil t)
    (autoload 'smtpmail-send-it "smtpmail")
    (autoload 'sort-numeric-fields "sort" nil t)
    (autoload 'sort-subr "sort")
    (autoload 'thing-at-point "thingatpt")
    (autoload 'toggle-truncate-lines "view-less" nil t)
    (autoload 'trace-function-background "trace" nil t)
    (autoload 'unmorse-region "morse" nil t)
    (defalias 'frame-char-height 'frame-height)
    (defalias 'frame-char-width 'frame-width)
    (defalias 'frame-parameter 'frame-property)
    (defalias 'make-overlay 'ignore)
    (defalias 'overlay-end 'ignore)
    (defalias 'overlay-get 'ignore)
    (defalias 'overlay-put 'ignore)
    (defalias 'overlay-start 'ignore)
    (defalias 'overlays-in 'ignore)
    (defalias 'replace-dehighlight 'ignore)
    (defalias 'replace-highlight 'ignore)
    (defalias 'gnutls-available-p 'ignore)
    (defvar timer-list nil)
    (defvar scroll-margin 0)))

(defun dgnushack-emacs-compile-defcustom-p ()
  "Return non-nil if Emacs byte compiles `defcustom' forms.
Those Emacsen will warn against undefined variables and functions used
in `defcustom' forms."
  (let ((outbuf (with-temp-buffer
		  (insert "(defcustom foo (1+ (random)) \"\" :group 'emacs)\n")
		  (byte-compile-from-buffer (current-buffer) "foo.el"))))
    (when outbuf
      (prog1
	  (with-current-buffer outbuf
	    (goto-char (point-min))
	    (search-forward " 'foo '(byte-code " nil t))
	(kill-buffer outbuf)))))

(when (and (featurep 'xemacs)
	   (dgnushack-emacs-compile-defcustom-p))
  (maybe-fbind '(defined-colors face-attribute))
  (maybe-bind '(idna-program installation-directory)))

(when (featurep 'xemacs)
  (defadvice byte-optimize-apply (before use-mapcan (form) activate)
    "Replace (apply 'nconc (mapcar ...)) with (mapcan ...)."
    (let ((last (nth (1- (length form)) form)))
      (when (and (eq last (third form))
		 (consp last)
		 (eq 'mapcar (car last))
		 (equal (nth 1 form) ''nconc))
	(setq form (cons 'mapcan (cdr last)))))))

(defun dgnushack-compile-verbosely ()
  "Call dgnushack-compile with warnings ENABLED.  If you are compiling
patches to gnus, you should consider modifying make.bat to call
dgnushack-compile-verbosely.  All other users should continue to use
dgnushack-compile."
  (dgnushack-compile t))

(defun dgnushack-compile-error-on-warn ()
  "Call dgnushack-compile with minimal warnings, but with error-on-warn ENABLED.
This means that every warning will be reported as an error."
  (unless (dgnushack-compile nil t)
    (error "Error during byte compilation (warnings were reported as errors!).")))

(defun dgnushack-compile (&optional warn error-on-warn)
  ;;(setq byte-compile-dynamic t)
  (unless warn
    (setq byte-compile-warnings
	  '(free-vars unresolved callargs redefine suspicious)))
  (let ((files (directory-files srcdir nil "^[^=].*\\.el$"))
	(compilesuccess t)
	;;(byte-compile-generate-call-tree t)
	file elc)
    ;; Avoid barfing (from gnus-xmas) because the etc directory is not yet
    ;; installed.
    (when (featurep 'xemacs)
      (setq gnus-xmas-glyph-directory "dummy"))
    (dolist (file '(".dir-locals.el" "dgnushack.el" "lpath.el"))
      (setq files (delete file files)))
    (when (featurep 'base64)
      (setq files (delete "base64.el" files)))
    (condition-case code
	;; Under XEmacs 21.4 this loads easy-mmode.elc that provides
	;; the Emacs functions `propertize' and `replace-regexp-in-string'.
	(require 'mh-e)
      (error
       (message "No mh-e: %s %s" (cadr code) (or (locate-library "mh-e") ""))
       (setq files (delete "gnus-mh.el" files))))
    (condition-case code
	(require 'xml)
      (error
       (message "No xml: %s %s" (cadr code) (or (locate-library "xml") ""))
       (setq files (delete "nnrss.el" files))))
    (dolist (file
	     (if (featurep 'xemacs)
		 '("md5.el")
	       '("gnus-xmas.el" "messagexmas.el" "nnheaderxm.el")))
      (setq files (delete file files)))
    (unless (and (fboundp 'libxml-parse-html-region)
		 ;; lpath.el binds it.
		 (not (eq (symbol-function 'libxml-parse-html-region)
			  'ignore)))
      (dolist (file '("color.el"))
	(setq files (delete file files))))
    (unless (locate-library "epg")
      (setq files (delete "plstore.el" files)))
    ;; Temporary code until we fix pcase and defmethod stuff.
    (when (or (featurep 'xemacs)
	      (or (< emacs-major-version 24)
		  (< emacs-minor-version 3)))
      (setq files (delete "gnus-icalendar.el" files))
      ;; Temporary during development.
      (setq files (delete "gnus-cloud.el" files)))
    (dolist (file files)
      (setq file (expand-file-name file srcdir))
      (when (and (file-exists-p
		  (setq elc (concat (file-name-nondirectory file) "c")))
		 (file-newer-than-file-p file elc))
	(delete-file elc)))

    (while (setq file (pop files))
      (setq file (expand-file-name file srcdir))
      (when (or (not (file-exists-p
		      (setq elc (concat (file-name-nondirectory file) "c"))))
		(file-newer-than-file-p file elc))
	(if error-on-warn
	    (let ((byte-compile-error-on-warn t))
	      (unless (ignore-errors
			(byte-compile-file file))
		(setq compilesuccess nil)))
	  (ignore-errors
	    (byte-compile-file file)))))
    compilesuccess))

(defun dgnushack-recompile ()
  (require 'gnus)
  (byte-recompile-directory "." 0))

(defvar dgnushack-gnus-load-file
  (if (featurep 'xemacs)
      (expand-file-name "auto-autoloads.el")
    (expand-file-name "gnus-load.el")))

(defvar	dgnushack-cus-load-file
  (if (featurep 'xemacs)
      (expand-file-name "custom-load.el")
    (expand-file-name "cus-load.el")))

(defun dgnushack-make-cus-load ()
  (load "cus-dep")
  (let ((cusload-base-file dgnushack-cus-load-file))
    (defadvice directory-files (after exclude-dir-locals activate)
      "Exclude .dir-locals.el file."
      (dolist (file ad-return-value)
	(if (string-match "\\(?:\\`\\|/\\)\\.dir-locals\\.el\\'" file)
	    (setq ad-return-value (delete file ad-return-value)))))
    (unwind-protect
	(if (fboundp 'custom-make-dependencies)
	    (custom-make-dependencies)
	  (Custom-make-dependencies))
      (ad-unadvise 'directory-files))
    (when (featurep 'xemacs)
      (message "Compiling %s..." dgnushack-cus-load-file)
      (byte-compile-file dgnushack-cus-load-file))))

(defun dgnushack-make-auto-load ()
  (require 'autoload)
  (let ((generated-autoload-file dgnushack-gnus-load-file)
	(make-backup-files nil)
	(autoload-package-name "gnus"))
    (if (featurep 'xemacs)
	(if (file-exists-p generated-autoload-file)
	    (delete-file generated-autoload-file))
      (with-temp-file generated-autoload-file
	(insert ?\014)))
    (defadvice directory-files (after exclude-dir-locals activate)
      "Exclude .dir-locals.el file."
      (dolist (file ad-return-value)
	(if (string-match "\\(?:\\`\\|/\\)\\.dir-locals\\.el\\'" file)
	    (setq ad-return-value (delete file ad-return-value)))))
    (unwind-protect
	(batch-update-autoloads)
      (ad-unadvise 'directory-files))))

(defun dgnushack-make-load ()
  (unless (featurep 'xemacs)
    (message "Generating %s..." dgnushack-gnus-load-file)
    (with-temp-file dgnushack-gnus-load-file
      (insert-file-contents dgnushack-cus-load-file)
      (delete-file dgnushack-cus-load-file)
      (goto-char (point-min))
      (search-forward ";;; Code:")
      (forward-line)
      (delete-region (point-min) (point))
      (insert "\
;;; gnus-load.el --- automatically extracted custom dependencies and autoload
;;
;;; Code:
")
      (goto-char (point-max))
      (if (search-backward "custom-versions-load-alist" nil t)
	  (forward-line -1)
	(forward-line -1)
	(while (eq (char-after) ?\;)
	  (forward-line -1))
	(forward-line))
      (delete-region (point) (point-max))
      (insert "\n")
      ;; smiley-* are duplicated. Remove them all.
      (let ((point (point)))
	(insert-file-contents dgnushack-gnus-load-file)
	(goto-char point)
	(while (search-forward "smiley-" nil t)
	  (beginning-of-line)
	  (if (looking-at "(autoload ")
	      (delete-region (point) (progn (forward-sexp) (point)))
	    (forward-line))))
      ;;
      (goto-char (point-max))
      (when (search-backward "\n(provide " nil t)
	(forward-line -1)
	(delete-region (point) (point-max)))
      (insert "\

\(provide 'gnus-load)

;;; Local Variables:
;;; version-control: never
;;; no-byte-compile: t
;;; no-update-autoloads: t
;;; End:
;;; gnus-load.el ends here
")
      ))
  (message "Compiling %s..." dgnushack-gnus-load-file)
  (byte-compile-file dgnushack-gnus-load-file)
  (when (featurep 'xemacs)
    (message "Creating dummy gnus-load.el...")
    (with-temp-file (expand-file-name "gnus-load.el")
      (insert "\

\(provide 'gnus-load)

;;; Local Variables:
;;; version-control: never
;;; no-byte-compile: t
;;; no-update-autoloads: t
;;; End:
;;; gnus-load.el ends here"))))

(defun dgnushack-find-lisp-shadows (&optional lispdir)
  "Return a list of directories in which other Gnus installations exist.
This function looks for the other Gnus installations which will shadow
the new Gnus Lisp modules which have been installed in LISPDIR, using
the default `load-path'.  The return value will make sense only when
LISPDIR is existent and is listed in the default `load-path'.  Assume
LISPDIR will be prepended to `load-path' by a user if the default
`load-path' does not contain it."
  (unless lispdir
    (setq lispdir (getenv "lispdir")))
  (when (and lispdir (file-directory-p lispdir))
    (setq lispdir (file-truename (directory-file-name lispdir)))
    (let ((indices '("gnus.elc" "gnus.el" "gnus.el.bz2" "gnus.el.gz"
		     "message.elc" "message.el" "message.el.bz2"
		     "message.el.gz"))
	  (path (delq nil (mapcar
			   (lambda (p)
			     (condition-case nil
				 (when (and p (file-directory-p p))
				   (file-truename (directory-file-name p)))
			       (error nil)))
			   dgnushack-default-load-path)))
	  rest elcs)
      (while path
	(setq rest (cons (car path) rest)
	      path (delete (car rest) (cdr path))))
      (setq path (nreverse (cdr (member lispdir rest)))
	    rest nil)
      (while path
	(setq elcs indices)
	(while elcs
	  (when (file-exists-p (expand-file-name (pop elcs) (car path)))
	    (setq rest (cons (car path) rest)
		  elcs nil)))
	(setq path (cdr path)))
      (prog1
	  (setq path (nreverse rest))
	(when path
	  (let (print-level print-length)
	    (princ (concat "\n\
WARNING: The other Gnus installation" (if (cdr path) "s have" " has") "\
 been detected in:\n\n  " (mapconcat 'identity path "\n  ") "\n\n\
You will need to modify the run-time `load-path', remove them manually,
or remove them using `make remove-installed-shadows'.\n\n"))))))))

(defun dgnushack-remove-lisp-shadows (&optional lispdir)
  "Remove the other Gnus installations which shadow the recent one."
  (let ((path (with-temp-buffer
		(let ((standard-output (current-buffer)))
		  (dgnushack-find-lisp-shadows lispdir))))
	elcs files shadows file)
    (when path
      (unless (setq elcs (directory-files srcdir nil "\\.elc\\'"))
	(error "You should build .elc files first."))
      (setq files
	    (apply
	     'append
	     (mapcar
	      (lambda (el)
		(list (concat el "c") el (concat el ".bz2") (concat el ".gz")))
	      (append
	       (list (file-name-nondirectory dgnushack-gnus-load-file)
		     (file-name-nondirectory dgnushack-cus-load-file))
	       (mapcar (lambda (elc) (substring elc 0 -1)) elcs)))))
      (while path
	(setq shadows files)
	(while shadows
	  (setq file (expand-file-name (pop shadows) (car path)))
	  (when (file-exists-p file)
	    (princ (concat "  Removing " file "..."))
	    (condition-case nil
		(progn
		  (delete-file file)
		  (princ "done\n"))
	      (error (princ "failed\n")))))
	(setq path (cdr path))))))

(unless (fboundp 'with-demoted-errors)
  (defmacro with-demoted-errors (&rest body)
    "Run BODY and demote any errors to simple messages.
If `debug-on-error' is non-nil, run BODY without catching its errors.
This is to be used around code which is not expected to signal an error
but which should be robust in the unexpected case that an error is signaled."
    (declare (debug t) (indent 0))
    (let ((err (make-symbol "err")))
      `(condition-case ,err
	   (progn ,@body)
	 (error (message "Error: %S" ,err) nil)))))

;; XEmacs's `define-obsolete-variable-alias' takes only two arguments:
;; (define-obsolete-variable-alias OLDVAR NEWVAR)
(condition-case nil
    (progn
      (defvar dgnushack-obsolete-name nil)
      (defvar dgnushack-current-name nil)
      (unwind-protect
	  (define-obsolete-variable-alias
	    'dgnushack-obsolete-name 'dgnushack-current-name "0")
	(makunbound 'dgnushack-obsolete-name)
	(makunbound 'dgnushack-current-name)))
  (wrong-number-of-arguments
   (defadvice define-obsolete-variable-alias (around ignore-rest-args
						     (oldvar newvar &rest args)
						     activate)
     "Ignore arguments other than the 1st and the 2nd ones."
     ad-do-it)
   (put 'define-obsolete-variable-alias 'byte-optimizer
	(lambda (form)
	  (setcdr (nthcdr 2 form) nil)
	  form))))

;;; dgnushack.el ends here
