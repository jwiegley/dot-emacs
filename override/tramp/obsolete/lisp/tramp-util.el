;;; tramp-util.el --- Misc utility functions to use with Tramp

;; Copyright (C) 2001-2013 Free Software Foundation, Inc.

;; Author: Kai Großjohann <kai.grossjohann@gmx.net>
;;         Michael Albinus <michael.albinus@gmx.de>
;; Keywords: comm, extensions, processes
;; Package: tramp

;; This file is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Some misc. utility functions that might go nicely with Tramp.
;; Mostly, these are kluges awaiting real solutions later on.

;;; Code:

(require 'tramp)
(require 'tramp-sh)

;; Utility functions.

;; `executable-find', `start-process' and `call-process' have no file
;; name handler.  The idea is that such a handler is called when
;; `default-directory' matches a regexp in `file-name-handler-alist'.
;; This would allow to run commands on remote hosts.  The disadvantage
;; is that commands which should run locally anyway would also run
;; remotely, like the commands called by `gnus'.  This implementation
;; is an experimental one as proof of concept, it will change after
;; discussion with (X)Emacs maintainers.

;; In Emacs 22, there is already `process-file', which is similar to
;; `call-process'.

;; `call-process-region' must be advised, because it calls the C
;; function `Fcall_process'.  Once `call-process' has a file name
;; handler, this advice isn't necessary any longer.

;; `start-process-shell-command' and `call-process-shell-command' must
;; be advised, because they use `shell-file-name'.  It cannot be
;; assumed that the shell on a remote host is equal to the one of the
;; local host.

;; With Emacs 23 this shouldn't be necessary any longer.  We check it
;; via the existence of `start-file-process', which has introduced
;; there.

;; Other open problems are `setenv'/`getenv'.

(unless (tramp-exists-file-name-handler 'start-file-process "/")

  (defadvice executable-find
    (around tramp-advice-executable-find activate)
    "Invoke `tramp-sh-handle-executable-find' for Tramp files."
    ;; The check for `load-in-progress' is necessary because during
    ;; loading the usual trick setting `default-directory' to a local
    ;; filename seems not to work.  On the other hand, it might
    ;; prevent `executable-find' checks in packages which expect the
    ;; executables on remote hosts.  Needs a better solution.
    (if (and (not load-in-progress)
	     (eq (tramp-find-foreign-file-name-handler default-directory)
		 'tramp-sh-file-name-handler))
	(setq ad-return-value
	      (apply 'tramp-sh-handle-executable-find (ad-get-args 0)))
      ad-do-it))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'executable-find)))

  (defadvice start-process
    (around tramp-advice-start-process activate)
    "Invoke `tramp-sh-handle-start-file-process' for Tramp files."
    (if (eq (tramp-find-foreign-file-name-handler default-directory)
	    'tramp-sh-file-name-handler)
	(setq ad-return-value (apply 'start-file-process (ad-get-args 0)))
      ad-do-it))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'start-process)))

  (defadvice start-process-shell-command
    (around tramp-advice-start-process-shell-command activate)
    "Invoke `tramp-sh-handle-shell-command' for Tramp files."
    (if (eq (tramp-find-foreign-file-name-handler default-directory)
	    'tramp-sh-file-name-handler)
	(with-parsed-tramp-file-name default-directory nil
	  (let ((shell-file-name
		 (tramp-get-connection-property v "remote-shell" "/bin/sh"))
		(shell-command-switch "-c"))
	    ad-do-it))
      ad-do-it))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'start-process-shell-command))))

(unless (tramp-exists-file-name-handler 'process-file "/")

  (defadvice call-process
    (around tramp-advice-process-file activate)
    "Invoke `tramp-sh-handle-process-file' for Tramp files."
    (if (eq (tramp-find-foreign-file-name-handler default-directory)
	    'tramp-sh-file-name-handler)
	(setq ad-return-value (apply 'process-file (ad-get-args 0)))
      ad-do-it))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'call-process)))

  (defadvice call-process-region
    (around tramp-advice-call-process-region activate)
    "Invoke `tramp-sh-handle-call-process-region' for Tramp files."
    (if (eq (tramp-find-foreign-file-name-handler default-directory)
	    'tramp-sh-file-name-handler)
	(setq ad-return-value
	      (apply 'tramp-sh-handle-call-process-region (ad-get-args 0)))
      ad-do-it))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'call-process-region)))

  (defadvice call-process-shell-command
    (around tramp-advice-call-process-shell-command activate)
    "Configure `call-process-shell-command' for Tramp files."
    (if (eq (tramp-find-foreign-file-name-handler default-directory)
	    'tramp-sh-file-name-handler)
	(with-parsed-tramp-file-name default-directory nil
	  (let ((shell-file-name
		 (tramp-get-connection-property v "remote-shell" "/bin/sh"))
		(shell-command-switch "-c"))
	    ad-do-it))
      ad-do-it))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'call-process-shell-command))))

(unless (tramp-exists-file-name-handler 'file-remote-p "/")
  (defadvice file-remote-p
    (around tramp-advice-file-remote-p
	    (filename &optional identification connected) activate)
    "Invoke `tramp-handle-file-remote-p' for Tramp files."
    (save-match-data
      (if (eq (tramp-find-foreign-file-name-handler
	       (expand-file-name filename))
	      'tramp-sh-file-name-handler)
	  (setq ad-return-value
		(tramp-handle-file-remote-p filename identification connected))
	ad-do-it)))
  (add-hook 'tramp-util-unload-hook
	    (lambda () (ad-unadvise 'file-remote-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; compile.el parses the compilation output for file names.  It
;; expects them on the local machine.  This must be changed.

(add-hook
 'compilation-mode-hook
 (lambda ()
   (set (make-local-variable 'comint-file-name-prefix)
	(or (file-remote-p default-directory) ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; `grep-compute-defaults' computes `grep-command',
;; `grep-find-command', `grep-tree-command', `grep-use-null-device',
;; `grep-find-use-xargs' and `grep-highlight-matches'.  Since those
;; values might be different for remote hosts, we set the variables to
;; the "Not Set" (default) value.

(mapc
 (lambda (x)

   (eval
    `(defadvice ,x
       (around ,(intern (format "tramp-advice-%s" x)) activate)
       "Make customization variables local for Tramp files."
       (if (eq (tramp-find-foreign-file-name-handler default-directory)
	       'tramp-sh-file-name-handler)
	   (with-parsed-tramp-file-name default-directory nil
	     ;; Initialize with default values from defcustom, if
	     ;; not set yet for this remote connection.
	     (let ((grep-command
		    (when (boundp 'grep-command)
		      (tramp-get-connection-property
		       v "grep-command"
		       (eval (car (get 'grep-command
				       'standard-value))))))
		   (grep-find-command
		    (when (boundp 'grep-find-command)
		      (tramp-get-connection-property
		       v "grep-find-command"
		       (eval (car (get 'grep-find-command
				       'standard-value))))))
		   (grep-tree-command
		    (when (boundp 'grep-tree-command)
		      (tramp-get-connection-property
		       v "grep-tree-command"
		       (eval (car (get 'grep-tree-command
				       'standard-value))))))
		   (grep-use-null-device
		    (when (boundp 'grep-use-null-device)
		      (tramp-get-connection-property
		       v "grep-use-null-device"
		       (eval (car (get 'grep-use-null-device
				       'standard-value))))))
		   (grep-find-use-xargs
		    (when (boundp 'grep-find-use-xargs)
		      (tramp-get-connection-property
		       v "grep-find-use-xargs"
		       (eval (car (get 'grep-find-use-xargs
				       'standard-value))))))
		   (grep-highlight-matches
		    (when (boundp 'grep-highlight-matches)
		      (tramp-get-connection-property
		       v "grep-highlight-matches"
		       (eval (car (get 'grep-highlight-matches
				       'standard-value)))))))
	       ad-do-it))
	 ;; local file
	 ad-do-it)))

   (eval
    `(add-hook
      'tramp-util-unload-hook
      (lambda () (ad-unadvise (quote ,x))))))

 '(grep grep-find grep-tree grep-process-setup))

(defadvice grep-compute-defaults
  (around tramp-advice-grep-compute-defaults activate)
  "Save customization variables for Tramp files."
  (if (eq (tramp-find-foreign-file-name-handler default-directory)
	  'tramp-sh-file-name-handler)
      (with-parsed-tramp-file-name default-directory nil
	(prog1
	    ad-do-it
	  ;; Save computed values for next run.
	  (when (boundp 'grep-command)
	    (tramp-set-connection-property
	     v "grep-command" (symbol-value 'grep-command)))
	  (when (boundp 'grep-find-command)
	    (tramp-set-connection-property
	     v "grep-find-command" (symbol-value 'grep-find-command)))
	  (when (boundp 'grep-tree-command)
	    (tramp-set-connection-property
	     v "grep-tree-command" (symbol-value 'grep-tree-command)))
	  (when (boundp 'grep-use-null-device)
	    (tramp-set-connection-property
	     v "grep-use-null-device" (symbol-value 'grep-use-null-device)))
	  (when (boundp 'grep-find-use-xargs)
	    (tramp-set-connection-property
	     v "grep-find-use-xargs" (symbol-value 'grep-find-use-xargs)))
	  (when (boundp 'grep-highlight-matches)
	    (tramp-set-connection-property
	     v "grep-highlight-matches"
	     (symbol-value 'grep-highlight-matches)))))
    ;; local file
    ad-do-it))

(add-hook 'tramp-util-unload-hook
	  (lambda () (ad-unadvise 'grep-compute-defaults)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; gud.el uses `gud-find-file' for specifying a file name function.
;; In XEmacs 21, 'gud must be required before calling `gdb'.
;; Otherwise, gdb.el is used, which is not supported.

(defun tramp-gud-file-name (filename)
  "Evaluate a file name to be loaded.
If it is an absolute file name, and not a remote one, prepend the remote part."
  (let ((filename (expand-file-name filename)))
    (setq filename
	  (if (file-remote-p filename)
	      ;; It is already expanded.
	      filename
	    ;; Prefix the Tramp remote file name.
	    (expand-file-name filename (file-remote-p default-directory))))

    ;; Emacs 22 uses `gud-file-name' which we should do as well.
    ;; `gud-<MINOR-MODE>-directories' must be Tramp file names.
    (if (functionp 'gud-file-name)
	(tramp-compat-funcall 'gud-file-name filename)
      filename)))

(defun tramp-gud-massage-args (args)
  "Set arguments of debugger on remote hosts.
They must be changed to be relative to the default directory.
Works only for relative file names and Tramp file names."
  (let ((default-directory (expand-file-name default-directory))
	(item args)
	file)
    (while (car item)
      ;; The expansion is performed for EVERY parameter, even for
      ;; non file names.  But this doesn't hurt, because it is
      ;; changed back to its original value afterwards.
      (setq file (expand-file-name (car item)))
      (when (string-lessp default-directory file)
	(setcar item (substring file (length default-directory))))
      (setq item (cdr item))))
  args)

(when (functionp 'gud-find-file)
  (defvar gud-find-file)
  (setq gud-find-file 'tramp-gud-file-name))

(mapc
 (lambda (x)

   ;; (X)Emacs 21 use `gud-<MINOR-MODE>-find-file'.
   (eval
    `(defadvice ,(intern (format "gud-%s-find-file" x))
       (before
	,(intern (format "tramp-advice-gud-%s-find-file" x))
	(filename) activate)
       "Invoke `tramp-gud-find-file' for Tramp files."
       (when (eq (tramp-find-foreign-file-name-handler default-directory)
		 'tramp-sh-file-name-handler)
	 (ad-set-arg 0 (tramp-gud-file-name (ad-get-arg 0))))))
   (eval
    `(add-hook
      'tramp-util-unload-hook
      (lambda ()
	(ad-unadvise (quote ,(intern (format "gud-%s-find-file" x)))))))

   ;; Arguments shall be trimmed to local file names.
   (eval
    `(defadvice ,(intern (format "gud-%s-massage-args" x))
       (before
	,(intern (format "tramp-advice-gud-%s-massage-args" x))
	(file args) activate)
       "Invoke `tramp-gud-massage-args' for Tramp files."
       (when (eq (tramp-find-foreign-file-name-handler
		  (expand-file-name (ad-get-arg 0)))
		 'tramp-sh-file-name-handler)
	 (ad-set-arg 0 (car (tramp-gud-massage-args (list (ad-get-arg 0)))))
	 (ad-set-arg 1 (tramp-gud-massage-args (ad-get-arg 1))))))
   (eval
    `(add-hook
      'tramp-util-unload-hook
      (lambda ()
	(ad-unadvise (quote ,(intern (format "gud-%s-massage-args" x))))))))

 ;; So far, I've tested only gdb and perldb.
 ;; (X)Emacs
 '(gdb sdb dbx xdb perldb pdb
 ;; Emacs
   jdb bashdb))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Files to be compared in ediff.el shall be local.

(defadvice ediff-exec-process
  (before tramp-advice-before-ediff-exec-process
	  (program buffer synch options &rest files) activate)
  "Make FILES local."
  (setq files
	(mapcar
	 (lambda (x) (when (stringp x) (or (file-local-copy x) x))) files)))
(eval
 `(add-hook
   'tramp-util-unload-hook
   (lambda () (ad-unadvise 'ediff-exec-process))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Several packages expect that the processes run locally.

(mapc
 (lambda (x)
   (eval
    `(defadvice ,x
       (around ,(intern (format "tramp-advice-%s" x)) activate)
       ,(format "Run `%s' on a local default directory." x)
       (let ((default-directory
	       (unhandled-file-name-directory default-directory)))
	 ad-do-it)))
   (eval
    `(add-hook
      'tramp-util-unload-hook
      (lambda () (ad-unadvise (quote ,x))))))

 '(browse-url-default-windows-browser
   browse-url-default-macosx-browser browse-url-netscape
   browse-url-mozilla browse-url-firefox browse-url-galeon
   browse-url-epiphany browse-url-gnome-moz browse-url-mosaic
   browse-url-grail browse-url-cci browse-url-iximosaic
   browse-url-w3-gnudoit browse-url-lynx-xterm
   browse-url-lynx-emacs browse-url-mmm browse-url-generic
   browse-url-kde
   ediff-exec-process
   gnus-1
   ispell-start-process
   jka-compr-call-process jka-compr-partial-uncompress))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PC-expand-many-files needs special care-

;; This function contributed by Ed Sabol
(defun tramp-PC-expand-many-files (name)
  "Like `PC-expand-many-files' for Tramp files."
  (with-parsed-tramp-file-name name nil
    (save-match-data
      (if (or (string-match "\\*" name)
	      (string-match "\\?" name)
	      (string-match "\\[.*\\]" name))
	  (progn
	    (let (bufstr)
	      ;; CCC: To do it right, we should quote certain characters
	      ;; in the file name, but since the echo command is going to
	      ;; break anyway when there are spaces in the file names, we
	      ;; don't bother.
	      ;;-(let ((comint-file-name-quote-list
	      ;;-       (set-difference tramp-file-name-quote-list
	      ;;-                       '(?\* ?\? ?[ ?]))))
	      ;;-  (tramp-send-command
	      ;;-   method user host
	      ;;-   (format "echo %s" (comint-quote-filename localname))))
	      (tramp-send-command v (format "echo %s" localname))
	      (setq bufstr (buffer-substring (point-min) (point-at-eol)))
	      (with-current-buffer (tramp-get-buffer v)
		(goto-char (point-min))
		(if (string-equal localname bufstr)
		    nil
		  (insert "(\"")
		  (while (search-forward " " nil t)
		    (delete-backward-char 1)
		    (insert "\" \""))
		  (goto-char (point-max))
		  (delete-backward-char 1)
		  (insert "\")")
		  (goto-char (point-min))
		  (mapcar
		   (lambda (x) (tramp-make-tramp-file-name method user host x))
		   (read (current-buffer)))))))
	(list (expand-file-name name))))))

(when (functionp 'PC-expand-many-files)
  (eval-after-load "complete"
    '(progn
       (defadvice PC-expand-many-files
	 (around tramp-advice-PC-expand-many-files (name) activate)
	 "Invoke `tramp-PC-expand-many-files' for Tramp files."
	 (if (tramp-tramp-file-p name)
	     (setq ad-return-value (tramp-PC-expand-many-files name))
	   ad-do-it))
       (add-hook 'tramp-unload-hook
		 (lambda () (ad-unadvise 'PC-expand-many-files))))))

(add-hook 'tramp-unload-hook
	  (lambda ()
	    (unload-feature 'tramp-util 'force)))

(provide 'tramp-util)

;;; tramp-util.el ends here

;; Local Variables:
;; mode: Emacs-Lisp
;; coding: utf-8
;; End:
