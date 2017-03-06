;;; nix-buffer.el --- Set up buffer environments with nix

;; Copyright (C) 2016, 2017 Shea Levy

;; Author: Shea Levy
;; URL: https://github.com/shlevy/nix-buffer/tree/master/
;; Version: 3.0.0
;; Package-Requires: ((f "0.17.3") (emacs "24.4"))

;;; Commentary:

;; This package provides 'nix-buffer', to modify your buffer
;; according to a directory-local nix expression.  Think of it as
;; nix-shell for Emacs.  See the documentation for 'nix-buffer' for
;; more details.

;; It may be desirable to run 'nix-buffer' before 'normal-mode' is
;; called so it affects all modes.

;;; Code:

(require 'f)
(require 'subr-x)

(defgroup nix-buffer nil "Customization for nix-buffer."
  :prefix "nix-buffer-"
  :group 'environment
  :package-version '('nix-buffer . "2.3.0"))

(defun nix-buffer--directory-name-setter (opt val)
  "Defcustom setter for nix-buffer-directory-name.
OPT The option we're setting.

VAL The value it's being set to."
  (nix-buffer-update-directory-name val))

(defcustom nix-buffer-directory-name
  (locate-user-emacs-file "nix-buffer")
  "Path where nix-buffer keeps its data.
To update this variable outside of Customize, please use
'nix-buffer-update-directory-name'."
  :group 'nix-buffer
  :type '(directory)
  :set 'nix-buffer--directory-name-setter
  :initialize 'custom-initialize-default
  :risky t)

(defvar nix-buffer--trust-exprs-file
  (f-join nix-buffer-directory-name "trusted-exprs"))

(defun nix-buffer--load-trusted-exprs ()
  "Load the trusted nix-buffer exprs."
  (let ((tbl (ignore-errors
	       (with-temp-buffer
		 (insert-file-contents-literally
		  nix-buffer--trust-exprs-file)
		 (read (current-buffer))))))
    (if (hash-table-p tbl)
	tbl
      (make-hash-table :test 'equal))))

(defvar nix-buffer--trusted-exprs (nix-buffer--load-trusted-exprs))

(defun nix-buffer-update-directory-name (path)
  "Update the nix-buffer state directory.
PATH The path to store the nix-buffer state."
  (setq nix-buffer-directory-name path)
  (setq nix-buffer--trust-exprs-file
	(f-join nix-buffer-directory-name "trusted-exprs"))
  (setq nix-buffer--trusted-exprs (nix-buffer--load-trusted-exprs)))

(defun nix-buffer-unload-function ()
  "Save state on unload."
  (ignore-errors (make-directory nix-buffer-directory-name t))
  (with-temp-buffer
    (prin1 nix-buffer--trusted-exprs (current-buffer))
    (write-region nil nil nix-buffer--trust-exprs-file))
  nil)

(defun nix-buffer--unique-filename (path)
  "Create a unix-safe filename from an entire path.
PATH the path to generate the name from."
  (replace-regexp-in-string "[|\\/]"
			    (lambda (str)
			      (if (equal str "/")
				  "|"
				(concat "\\\\" str)))
			    path))

(defun nix-buffer--query-safety (expr-file lisp-file)
  "Ask the user whether to trust a Lisp file.
EXPR-FILE The nix expression leading to this file.

LISP-FILE The file in question."
  (let ((res (yes-or-no-p (concat expr-file
				  " resulted in unknown Lisp file "
				  lisp-file
				  "; trust it? "))))
    (puthash lisp-file res nix-buffer--trusted-exprs)
    res))

(defvar nix-buffer-after-load-hook nil
  "Hook run after nix-buffer loads an expression.")

(defun nix-buffer--load-result (expr-file out)
  "Load the result of a nix-buffer build, checking for safety.
EXPR-FILE The nix expression being built.

OUT The build result."
  (when (or (gethash out nix-buffer--trusted-exprs)
	    (nix-buffer--query-safety expr-file out))
    (load-file out)
    (run-hooks 'nix-buffer-after-load-hook)))

(defun nix-buffer--sentinel
    (out-link last-out expr-file user-buf err-buf process event)
  "Handle the results of the nix build.
OUT-LINK The path to the output symlink.

LAST-OUT The previous build result, if any.

EXPR-FILE The nix expression being built.

USER-BUF The buffer to apply the results to.

ERR-BUF The standard error buffer of the nix-build

PROCESS The process whose status changed.

EVENT The process status change event string."
  (unless (process-live-p process)
    (let ((out-buf (process-buffer process)))
      (progn
	(if (= (process-exit-status process) 0)
	    (let ((cur-out (with-current-buffer out-buf
			     (string-trim-right (buffer-string)))))
	      (if (string= "" cur-out)
		  (ignore-errors (delete-file out-link))
		(unless (string= last-out cur-out)
		  (with-current-buffer user-buf
		    (nix-buffer--load-result expr-file cur-out)))))
	  (with-current-buffer
	      (get-buffer-create "*nix-buffer errors*")
	    (insert "nix-build for nix-buffer for "
		    (buffer-name user-buf)
		    " "
		    (string-trim-right event)
		    " with error output: \n")
	    (insert-buffer-substring err-buf)
	    (pop-to-buffer (current-buffer))))
	(kill-buffer out-buf)
	(kill-buffer err-buf)))))

(defun nix-buffer--nix-build (root expr-file)
  "Start the nix build.
ROOT The path we started from.

EXPR-FILE The file containing the nix expression to build."
  (let* ((state-dir (f-join nix-buffer-directory-name
			    (nix-buffer--unique-filename root)))
	 (out-link (f-join state-dir "result"))
	 (current-out (file-symlink-p out-link))
	 (err (generate-new-buffer " nix-buffer-nix-build-stderr")))
    (progn
      (ignore-errors (make-directory state-dir t))
      (make-process
       :name "nix-buffer-nix-build"
       :buffer (generate-new-buffer " nix-buffer-nix-build-stdout")
       :command (list
		 "nix-build"
		 "--arg" "root" root
		 "--out-link" out-link
		 expr-file
		 )
       :noquery t
       :sentinel (apply-partially 'nix-buffer--sentinel
				  out-link
				  current-out
				  expr-file
				  (current-buffer)
				  err)
       :stderr err)
      (when current-out
	(nix-buffer--load-result expr-file current-out)))))

;;;###autoload
(defun nix-buffer ()
  "Set up the buffer according to the directory-local nix expression.
Looks for dir-locals.nix upward from the current directory.  If found,
asynchronously builds the derivation defined there with the 'root' arg
set to the current buffer file name or directory and evaluates the
resulting elisp if safe to do so.  'nix-buffer-after-load-hook' can be
used to detect when the elisp load occurs.

If we have previously built dir-locals.nix for the current file or
directory, the elisp corresponding to the last build is evaluated
synchronously and the new elisp is evaluated when the build completes,
unless the newly-built file is identical.  As such, the elisp
generated by dir-locals.nix should be written with multiple
evaluations in mind.

Because in practice dir-locals.nix will always want to do things that
are unsafe in dir-locals.el (e.g. append to 'exec-path'), we don't
reuse that mechanism and instead just load the file as elisp.  Because
this allows arbitrary code execution, the first time we're asked to
load a particular store path we query the user to verify if it's safe
to load beforehand.

The Lisp code generated by dir-locals.nix should limit itself to
modifying buffer-local variables, but there is no actual enforcement
of this.  'setq-local' is your friend.

If dir-locals.nix does not evaluate to any derivations (e.g. it
evaluates to {}), then nothing is loaded and the cached result, if any,
is removed."
  (interactive)
  (let* ((root (or (buffer-file-name) default-directory))
	 (expr-dir (locate-dominating-file root "dir-locals.nix")))
    (when expr-dir
	 (let ((expr-file (f-expand "dir-locals.nix" expr-dir)))
	   (nix-buffer--nix-build root expr-file)))))

(add-hook 'kill-emacs-hook 'nix-buffer-unload-function)

(provide 'nix-buffer)

;;; nix-buffer.el ends here
