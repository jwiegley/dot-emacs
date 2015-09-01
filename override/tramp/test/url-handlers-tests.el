;;; url-handlers-tests.el --- Tests of remote file access in url syntax

;; ~/src/emacs/src/emacs -L ~/src/tramp/test ~/src/tramp/test/url-handlers-tests.el -f eval-buffer -f url-handlers-test-all &

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Michael Albinus <michael.albinus@gmx.de>

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see `http://www.gnu.org/licenses/'.

;;; Commentary:

;; Some of the tests require access to a remote host files.  Since
;; this could be problematic, a mock-up connection method "mock" is
;; used.  Emulating a remote connection, it simply calls "sh -i".
;; Tramp's file name handlers still run, so this test is sufficient
;; except for connection establishing.

;; If you want to test a real Tramp connection, set
;; $REMOTE_TEMPORARY_FILE_DIRECTORY to a suitable value in order to
;; overwrite the default value.  If you want to skip tests accessing a
;; remote host, set this environment variable to "/dev/null" or
;; whatever is appropriate on your system.

;; A whole test run can be performed calling the command
;; `url-handlers-test-all'.

;;; Code:

(require 'url-handlers)
(require 'ert)
;; We don't want checks during load of tramp-tests.el.
(let ((process-environment (copy-sequence process-environment)))
  (setenv "REMOTE_TEMPORARY_FILE_DIRECTORY" null-device)
  (load "tramp-tests" 'noerror 'nomessage))

;; There is no default value on w32 systems, which could work out of the box.
(defconst url-handlers-test-temporary-file-directory
  (cond
   ((getenv "REMOTE_TEMPORARY_FILE_DIRECTORY"))
   ((eq system-type 'windows-nt) null-device)
   (t ;; Prepare url-handlers.
    (add-to-list 'url-tramp-protocols "mock")
    (setq url-handler-regexp
	  (replace-regexp-in-string "ssh" "ssh\\\\|mock" url-handler-regexp))
    ;; Prepare Tramp.
    (add-to-list
     'tramp-methods
     '("mock"
       (tramp-login-program        "sh")
       (tramp-login-args           (("-i")))
       (tramp-remote-shell         "/bin/sh")
       (tramp-remote-shell-args    ("-c"))
       (tramp-connection-timeout   10)))
    ;; The mock url.
    (format "mock://%s" temporary-file-directory)))
  "Temporary directory for tests.")

(defmacro url-handlers--deftest (test docstring)
  "Define ert `url-handlers-TEST', derived from `tramp-TEST'."
  `(when (featurep 'tramp-tests)
     (ert-deftest ,(intern (concat "url-handlers-" (symbol-name test))) ()
       ,docstring
       (unwind-protect
	   (let ((tramp-test-temporary-file-directory
		  url-handlers-test-temporary-file-directory)
		 tramp--test-enabled-checked)
	     (url-handler-mode 1)
	     (tramp--instrument-test-case 10
	       (funcall
		(ert-test-body
		 (ert-get-test
		  (intern (concat "tramp-" (symbol-name ',test))))))))
	 (url-handler-mode 0)))))

(url-handlers--deftest test00-availability
  "Test availability of url-handlers functions.")

(url-handlers--deftest test07-file-exists-p
  "Check `file-exist-p', `write-region' and `delete-file'.")

(url-handlers--deftest test08-file-local-copy
  "Check `file-local-copy'.")

(url-handlers--deftest test09-insert-file-contents
  "Check `insert-file-contents'.")

(url-handlers--deftest test10-write-region
  "Check `write-region'.")

(url-handlers--deftest test11-copy-file
  "Check `copy-file'.")

(url-handlers--deftest test12-rename-file
  "Check `rename-file'.")

(url-handlers--deftest test13-make-directory
  "Check `make-directory'.
This tests also `file-directory-p' and `file-accessible-directory-p'.")

(url-handlers--deftest test14-delete-directory
  "Check `delete-directory'.")

(url-handlers--deftest test15-copy-directory
  "Check `copy-directory'.")

(url-handlers--deftest test16-directory-files
  "Check `directory-files'.")

(url-handlers--deftest test17-insert-directory
  "Check `insert-directory'.")

(url-handlers--deftest test18-file-attributes
  "Check `file-attributes'.
This tests also `file-readable-p' and `file-regular-p'.")

(url-handlers--deftest test19-directory-files-and-attributes
  "Check `directory-files-and-attributes'.")

(url-handlers--deftest test20-file-modes
  "Check `file-modes'.")

(url-handlers--deftest test21-file-links
  "Check `file-symlink-p'.
This tests also `make-symbolic-link', `file-truename' and `add-name-to-file'.")

(url-handlers--deftest test22-file-times
  "Check `set-file-times' and `file-newer-than-file-p'.")

(url-handlers--deftest test23-visited-file-modtime
  "Check `set-visited-file-modtime' and `verify-visited-file-modtime'.")

(url-handlers--deftest test24-file-name-completion
  "Check `file-name-completion' and `file-name-all-completions'.")

(url-handlers--deftest test25-load
  "Check `load'.")

(url-handlers--deftest test26-process-file
  "Check `process-file'.")

(url-handlers--deftest test27-start-file-process
  "Check `start-file-process'.")

(url-handlers--deftest test28-shell-command
  "Check `shell-command'.")

(url-handlers--deftest test29-vc-registered
  "Check `vc-registered'.")

(url-handlers--deftest test30-special-characters
  "Check special characters in file names.")

(url-handlers--deftest test32-asynchronous-requests
  "Check parallel asynchronous requests.
Such requests could arrive from timers, process filters and
process sentinels.  They shall not disturb each other.")

(defun url-handlers-test-all (&optional interactive)
  "Run all tests for \\[url-handlers]."
  (interactive "p")
  (funcall
   (if interactive 'ert-run-tests-interactively 'ert-run-tests-batch)
   "^url-handlers"))

(provide 'url-handlers-tests)
;;; url-handlers-tests.el ends here
