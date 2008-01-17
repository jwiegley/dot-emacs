;;; pg-autotest.el --- Simple testing framework for Proof General
;;
;; Copyright (C) 2005 LFCS Edinburgh, David Aspinall.
;; Authors:   David Aspinall
;;
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; TODO:
;; -- fix failure handling for scriptfile
;; -- force re
;; -- add macros for defining test suites
;; -- add more precise functional tests to check results
;; -- add negative tests
;; -- output test results to stdout
;; 
;; $Id$

(require 'proof)

;;; Commentary:
;; 

;;; Code:
(defvar pg-autotest-success t)		;; success unless error caught

;;; Some utilities

(defun pg-autotest-find-file (file)
  "Find FILE (relative to `proof-home-directory') and redisplay."
  (let* ((name   (concat proof-home-directory file)))
    (if (file-exists-p name)
	(find-file name)
      (error (format "autotest: requested file %s does not exist" name)))))

(defun pg-autotest-find-file-restart (file)
  "Find FILE and make ready to script there."
  ;; Ensure scripting off; if completely full, will register, otherwise retract
  (proof-deactivate-scripting-auto)
  (pg-autotest-find-file file)
  (goto-char (point-min))
  (unless (proof-locked-region-empty-p)
    ;; Should retract and unregister if was completely full
    (proof-goto-point))
  (pg-autotest-assert-unprocessed file))

;;; Invoke a test

(defmacro pg-autotest (fn &rest args)
  `(condition-case err
       (apply (intern (concat "pg-autotest-" (symbol-name (quote ,fn))))
	      (list ,@args))
     (error
      (progn
	(setq pg-autotest-success nil)
	(princ (format "Error in test %s: %s" (symbol-name (quote ,fn))
		       err)))))) ;; display-error stdout?



;;; The tests proper

(defun pg-autotest-script-wholefile (file)
  "Load FILE and script line-by-line, waiting a second between each line.
An error is signalled if scripting doesn't complete."
  (pg-autotest-find-file-restart file)
  (save-excursion
    (let ((making-progress t) last-locked-end)
      (while making-progress
	(setq last-locked-end (proof-locked-end))
	(goto-char last-locked-end)
	(save-current-buffer
	  (proof-assert-next-command-interactive)
	  (proof-shell-wait))
	(goto-char (proof-queue-or-locked-end))
	(setq making-progress (> (point) last-locked-end))
	(sit-for 1))))
  (pg-autotest-assert-processed file))

(defun pg-autotest-retract-file (file)
  (save-excursion
    (pg-autotest-find-file file)
    (proof-retract-buffer)
    (sit-for 1)))

(defun pg-autotest-assert-processed (file)
  "Check that FILE has been fully processed."
  (save-excursion
    (pg-autotest-find-file file)
    (unless (proof-locked-region-full-p)
      (error (format "Locked region in file `%f' is not full" file)))))

(defun pg-autotest-assert-unprocessed (file)
  "Check that FILE has been fully unprocessed."
  (save-excursion
    (pg-autotest-find-file file)
    (unless (proof-locked-region-empty-p)
      (error (format "Locked region in file `%f' is not empty" file)))))

(defun pg-autotest-message (msg)
  "Give message MSG on std out & on display."
  (message msg)
  ;; FIXME: can we send to std out even if emacs is not batch mode?
  (print msg)
  (sit-for 1))

(defun pg-autotest-quit-prover ()
  "Exit prover process."
  (if (buffer-live-p proof-shell-buffer)
	(kill-buffer proof-shell-buffer)
    (error "No proof shell buffer to kill")))

(defun pg-autotest-finished ()
  "Exit Emacs returning Unix success 0 if all tests succeeded."
  (kill-emacs (if pg-autotest-success 0 1)))
    
    

(provide 'pg-autotest)
;;; pg-autotest.el ends here

