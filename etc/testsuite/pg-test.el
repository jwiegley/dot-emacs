;;; pg-test.el --- Simple test framework for Proof General.

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;;; Commentary:
;;

;;; Code:

(defconst pg-test-buffer "** PG test output **")

(defvar pg-test-total-success-count  0)
(defvar pg-test-total-fail-count 0)

(defvar pg-test-suite-success-count 0)
(defvar pg-test-suite-fail-count 0)

;; A test suite is a list of tests.
(defvar pg-test-suite-table nil)

(defvar pg-current-test-suite nil)

(defun pg-set-test-suite (name)
  (setq pg-current-test-suite name)
  (unless (assoc name pg-test-suite-table)
    (setq pg-test-suite-table
	  ;; Add an empty subtable
	  (cons (cons name nil) pg-test-suite-table))))

(defun pg-clear-test-suite (name)
  (setq pg-test-suite-table
	(remassoc name pg-test-suite-table)))


(defmacro pg-test-eval (expr result)
  "Add test (equal (eval EXPR) RESULT) to current test suite."
  (let* ((suite    (assoc pg-current-test-suite pg-test-suite-table))
	 (testnum  (length suite))
	 (name     (concat pg-current-test-suite "." (int-to-string testnum))))
    (setcdr suite (cons (list name 'eval expr result) (cdr suite)))
    ;; Result is number of this test in suite
    testnum))

(defun pg-execute-test (test)
  (let ((name (car test))
	(type (cadr test)))
    (cond
     ((eq type 'eval)
      (let ((expr       (nth 2 test))
	    (goodresult (nth 3 test))
	    result errorresult exn)
      (condition-case exn
	  (setq result (eval expr))
	;; FIXME: add negative tests here, that exns _are_ raised.
	(t (setq errorresult 
		 (format " %s failed: error signalled: %s %s\n" 
			 name (car exn) (cdr exn)))))
      (or errorresult
	  (unless (equal goodresult result)
	    (setq errorresult
		  (format " %s failed: exprected result %s, got %s\n"
			  name goodresult result))))
      (if errorresult
	  (incf pg-test-suite-fail-count)
	(incf pg-test-suite-success-count)
	(setq errorresult (format " %s succeeded.\n" name)))
      ;; Return string
      errorresult))
     ;; No other types at the moment
     (t
      (error "Eek! unrecognized test type."))
     )))

(defun pg-execute-test-suite (name)
  (interactive (list
		(completing-read "Run test suite: "
				 pg-test-suite-table)))
  (setq pg-test-suite-success-count 0)
  (setq pg-test-suite-fail-count 0)
  (save-excursion
    (set-buffer (get-buffer-create pg-test-buffer))
    (insert "=================================================================\n")
    (insert "TEST SUITE: " name "\n") 
    (insert "=================================================================\n")
    (apply 'insert
     (mapcar 'pg-execute-test 
	     (reverse (cdr-safe
		       (assoc name pg-test-suite-table)))))
    (insert (format
	     "\nTotal successful tests: %s, failed tests: %s\n\n"
	     pg-test-suite-success-count   pg-test-suite-fail-count)))
  (setq pg-test-total-success-count 
	(+ pg-test-suite-success-count pg-test-total-success-count))
  (setq pg-test-total-fail-count 
	(+ pg-test-suite-fail-count pg-test-total-fail-count)))

(defun pg-execute-all-tests ()
  (interactive)
  (pop-to-buffer
   (get-buffer-create pg-test-buffer))
  (erase-buffer)
  (sit-for 0)
  (setq pg-test-total-success-count 0)
  (setq pg-test-total-fail-count 0)
  (mapcar 'pg-execute-test-suite (mapcar 'car pg-test-suite-table)))






(provide 'pg-test)
;; End of `pg-test.el'
