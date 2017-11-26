;;; outorg-test.el --- ERT suite for outorg.el

;; Maintainer: Adam Porter
;; Version: 2.0
;; URL: https://github.com/alphapapa/outorg

;;;; MetaData
;;   :PROPERTIES:
;;   :copyright: Thorsten Jolitz
;;   :copyright-years: 2014+
;;   :version:  2.0
;;   :licence:  GPL 2 or later (free software)
;;   :licence-url: http://www.gnu.org/licenses/
;;   :part-of-emacs: no
;;   :maintainer: Adam Porter
;;   :inspiration:  test-org-element.el
;;   :keywords: emacs org-mode ert buffer
;;   :git-repo: https://github.com/alphapapa/outorg
;;   :git-clone: git://github.com/alphapapa/outorg.git
;;   :END:


;;; Requires

(require 'ert-buffer)

;;; Dependencies

(unless (featurep 'outorg)
  (signal 'missing-test-dependency "outorg"))
(unless (featurep 'ert-buffer)
  (signal 'missing-test-dependency "ert-buffer"))

;;; Variables

(defvar outorg-test-saved-org-cmd ()
  "Org command to be used in ERT test.")

(defvar outorg-test-saved-major-mode nil
  "Major mode to be used in ERT test.")

(defvar outorg-test-saved-prefix-arg nil
  "Prefix arg to be used in ERT test.")

;; (defvar outorg-test-with-return-p nil
;;   "Test return values too.")

;; (defvar outorg-test-with-explain-p nil
;;   "Explain test results.")


;;; Functions

;; (defun outorg-test-toggle-with-return ()
;;   "Toggles the value of boolean var.
;; If `outorg-test-with-return-p' is non-nil, a test that includes
;; expected and actual return values is called."
;;   (interactive)
;;   (if outorg-test-with-return-p
;;       (setq outorg-test-with-return-p nil)
;;     (setq outorg-test-with-return-p t))
;;   (message "Outorg-test: include return values is %s"
;; 	   outorg-test-with-return-p))

;; (defun outorg-test-toggle-with-explain ()
;;   "Toggles the value of boolean var.
;; If `outorg-test-with-explain-p' is non-nil, a test that explains
;; results is called."
;;   (interactive)
;;   (if outorg-test-with-explain-p
;;       (setq outorg-test-with-explain-p nil)
;;     (setq outorg-test-with-explain-p t))
;;   (message "Outorg-test: explain results is %s"
;; 	   outorg-test-with-explain-p))

(defun outorg-test-cmd ()
  "Command to be used inside `ert-deftest'"
  (interactive)
  (let ((pref-arg '(4))
	saved-undo-tree)
    ;; set major mode in buffer copy
    (if (eq outorg-test-saved-major-mode 'ess-mode)
	;; special case R-mode
	(funcall 'R-mode)
      (funcall outorg-test-saved-major-mode))
    ;; (funcall outorg-test-saved-major-mode)
    ;; 1ST ROUND: convert buffer from source to org
    (outorg-edit-as-org
     outorg-test-saved-prefix-arg)
    ;; activate undo-tree-mode
    (undo-tree-mode t)
    ;; avoid failing tests due to moving point
    (save-excursion
      ;; call org cmd (and modify buffer)
      (call-interactively
       outorg-test-saved-org-cmd))
    ;; necessary (?) HACK to fill buffer-undo-tree
    (undo-tree-visualize)
    (undo-tree-visualizer-quit)
    ;; store buffer-undo-tree
    (setq saved-undo-tree buffer-undo-tree)
    ;; reconvert buffer from org to source
    (outorg-copy-edits-and-exit)
    ;; 2ND ROUND: convert buffer from source to org (again)
    (outorg-edit-as-org 
     outorg-test-saved-prefix-arg)
    ;; activate undo-tree-mode
    (undo-tree-mode t)
    ;; undo changes by org cmd
    (org-set-local 'buffer-undo-tree saved-undo-tree)
    (undo-tree-undo (undo-tree-count buffer-undo-tree))
    ;; reconvert buffer from org to source
    (outorg-copy-edits-and-exit)))


(defun outorg-test-run-ert (org-cmd &optional USE-PREFIX-ARG-P RETURN-P EXPLAIN-P)
  "Prepare and run ERT test.

This command records the major-mode of current-buffer in global
variable `outorg-test-saved-major-mode', the given
prefix-argument in `outorg-test-saved-prefix-arg' (if
USE-PREFIX-ARG-P is non-nil) and the given ORG-CMD in
`outorg-test-saved-org-cmd', and it copies the content of current
buffer into a temporary *outorg-test-buffer* and sets its
major-mode.

After this preparation it calls either

 - `outorg-test-conversion-with-equal' :: RETURN-P and EXPLAIN-P
      are both nil

 - `outorg-test-conversion-with-equal-explain' :: RETURN-P is
      nil, EXPLAIN-P is non-nil

 - `outorg-test-conversion-with-equal-return' :: RETURN-P is
      non-nil, EXPLAIN-P is nil

 - `outorg-test-conversion-with-equal-return-explain' :: RETURN-P
      and EXPLAIN-P are both non-nil

depending on the values of optional function arguments RETURN-P
and EXPLAIN-P or on `outorg-test-with-return-p' and
`outorg-test-with-explain-p'. All of these tests make use of the
*outorg-test-buffer* and the three global variables mentioned
above."
  (interactive
   (if current-prefix-arg
       (list
	(read-command "Org Command: ")
	(y-or-n-p "Use prefix-arg for calling outorg ")
	(y-or-n-p "Test return values ")
	(y-or-n-p "Explain test results "))
     (list (read-command "Org Command: "))))
  (let ((old-buf (current-buffer))
	(maj-mode (outorg-get-buffer-mode)))
    ;; (ret-p (or RETURN-P outorg-test-with-return-p))
    ;; (exp-p (or EXPLAIN-P outorg-test-with-explain-p)
    ;; (use-pref-arg-p (or USE-PREFIX-ARG-P
    ;; 		    outorg-test-with-return-p))))
    ;; necessary (?) HACK
    (setq outorg-test-saved-org-cmd org-cmd)
    (setq outorg-test-saved-major-mode maj-mode)
    (when USE-PREFIX-ARG-P
      (setq outorg-test-saved-prefix-arg current-prefix-arg))
    (save-restriction
      (widen)
      (with-current-buffer
	  (get-buffer-create "*outorg-test-buffer*")
	(erase-buffer)
	(insert-buffer-substring old-buf)
	(if (eq maj-mode 'ess-mode)
	    ;; special case R-mode
	    (funcall 'R-mode)
	  (funcall outorg-test-saved-major-mode))
	;; (funcall maj-mode)
	;; (call-interactively 'ert-run-tests-interactively)
	(cond
	 ((and (org-string-nw-p RETURN-P)
	       (org-string-nw-p EXPLAIN-P))
	  (funcall
	   'ert-run-test ;s-interactively
	   "outorg-test-conversion-with-equal-return-explain"))
	 ((org-string-nw-p RETURN-P)
	  (funcall
	   'ert-run-test ;s-interactively
	   "outorg-test-conversion-with-equal-return"))
	 ((org-string-nw-p EXPLAIN-P)
	  (funcall
	   'ert-run-test ;s-interactively
	   "outorg-test-conversion-with-equal-explain"))
	 (t
	  (funcall
	   'ert-run-tests-interactively
	   "outorg-test-conversion-with-equal")))))))


;;; Tests

(ert-deftest outorg-test-conversion-with-equal ()
  "Test outorg conversion to and from Org.

This test assumes that it is called via user command
`outorg-test-run-ert' with point in the original programming
language buffer to be converted to Org-mode, and with the prefix
argument that should be used for `outorg-edit-as-org'. It further
relies on the `ert-buffer' library for doing its work.

Since outorg is about editing (and thus modifying) a buffer in
Org-mode, defining the expected outcome manually would be bit
cumbersome. Therefore so called 'do/undo' tests (invented and
named by the author) are introduced:

 - do :: convert to org, save original state before editing, edit
         in org, produce and save the diffs between original and
         final state, convert back from org

 - undo :: convert to org again, undo the saved diffs, convert
           back from org

After such an do/undo cyle the test buffer should be in exactly
the same state as before the test, i.e.

 - buffer content after the test should be string-equal to buffer
   content before

 - point should be in the same position

 - the mark should be in the same position (or nil)

These are actually the three criteria checked by the 'ert-buffer'
library, and when one or more of the checks returns nil, the ert
test fails.

This test is a one-size-fits-all test for outorg, since it
allows, when called via command `outorg-test-run-ert', to execute
arbitrary Org-mode commands in the *outorg-edit-buffer* and undo
the changes later on, checking for any undesired permanent side
effects of the conversion process per se."
  (let ((curr-buf-initial-state
	 (with-current-buffer "*outorg-test-buffer*"
	   (ert-Buf-from-buffer))))
    (should
     (ert-equal-buffer
      (outorg-test-cmd)
      curr-buf-initial-state
      t))))

;; (ert-deftest outorg-test-conversion-with-equal-return ()
;;   "Test outorg conversion to and from Org.

;; This test takes return values into account. See docstring of
;; `outorg-test-conversion-with-equal' for more info."
;;   (let ((curr-buf-initial-state
;; 	 (with-current-buffer "*outorg-test-buffer*"
;; 	   (ert-Buf-from-buffer))))
;;     (should
;;      (ert-equal-buffer-return
;;       (outorg-test-cmd)
;;       curr-buf-initial-state
;;       t nil))))

;; (ert-deftest outorg-test-conversion-with-equal-explain ()
;;   "Test outorg conversion to and from Org.

;; This test explains results. See docstring of
;; `outorg-test-conversion-with-equal' for more info."
;;   (let ((curr-buf-initial-state
;; 	 (with-current-buffer "*outorg-test-buffer*"
;; 	   (ert-Buf-from-buffer))))
;;     (should
;;      (ert-equal-buffer-explain
;;       (outorg-test-cmd)
;;       curr-buf-initial-state
;;       t))))

;; (ert-deftest outorg-test-conversion-with-equal-return-explain ()
;;   "Test outorg conversion to and from Org.

;; This test takes return values into account and explains
;; results. See docstring of `outorg-test-conversion-with-equal' for
;; more info."
;;   (let ((curr-buf-initial-state
;; 	 (with-current-buffer "*outorg-test-buffer*"
;; 	   (ert-Buf-from-buffer))))
;;     (should
;;      (ert-equal-buffer-return-explain
;;       (outorg-test-cmd)
;;       curr-buf-initial-state
;;       t nil))))


;;; Run hooks and provide

(provide 'outorg-test)

;;; outorg-test.el ends here
