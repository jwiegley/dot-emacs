;;; ob-jq-test.el --- tests for ob-jq.el

;; Copyright (c) 2015 Bjarte Johansen
;; Authors: Bjarte Johansen

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'ert)
(require 'org-id)

(unless (featurep 'ob-jq)
  (signal 'missing-test-dependency "Support for jq code blocks"))

(defmacro ob-jq-test/test-src-block (name &rest body)
    (declare (indent 1))
    (let ((buf (make-symbol "buf"))
	  (visited-p (make-symbol "visited-p"))
	  (file-pos (make-symbol "file-pos"))
	  (active-session (make-symbol "active-session"))
	  (file "ob-jq-test.org"))
      `(let ((,visited-p (get-file-buffer ,file))
	     (,buf (find-file-noselect , file))
	     ,active-session)
	 (with-current-buffer ,buf
	   (unwind-protect
	       (save-match-data
		 (save-excursion
		   (goto-char (point-min))
		   (condition-case nil
		       (progn
			 (org-show-subtree)
			 (org-show-block-all))
		     (error nil))
		   (org-babel-goto-named-src-block ,(symbol-name name))
		   (save-excursion
		     (ignore-errors
		       (let* ((info (nth 2 (org-babel-get-src-block-info)))
			      (session (cdr (assq :session info)))
			      (bound (progn
				       (org-babel-previous-src-block)
				       (end-of-line)
				       (point))))
			 (setq ,active-session
			       (unless (string= "none" session)
				 session))
			 (goto-char (point-min))
			 (while (search-forward
				 (concat ":session " session) bound t)
			   (org-babel-execute-src-block)))))
		   (save-restriction ,@body)))
	     (unless ,visited-p
	       (kill-buffer ,buf))
	     (when ,active-session
	       (kill-buffer ,active-session)))))))

(ert-deftest ob-jq-test/simple-execution ()
  "Test simple execution of jq source block."
  (ob-jq-test/test-src-block simple-execution
    (should (string= "test" (org-babel-execute-src-block)))))
