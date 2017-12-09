;;; ob-jq.el --- org-babel functions for jq scripts

;; Copyright (C) 2015 Bjarte Johansen

;; Author: Bjarte Johansen
;; Keywords: literate programming, reproducible research
;; Homepage: http://www.github.com/ljos/jq-mode
;; Version: 0.1.0

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with jq-mode. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Provides a way to evaluate jq scripts in org-mode.

;;; Usage:

;; Add to your Emacs config:

;; (org-babel-do-load-languages
;;  'org-babel-load-languages
;;  '((jq . t)))

;;; Code:
(require 'ob)
(require 'jq-mode)

(defvar org-babel-jq-command "jq"
  "Name of the jq executable command.")

(defvar org-babel-tangle-lang-exts)
(add-to-list 'org-babel-tangle-lang-exts '("jq" . "jq"))

(defconst org-babel-header-args:jq
  '((:in-file  . :any)
    (:cmd-line . :any))
  "Jq specific header arguments.")

(defvar org-babel-default-header-args:jq '()
  "Default arguments for evaluating a jq source block.")

(defun org-babel-execute:jq (body params)
  "Execute a block of jq code with org-babel.  This function is
called by `org-babel-execute-src-block'"
  (message "executing jq source code block")
  (let* ((result-params (cdr (assq :result-params params)))
	 (cmd-line (cdr (assq :cmd-line params)))
	 (in-file (cdr (assq :in-file params)))
	 (code-file (let ((file (org-babel-temp-file "jq-")))
		      (with-temp-file file
			(insert body)
			file)))
	 (stdin (let ((stdin (cdr (assq :stdin params))))
		  (when stdin
		    (let ((tmp (org-babel-temp-file "jq-stdin-"))
			  (res (org-babel-ref-resolve stdin)))
		      (with-temp-file tmp
			(insert res)
			tmp)))))
	 (cmd (mapconcat #'identity
			 (remq nil
			       (list org-babel-jq-command
				     (format "--from-file \"%s\"" code-file)
				     cmd-line
				     in-file))
			 " ")))
    (org-babel-reassemble-table
     (let ((results
	    (cond
	     (stdin (with-temp-buffer
		      (call-process-shell-command cmd stdin (current-buffer))
		      (buffer-string)))
	     (t (org-babel-eval cmd "")))))
       (when results
	 (org-babel-result-cond result-params
	   results
	   (let ((tmp (org-babel-temp-file "jq-results-")))
	     (with-temp-file tmp
	       (insert results))
	     (org-babel-import-elisp-from-file tmp)))))
     (org-babel-pick-name (cdr (assq :colname-names params))
			  (cdr (assq :colnames params)))
     (org-babel-pick-name (cdr (assq :rowname-names params))
			  (cdr (assq :rownames params))))))

(provide 'ob-jq)
;;; ob-jq.el ends here
