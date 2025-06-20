;;; gptel-tools --- Tools for use with gptel -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 19 Jun 2025
;; Version: 1.0
;; Keywords: ai gptel tools
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Code:

(require 'cl-lib)
(require 'gptel)

(defun find-functions-with-keyword (keywords)
  "Find functions containing all KEYWORDS in their name or docstring."
  (interactive "sEnter keyword: ")
  (let ((results '()))
    (mapatoms
     (lambda (symbol)
       (when (fboundp symbol)
         (let ((name (symbol-name symbol))
               (doc (ignore-errors (documentation symbol))))
           (when (or (cl-every #'(lambda (keyword)
                                   (string-match-p (regexp-quote keyword) name))
                               keywords)
                     (and doc (cl-every #'(lambda (keyword)
                                            (string-match-p (regexp-quote keyword) doc))
                                        keywords)))
             (push symbol results))))))
    (if results
        (with-temp-buffer
          (insert (format "Functions containing '%s':\n\n" keywords))
          (dolist (func (sort results (lambda (a b)
                                        (string< (symbol-name a)
                                                 (symbol-name b)))))
            (insert (format "%-40s %s\n"
                            (symbol-name func)
                            (or (car (split-string (or (documentation func) "")
                                                   "\n"))
                                "No documentation"))))
          (buffer-string))
      (format "No functions found containing '%s'" keyword))))

(gptel-make-tool
 :function #'find-functions-with-keyword
 :name "find_functions"
 :description "Find available functions whose name or definitions matches a set of keywords.

Call this tool in order to determine if a particular function is
available.  This can also help determine which functions are available on
the user's Emacs.  This tool is a good starting point for general
questions about Emacs, Elisp, and common built-in packages.

You will usually follow this call with a subsequent call to
`get_function_docstring' in order to learn more about how to call those
functions. This call is extremely cheap and should be used liberally."
 :args (list
        '(:name "keyword"
	        :type "array"
                :items (:type "string")
	        :description "Keywords used to lookup up defined functions"))
 :category "emacs"
 :confirm nil)

(defun get-function-docstring (name)
  "Return the documentation for a given function NAME."
  (let ((sym (intern-soft name)))
    (and sym
         (fboundp sym)
         (documentation sym))))

(gptel-make-tool
 :function #'get-function-docstring
 :name "get_function_docstring"
 :description "Return the documentation for a given function.
Call this tool in order to determine the arguments, convensations, and
return value of a particular function by name. This call is extremely
cheap and should be used liberally."
 :args (list
        '(:name "name"
	        :type "string"
                :description "Name of the function whose documentation is needed"))
 :category "emacs"
 :confirm nil)

(gptel-make-tool
 :function (lambda (x y)
             (format "The value of x and y multiplied is: %s" (* x y)))
 :name "multiply_numbers"
 :description "Multiply two numbers together"
 :args (list '(:name "x"
	             :type "integer"
	             :description "The first number to be multiplied")
             '(:name "y"
	             :type "integer"
	             :description "The second number to be multiplied"))
 :category "math"
 :confirm nil)

(gptel-make-tool
 :function (lambda (path filename content)
             (let ((full-path (expand-file-name filename path)))
               (with-temp-buffer
                 (insert content)
                 (write-file full-path))
               (format "Created file %s in %s" filename path)))
 :name "create_file"
 :description "Create a new file with the specified content"
 :args (list '(:name "path"
	             :type "string"
	             :description "The directory where to create the file")
             '(:name "filename"
	             :type "string"
	             :description "The name of the file to create")
             '(:name "content"
	             :type "string"
	             :description "The content to write to the file"))
 :category "filesystem"
 :confirm t)

(provide 'gptel-tools)

;;; gptel-tools.el ends here
