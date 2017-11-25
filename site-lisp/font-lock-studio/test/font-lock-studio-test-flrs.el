;;; font-lock-studio-test-flrs.el --- Real-world tests for font-lock-studio.

;; Copyright (C) 2016-2017 Anders Lindgren

;; Author: Anders Lindgren
;; Keywords: faces, tools

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is test for the package `font-lock-studio' using source code
;; provided by `font-lock-regression-suite', using the tools
;; `font-lock-profiler' and `faceup'.
;;
;; The test cases will fontify the source files with Font Lock Studio
;; and with the normal Font Lock engine and check that the result is
;; idnetical, and that each individual.
;;
;; The tests use the `ert' test framework, which is a part of Emacs.

;; Usage:
;;
;; Add test cases:
;;
;; `M-x font-lock-studio-test-flrs-add-ert-cases RET'.
;;
;; Run the test cases, for example:
;;
;; `M-x ert RET t RET'.

;;; Code:

(require 'font-lock-regression-suite)

;; TODO: Break out common code to a new file, say
;; `font-lock-studio-test-helper'.
(require 'font-lock-studio-test)

(defun font-lock-studio-test-flrs-add-ert-cases ()
  "Generate a number of ERT testcases.

The test cases checks that the end result is the same with normal
and profiled font-lock keywords. The source files are provided by
`font-lock-regression-suite'."
  (interactive)
  (font-lock-regression-suite-each-src-ref-file
   (lambda (name
            src-file
            ref-file
            modes)
     (when (file-exists-p ref-file)
       (eval
        `(ert-deftest ,(intern (concat "font-lock-studio-test-flrs--" name))
             ()
           (with-temp-buffer
             (insert-file-contents ,src-file)
             (skip-unless (font-lock-regression-suite-apply-modes
                           (quote ,modes)))
             (font-lock-studio-test-font-lock-vs-studio-with-log nil))))))))

(provide 'font-lock-studio-test-flrs)

;;; font-lock-studio-test-flrs.el ends here
