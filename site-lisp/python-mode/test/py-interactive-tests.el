;;; py-interactive-tests.el --- Tests expected to succeed interactively -*- lexical-binding: t; -*-

;; Copyright (C) 2015  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@online.de>
;; Keywords: lisp

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

;;; Commentary:

;;

;;; Code:

(defun py-shell-complete-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
impo")))
    (py-bug-tests-intern 'py-shell-complete-base arg teststring)))

(defun py-shell-complete-base ()
  (when (and (interactive-p) py-debug-p) (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (sit-for 0.1 t)
  (py-shell-complete)
  (sit-for 0.1)
  (assert (looking-back "import") nil "py-shell-complete-test failed"))

(ert-deftest py-ert-execute-statement-fast-1 ()
  (py-test-with-temp-buffer-point-min
      "print(1)"
    (let ((py-fast-process-p t)
	  (py-return-result-p t)
	  py-result py-store-result-p)
      (py-execute-statement)
      (should (string= "1" py-result)))))

(ert-deftest py-ert-execute-statement-fast-2 ()
  (py-test-with-temp-buffer-point-min
      "print(2)"
    (let ((py-fast-process-p t)
	  (py-return-result-p t)
	  py-result py-store-result-p)
      (py-execute-statement-fast)
      (should (string= "2" py-result)))))

(ert-deftest py-ert-fast-complete-1 ()
  (py-test-with-temp-buffer
      "obj"
    (let ((py-return-result-p t)
	  py-result py-store-result-p)
      (when py-debug-p (switch-to-buffer (current-buffer)))
      (py-fast-complete)
      (should (eq (char-before) 40)))))

(ert-deftest py-shell-complete-in-dedicated-shell ()
  (let (erg
	;; py-split-window-on-execute
	py-switch-buffers-on-execute-p)
    (with-temp-buffer
      (python-mode)
      (setq erg (python-dedicated))
      (with-current-buffer erg
	(goto-char (point-max))
	;; (when py-debug-p (switch-to-buffer (current-buffer)))
	;; (switch-to-buffer (current-buffer))
	(insert "pri")
	(sit-for 1 t)
	(call-interactively 'py-indent-or-complete)
	(sit-for 0.1 t)
	(should (or (eq 40 (char-before))
		    ;; python may just offer print(
		    (buffer-live-p (get-buffer  "*Python Completions*"))))
      (py-kill-buffer-unconditional erg)))))

(provide 'py-interactive-tests)
;;; py-interactive-tests.el ends here
