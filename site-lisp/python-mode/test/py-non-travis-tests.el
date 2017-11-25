;;; py-non-travis-tests.el --- non-travis tests

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

(ert-deftest py-complete-in-ipython-shell-test ()
  (let ((py-shell-name "ipython")
	(py-switch-buffers-on-execute-p t))
    (py-kill-buffer-unconditional "*IPython*")
    (ipython)
    (goto-char (point-max))
    (insert "pri")
    (py-indent-or-complete)
    (forward-word -1)
    (should (eq ?p (char-after)))))

(ert-deftest py-ert-script-buffer-appears-instead-of-python-shell-buffer-lp-957561-test ()
  (py-test-with-temp-buffer
      "#! /usr/bin/env python
 # -*- coding: utf-8 -*-
print(\"I'm the script-buffer-appears-instead-of-python-shell-buffer-lp-957561-test\")
"
     (let (py-switch-buffers-on-execute-p
	  (py-split-window-on-execute t))
      (delete-other-windows)
      (ipython)
      (sit-for 0.1)
      (py-execute-buffer-ipython)
      ;; (should (window-live-p (other-buffer)))
      (should (not (window-full-height-p))))))

(ert-deftest py-ert-socket-modul-completion-lp-1284141 ()
  (dolist (ele py-ert-test-default-executables)
    (when (buffer-live-p (get-buffer "*Python Completions*"))
      (py-kill-buffer-unconditional (get-buffer "*Python Completions*")))
    (py-test-with-temp-buffer
	"import socket\nsocket."
      (let ((py-debug-p t)
	    (py-shell-name ele)
	    oldbuf)
	(when py-debug-p (switch-to-buffer (current-buffer))
	      (font-lock-fontify-buffer))
	(py-indent-or-complete)
	(if (string-match "ipython" ele)
	    (sit-for 0.5)
	  (sit-for 0.1))
	(should (buffer-live-p (get-buffer "*Python Completions*")))
	(set-buffer "*Python Completions*")
	(switch-to-buffer (current-buffer))
	(goto-char (point-min))
	(sit-for 0.1)
	(prog1 (should (search-forward "socket."))
	  (py-kill-buffer-unconditional (current-buffer)))))))

(provide 'py-non-travis-tests)
;;; py-non-travis-tests.el ends here
