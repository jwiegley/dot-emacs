;;; py-ert-interactive-tests.el --- test interactively -*- lexical-binding: t; -*- 

;; Copyright (C) 2015  Andreas Röhler

;; Author: speck <andreas.roehler@online.de>
;; Keywords: languages

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

;;; Commentary: These tests fail in batch-mode

;;

;;; Code:

(ert-deftest py-ert-always-split-dedicated-lp-1361531-python2-test ()
  (py-test-with-temp-buffer
      "#! /usr/bin/env python2
# -*- coding: utf-8 -*-
print(\"I'm the py-always-split-dedicated-lp-1361531-python2-test\")"
    (delete-other-windows)
    (let* ((py-split-window-on-execute 'always)
	   (erg1 (progn (py-execute-statement-python2-dedicated) py-buffer-name))
	   (erg2 (progn (py-execute-statement-python2-dedicated) py-buffer-name)))
      (sit-for 1 t)
      (when py-debug-p (message "(count-windows) %s" (count-windows)))
      (should (< 2 (count-windows)))
      (py-kill-buffer-unconditional erg1)
      (py-kill-buffer-unconditional erg2)
      (py-restore-window-configuration))))

(ert-deftest py-ert-fill-paragraph-lp-1291493 ()
  (py-test-with-temp-buffer-point-min
      "if True:
    if True:
        if True:
            if True:
                pass

def foo():
    \"\"\"Foo\"\"\"
"
    (font-lock-fontify-buffer)
    (sit-for 0.1 t)

    (search-forward "\"\"\"")
    (fill-paragraph)
    (sit-for 0.1 t)
    (should (eq 7 (current-column)))))

(ert-deftest fill-paragraph-causes-wrong-indent-lp-1397936-test ()
  (py-test-with-temp-buffer
      "def foo():
    \"\"\"abc\"\"\"
"
    (when py-debug-p (switch-to-buffer (current-buffer))
	  (font-lock-fontify-buffer))
    (goto-char 20)
    (call-interactively 'fill-paragraph)
    (should (eq 4 (current-indentation)))))

(ert-deftest py-ert-imports-in-interactive-shell-lp-1290709 ()
  ""
  (when (buffer-live-p (get-buffer "*Python*")) (kill-buffer-unconditional (get-buffer "*Python*")))
  (when (buffer-live-p (get-buffer "*Python3*")) (kill-buffer-unconditional (get-buffer "*Python3*")))
  (let ((buffer (py-shell nil nil "python")))
    (set-buffer buffer)
    (delete-other-windows)
    (let ((full-height (window-height)))
  
      (py-send-string "import os" (get-buffer-process (current-buffer)))
      (sit-for 0.1)
      (goto-char (point-max))
      ;; (sit-for 0.1 t)
      (insert "print(os.get")
      (py-indent-or-complete)
      (sit-for 0.1 t)
      (should (< (window-height) full-height)))))

(ert-deftest py-ert-execute-region-lp-1294796 ()
  (py-test-with-temp-buffer-point-min
      "print(1)
"
    (let ((py-shell-name "ipython")
	  py-split-window-on-execute
	  py-switch-buffers-on-execute-p)
      (py-execute-buffer)
      (sit-for 0.5 t)
      (set-buffer "*IPython*")
  
      (goto-char (point-max))
      (should (search-backward "1")))))

(ert-deftest py-ipython-shell-test ()
  ""
  (let ((erg (ipython)))
    (sit-for 1)
    (should (bufferp (get-buffer erg)))
    (should (get-buffer-process erg))))

(ert-deftest py-ert-execute-expression-test ()
  (py-test-with-temp-buffer-point-min
      "print(\"I'm the py-execute-expression-test\")"
    (let ((py-shell-name "python"))
  
      (py-execute-expression)
      (sit-for 0.1 t)
      (set-buffer ert-test-default-buffer)
      ;; (switch-to-buffer (current-buffer))
      (sit-for 0.1 t)
      (and (should
	    (or
	     (search-backward "py-execute-expression-test" nil t 1)
	     (search-forward "py-execute-expression-test" nil t 1)))
	   (py-kill-buffer-unconditional (current-buffer))))))

(ert-deftest py-ert-execute-line-test ()
  (py-test-with-temp-buffer-point-min
      "print(\"I'm the py-execute-line-test\")"
    (let ((py-shell-name "python"))
      (sit-for 0.1 t)
      (py-execute-line)
      (sit-for 0.1 t)
      (set-buffer ert-test-default-buffer)
      (sit-for 0.1 t)
      (when py-debug-p (switch-to-buffer (current-buffer)) )
      (and (should
	    (or
	     (search-backward "py-execute-line-test" nil t 1)
	     (search-forward "py-execute-line-test" nil t 1)))
	   (py-kill-buffer-unconditional (current-buffer))))))

(ert-deftest py-ert-execute-statement-python2-test ()
  (py-test-with-temp-buffer-point-min
      "print(\"I'm the py-execute-statement-python2-test\")"
    (when py-debug-p (switch-to-buffer (current-buffer))
	  (font-lock-fontify-buffer))
    (py-execute-statement-python2)
    (set-buffer "*Python2*")
    (goto-char (point-max))
    (sit-for 0.2 t)
    (and (should (search-backward "py-execute-statement-python2-test" nil t 1))
	 (py-kill-buffer-unconditional (current-buffer)))))

(ert-deftest py-ert-always-reuse-lp-1361531-test ()
  (py-test-with-temp-buffer
    "#! /usr/bin/env python
# -*- coding: utf-8 -*-
print(\"I'm the py-always-reuse-lp-1361531-test\")"
    (delete-other-windows)
    (python-mode)
    (let* ((py-split-window-on-execute 'always)
	   py-switch-buffers-on-execute-p
	   py-dedicated-process-p)
      (py-execute-statement-python)
      (py-execute-statement-python3)
      (py-execute-statement-python)
      (message "(window-list): %s" (window-list))
      (sit-for 0.1 t)
      ;; (when py-debug-p (message "py-split-window-on-execute: %s" py-split-window-on-execute))
      (should (eq 3 (count-windows)))
      (py-restore-window-configuration))))

(ert-deftest py-ert-execute-region-python2-test ()
  (py-test-with-temp-buffer
      "print(\"I'm the py-ert-execute-region-python2-test\")"
    (let (py-result)
    (push-mark)
    (goto-char (point-min))
    (py-execute-region-python2 (region-beginning) (region-end))
    (sit-for 0.1 t)
    (should (string-match "py-ert-execute-region-python2-test" py-result)))))

(ert-deftest py-ert-ipython-lp-1398530-test ()
  (when (buffer-live-p (get-buffer "*IPython*"))(py-kill-buffer-unconditional "*IPython*"))
  (py-test-with-temp-buffer
      ""
    ;; (when py-debug-p (switch-to-buffer (current-buffer)))
    (let ((py-shell-name "ipython"))
      (py-shell)
      (sit-for 0.1 t)
      (should (buffer-live-p (get-buffer "*IPython*"))))))

(ert-deftest py-ert-just-two-split-dedicated-lp-1361531-ipython-test ()
  (py-test-with-temp-buffer
      "#! /usr/bin/env ipython
# -*- coding: utf-8 -*-
print(\"I'm the py-just-two-split-dedicated-lp-1361531-ipython-test\")"
    (delete-other-windows)
    (let* ((py-split-window-on-execute 'just-two)
	   (erg1 (progn (py-execute-statement-ipython-dedicated) py-buffer-name))
	   (erg2 (progn (py-execute-statement-ipython-dedicated) py-buffer-name)))
      (sit-for 1 t)
      (when py-debug-p (message "(count-windows) %s" (count-windows)))
      (should (eq 2 (count-windows)))
      (py-kill-buffer-unconditional erg1)
      (py-kill-buffer-unconditional erg2)
      (py-restore-window-configuration))))

(ert-deftest py-ert-just-two-split-dedicated-lp-1361531-jython-test ()
  (py-test-with-temp-buffer
      "#! /usr/bin/env jython
# -*- coding: utf-8 -*-
print(\"I'm the py-just-two-split-dedicated-lp-1361531-jython-test\")"
    (delete-other-windows)
    (let* ((py-split-window-on-execute 'just-two)
	   (erg1 (progn (py-execute-statement-jython-dedicated) py-buffer-name))
	   (erg2 (progn (py-execute-statement-jython-dedicated) py-buffer-name)))
      (sit-for 1 t)
      (when py-debug-p (message "(count-windows) %s" (count-windows)))
      (should (eq 2 (count-windows)))
      (py-kill-buffer-unconditional erg1)
      (py-kill-buffer-unconditional erg2)
      (py-restore-window-configuration))))

(ert-deftest py-reuse-existing-shell-test ()
  "Reuse existing shell unless py-shell is called from within. "
  ;; kill existing shells
  (py--kill-buffer-unconditional "*Python*")
  (py--kill-buffer-unconditional "*IPython*")
  (py--kill-buffer-unconditional "*Python*<2>")
  (py--kill-buffer-unconditional "*IPython*<2>")
  (python)
  (ipython)
  (sit-for 0.1 t)
  (py-test-with-temp-buffer
    ;; this should not open a "*Python*<2>"
    (python)
    (ipython)
    (sit-for 0.1 t)
    (should (not (buffer-live-p (get-buffer "*Python*<2>"))))
    (should (not (buffer-live-p (get-buffer "*IPython*<2>"))))
    (should (buffer-live-p (get-buffer "*Python*")))
    (should (buffer-live-p (get-buffer "*IPython*")))))

(ert-deftest py-flycheck-mode ()
  (py-test-with-temp-buffer
   ""
   (py-flycheck-mode -1)
   (should-not flycheck-mode)
   (py-flycheck-mode 1)
   (should flycheck-mode)
   (py-flycheck-mode -1)
   (should-not flycheck-mode)))

(ert-deftest py-face-lp-1454858-python3-1-test ()
  (let ((py-python-edit-version ""))
    (py-test-with-temp-buffer
	"#! /usr/bin/env python3
file.close()"
      (beginning-of-line)
      (font-lock-fontify-buffer)
      (sit-for 0.1)
      (should-not (eq (face-at-point) 'py-builtins-face)))))

(ert-deftest py-face-lp-1454858-python3-2-test ()
  (let ((py-python-edit-version "python3"))
    (py-test-with-temp-buffer
	"#! /usr/bin/env python3
file.close()"
      (beginning-of-line)
      (font-lock-fontify-buffer)
      (sit-for 0.1)
      (should-not (eq (face-at-point) 'py-builtins-face)))))

(ert-deftest py-face-lp-1454858-python3-3-test ()
  (let ((py-python-edit-version "python3"))
  (py-test-with-temp-buffer
      "#! /usr/bin/env python2
print()"
    (beginning-of-line)
    (font-lock-fontify-buffer)
    (sit-for 0.1)
    (should (eq (face-at-point) 'py-builtins-face)))))

(ert-deftest py-face-lp-1454858-python3-4-test ()
  (let ((py-python-edit-version ""))
  (py-test-with-temp-buffer
      "#! /usr/bin/env python3
print()"
    (beginning-of-line)
    (sit-for 0.1)
    (should (eq (face-at-point) 'py-builtins-face)))))

(ert-deftest py-ert-execute-statement-split ()
  (py-test-with-temp-buffer-point-min
      "print(123)"
    (let ((py-split-window-on-execute t))
      (delete-other-windows)
      (py-execute-statement)
      (sit-for 0.1 t)
      (should (not (one-window-p))))))

(ert-deftest py-ert-py-execute-section-test ()
  (py-test-with-temp-buffer
      "# {{
print(3+3)
# }}"
    (search-backward "print")
    (py-execute-section)
    (sleep-for 1)
    (should (string= py-result "6"))))

(ert-deftest py-ert-match-paren-test-3 ()
    (py-test-with-temp-buffer
	"if __name__ == \"__main__\":
    main()
"
      (skip-chars-backward " \t\r\n\f")
      (back-to-indentation)
      (py-match-paren)
      (should (eq 4 (current-column)))))

(ert-deftest py-ert-match-paren-test-6 ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (search-backward "(treffer)")
    (skip-chars-backward "^\"")
    (forward-char -1)
    (py-match-paren)
    (should (eq (char-after) ?#))
    (py-match-paren)
    (should (eq (char-before) ?\)))
    (should (eolp))))

(ert-deftest py-ert-moves-up-fill-paragraph-pep-257-nn-2 ()
  (let ((py-docstring-style 'pep-257-nn))
    (py-test-with-temp-buffer-point-min

	"class MyClass(object):
    def my_method(self):
        \"\"\"Some long line with more than 70 characters in the docstring. Some more text.\"\"\"
"
      (search-forward "\"\"\"")
      (fill-paragraph)
      (search-forward "\"\"\"")
      (should (eq 8 (current-indentation))))))

(ert-deftest py-ert-moves-up-fill-paragraph-django-1 ()
  (let ((py-docstring-style 'django))
    (py-test-with-temp-buffer-point-min
	"# r1416

def baz():
    \"\"\"Hello there. This is a multiline function definition. Don't wor ry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don't worry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don't worry, be happy. Be very very happy. Very. happy.

    This is a multiline function definition. Don't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7
"
      (goto-char 49)
      ;; (when (called-interactively-p 'any) (message "fill-paragraph-function: %s" fill-paragraph-function))
      (message "fill-paragraph-function: %s" fill-paragraph-function)
      (fill-paragraph)
      (search-backward "\"\"\"")
      (goto-char (match-end 0))
      (should (eolp))
      (forward-line 1)
      (end-of-line)
      (when py-debug-p (message "fill-column: %s" fill-column))
      (should (<= (current-column) 72)))))

(ert-deftest py-ert-split-window-on-execute-1361535-test ()
  (py-test-with-temp-buffer-point-min
      "print(\"%(language)s has %(number)03d quote types.\" %
       {'language': \"Python\", \"number\": 2})"
    (let ((oldbuf (current-buffer))
	  (py-split-window-on-execute t)
	  (py-split-window-on-execute-threshold 3))
      (py-shell)
      (set-buffer oldbuf)
      (switch-to-buffer (current-buffer))
      (delete-other-windows)
      (split-window-vertically)
      (dired "~")
      (set-buffer oldbuf)
      (switch-to-buffer (current-buffer))
      (split-window-horizontally)
      (py-execute-statement)
      (should (eq 3 (length (window-list)))))))

(provide 'py-ert-interactive-tests)
;;; py-ert-interactive-tests.el ends here
