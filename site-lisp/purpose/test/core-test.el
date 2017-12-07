;;; core-test.el --- Tests for window-purpose-core.el -*- lexical-binding: t -*-

;; Copyright (C) 2015, 2016 Bar Magal

;; Author: Bar Magal
;; Package: purpose

;; This file is not part of GNU Emacs.

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
;; This file contains tests for window-purpose-core.el

;;; Code:

(ert-deftest purpose-test-dummy-buffer-name ()
  "Test generation of dummy buffer names"
  (should (equal (purpose--dummy-buffer-name 'edit) "*pu-dummy-edit*")))

(ert-deftest purpose-test-mode-purpose ()
  "Test `purpose--buffer-purpose-mode' returns correct values."
  (purpose-with-temp-config
      '((prog-mode . prog) (c-mode . c) (text-mode . text))
      nil nil
    (with-temp-buffer
      (let ((c++-mode-hook nil)
            (c-mode-hook nil)
            (text-mode-hook nil))
        (c++-mode)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'prog))
        (c-mode)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'c))
        (text-mode)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'text))))))

(ert-deftest purpose-test-name-purpose ()
  "Test `purpose--buffer-purpose-name' returns correct values."
  (purpose-with-temp-config
      nil
      '(("hello" . hello) ("foo" . foo))
      nil
    (with-temp-buffer
      (rename-buffer "hello" t)
      (should (equal (purpose-buffer-purpose (current-buffer)) 'hello))
      (rename-buffer "foo" t)
      (should (equal (purpose-buffer-purpose (current-buffer)) 'foo)))))

(ert-deftest purpose-test-regexp-purpose ()
  "Test `purpose--buffer-purpose-regexp' returns correct values."
  (purpose-with-temp-config
      nil nil
      '(("^hello$" . hello) ("^\\*foo" . foo))
    (with-temp-buffer
      (rename-buffer "hello" t)
      (should (equal (purpose-buffer-purpose (current-buffer)) 'hello))
      (rename-buffer "*foo bar*" t)
      (should (equal (purpose-buffer-purpose (current-buffer)) 'foo)))))

(ert-deftest purpose-test-buffer-purpose ()
  "Test `purpose-buffer-purpose' returns correct values."
  (purpose-with-temp-config
      '((c-mode . c))
      '(("foo" . foo-by-name) ("*foo bar*" . foo-bar))
      '(("^\\*foo" . foo-by-regexp))
    (with-temp-buffer
      (let ((c-mode-hook nil)
            (default-purpose 'some-default))
        (should (equal (purpose-buffer-purpose (current-buffer)) default-purpose))
        (c-mode)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'c))
        ;; regexp overrides mode
        (rename-buffer "*foo*" t)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'foo-by-regexp))
        ;; name overrides regexp and mode
        (rename-buffer "*foo bar*" t)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'foo-bar))
        ;; dummy buffer overrides anything else
        (rename-buffer "*pu-dummy-xxx*" t)
        (should (equal (purpose-buffer-purpose (current-buffer)) 'xxx))))))

(ert-deftest purpose-test-buffers-with-purpose ()
  "Test `purpose-buffers-with-purpose'."
  (purpose-with-temp-config
      nil nil '(("xxx-test" . test))
    (unwind-protect
        (let (buffers)
          (push (get-buffer-create "xxx-test-1") buffers)
          (push (get-buffer-create "xxx-test-2") buffers)
          (get-buffer-create "another-buffer")
          (should (or (equal (purpose-buffers-with-purpose 'test) buffers)
                      (equal (purpose-buffers-with-purpose 'test) (reverse buffers)))))
      (purpose-kill-buffers-safely "xxx-test-1" "xxx-test-2" "another-buffer"))))

(ert-deftest purpose-test-window-purpose ()
  "Test `purpose-window-purpose'."
  (unwind-protect
      (save-window-excursion
        (set-window-buffer nil (get-buffer-create "xxx-test-1"))
        (purpose-with-temp-config
            nil '(("xxx-test-1" . test)) nil
          (should (equal (purpose-window-purpose) 'test))))
    (purpose-kill-buffers-safely "xxx-test-1")))

(ert-deftest purpose-test-windows-with-purpose ()
  "Test `purpose-windows-with-purpose'."
  (unwind-protect
      (save-window-excursion
  (let (windows
        (split-width-threshold 1)
        (split-height-threshold 1))
    (delete-other-windows)
    (set-window-buffer nil (get-buffer-create "xxx-test-1"))
    (push (selected-window) windows)
    (select-window (split-window))
    (set-window-buffer nil (get-buffer-create "another-buffer"))
    (purpose-with-temp-config
        nil '(("another-buffer" . foo)) '(("xxx-test" . test))
      (should (equal (purpose-windows-with-purpose 'test) windows)))))
    (purpose-kill-buffers-safely "xxx-test-1" "another-buffer")))

(ert-deftest purpose-test-get-buffer-create ()
  "Test `purpose--get-buffer-create' returns/creates correct buffer."
  (unwind-protect
      (purpose-with-temp-config
          nil '(("xxx-test" . test)) nil
        (should (equal (buffer-name (purpose--get-buffer-create 'test)) "*pu-dummy-test*"))
        (purpose-kill-buffers-safely "*pu-dummy-test*")
        (get-buffer-create "xxx-test")
        (should (equal (buffer-name (purpose--get-buffer-create 'test)) "xxx-test")))
    (purpose-kill-buffers-safely "*pu-dummy-test*" "xxx-test")))

(ert-deftest purpose-test-set-window-buffer ()
  "Test `purpose--set-window-buffer' sets correct buffer and window."
  (unwind-protect
      (save-window-excursion
        (purpose-with-empty-config
          (delete-other-windows)
          (let* ((window (selected-window))
                 (other-window (split-window window)))
            (purpose--set-window-buffer 'test)
            (should (equal (buffer-name (window-buffer window)) "*pu-dummy-test*"))
            (should-not (equal (purpose-window-purpose other-window) 'test)))))
    (purpose-kill-buffers-safely "*pu-dummy-test*")))

(ert-deftest purpose-test-dedication-toggle ()
  "Test toggling of window dedication (purpose and buffer)."
  (let ((buffer-dedication (window-dedicated-p))
  (purpose-dedication (purpose-window-purpose-dedicated-p)))
    (unwind-protect
  (progn
    ;; buffer dedication
    (set-window-dedicated-p nil nil)
    (purpose-toggle-window-buffer-dedicated)
    (should (window-dedicated-p))
    (purpose-toggle-window-buffer-dedicated)
    (should-not (window-dedicated-p))
    ;; purpose dedication
    (purpose-set-window-purpose-dedicated-p nil nil)
    (purpose-toggle-window-purpose-dedicated)
    (should (purpose-window-purpose-dedicated-p))
    (purpose-toggle-window-purpose-dedicated)
    (should-not (purpose-window-purpose-dedicated-p)))
      (set-window-dedicated-p nil buffer-dedication)
      (purpose-set-window-purpose-dedicated-p nil purpose-dedication))))

(ert-deftest purpose-test-get-window ()
  "Test functions for getting top/bottom/left/right windows.
Functions tested are:
- `purpose-get-top-window'
- `purpose-get-bottom-window'
- `purpose-get-left-window'
- `purpose-get-right-window'"
  (save-window-excursion
    (delete-other-windows)
    (should-not (purpose-get-top-window))
    (should-not (purpose-get-bottom-window))
    (should-not (purpose-get-left-window))
    (should-not (purpose-get-right-window))
    (let ((top-window (selected-window))
    (bottom-window (split-window nil 5 'below)))
      (should (equal (purpose-get-top-window) top-window))
      (should (equal (purpose-get-bottom-window) bottom-window))
      (should-not (purpose-get-left-window))
      (should-not (purpose-get-right-window)))
    (delete-other-windows)
    (let ((left-window (selected-window))
    (right-window (split-window nil 5 'right)))
      (should (equal (purpose-get-left-window) left-window))
      (should (equal (purpose-get-right-window) right-window))
      (should-not (purpose-get-top-window))
      (should-not (purpose-get-bottom-window)))))

(defmacro purpose-test-preferred-prompt-checker (expected)
  (declare (indent defun) (debug symbolp))
  (cl-case expected
    ('ido '(equal (purpose-get-read-function 'ido-meth 'helm-meth 'vanilla-meth) 'ido-meth))
    ('helm '(equal (purpose-get-read-function 'ido-meth 'helm-meth 'vanilla-meth) 'helm-meth))
    ('vanilla '(equal (purpose-get-read-function 'ido-meth 'helm-meth 'vanilla-meth) 'vanilla-meth))
    (t (error "Invalid expectation: %S" expected))))

;; helm-mode needs to be bound for proper emulation to work in the next tests
(unless (boundp 'helm-mode)
  (defvar helm-mode))

(ert-deftest purpose-test-preferred-prmopt ()
  "Test user gets his preferred prompt method.
The prompt is chosen according to `purpose-preferred-prompt'."
  (let ((purpose-preferred-prompt 'ido))
    (should (purpose-test-preferred-prompt-checker ido)))
  (let ((purpose-preferred-prompt 'helm))
    (should (purpose-test-preferred-prompt-checker helm)))
  (let ((purpose-preferred-prompt 'vanilla))
    (should (purpose-test-preferred-prompt-checker vanilla)))
  (let ((purpose-preferred-prompt 'auto))
    (let ((ido-mode nil)
          (helm-mode nil))
      (should (purpose-test-preferred-prompt-checker vanilla)))
    (let ((ido-mode nil)
          (helm-mode t))
      (should (purpose-test-preferred-prompt-checker helm)))
    (let ((ido-mode t)
          (helm-mode nil))
      (should (purpose-test-preferred-prompt-checker ido)))
    (let ((ido-mode t)
          (helm-mode t))
      (should (purpose-test-preferred-prompt-checker ido)))))

(ert-deftest purpose-test-preferred-completing-read ()
  "Test `purpose-get-completing-read-function' sanity."
  (let ((purpose-preferred-prompt 'ido))
    (should (equal (purpose-get-completing-read-function) 'ido-completing-read))))

(ert-deftest purpose-test-preferred-read-file-name ()
  "Test `purpose-get-read-file-name-function' sanity."
  (let ((purpose-preferred-prompt 'ido))
    (should (equal (purpose-get-read-file-name-function) 'ido-read-file-name))))

(ert-deftest purpose-test-get-all-purposes ()
  "Test `purpose-get-all-purposes'."
  (purpose-with-temp-config
      '((mode1 . foo) (mode2 . bar))
      '(("name1" . baz) ("name2" . foo))
      nil
    (should (equal (sort (mapcar #'symbol-name (purpose-get-all-purposes)) #'string-lessp)
                   (sort (mapcar #'symbol-name '(foo bar baz general)) #'string-lessp)))))

(ert-deftest purpose-test-read-purpose ()
  "Test that `purpose-read-purpose' return correct purpose."
  (purpose-insert-user-input "foo")
  (should (equal (purpose-read-purpose "Purpose: " '(foo bar baz)) 'foo)))

(ert-deftest purpose-test-default-file-purpose ()
  "Test that the default purpose for a buffer visiting a file is 'edit.
Also test that if there was a predefined purpose for that buffer
it gets that one, and that the default purpose for a buffer not
visiting a file is still `default-purpose'."
  (unwind-protect
      (purpose-with-temp-config
          nil '(("foo" . yolo)) nil
        (find-file-noselect "foo")
        (should (equal (purpose-buffer-purpose (get-buffer "foo")) 'yolo))
        (find-file-noselect "bar")
        (should (equal (purpose-buffer-purpose (get-buffer "bar")) 'edit))
        (get-buffer-create "baz")
        (should (equal (purpose-buffer-purpose (get-buffer "baz")) default-purpose)))
    (purpose-kill-buffers-safely "foo" "bar" "baz")))

(provide 'core-test)

;;; core-test.el ends here
