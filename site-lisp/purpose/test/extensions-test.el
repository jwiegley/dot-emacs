;;; extensions-test.el --- Tests for window-purpose-x.el -*- lexical-binding: t -*-

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
;; This file contains tests for window-purpose-x.el

;;; Code:

(defmacro purpose-x-kill-test (&rest body)
  (declare (indent defun) (debug body))
  `(save-window-excursion
     (unwind-protect
         (progn
           (purpose-mode)
           (purpose-x-kill-setup)
           (purpose-with-temp-config
               nil nil '(("^xxx-p0-" . p0) ("^xxx-p1-" . p1))
             (purpose-create-buffers-for-test :p0 2 :p1 1)
             (delete-other-windows)
             ,@body))
       (purpose-x-kill-unset)
       (purpose-mode -1)
       (delete-other-windows)
       (purpose-set-window-purpose-dedicated-p nil nil)
       (set-window-dedicated-p nil nil)
       (purpose-kill-buffers-safely "xxx-p0-0" "xxx-p0-1" "xxx-p1-0"))))

;; kill in non-ded window -> replace with other purpose
(ert-deftest purpose-test-x-kill-1 ()
  "Test the purpose-x-kill extension."
  (purpose-x-kill-test
    (let ((win (selected-window)))
      (set-window-buffer win "xxx-p1-0")
      (set-window-buffer win "xxx-p0-0")
      (kill-buffer "xxx-p0-0")
      (should (eq (window-buffer win) (get-buffer "xxx-p1-0")))
      (should-not (buffer-live-p (get-buffer "xxx-p0-0"))))))

;; kill in buf-ded window (sole window) -> replace with any buffer, buf is dead
(ert-deftest purpose-test-x-kill-2 ()
  "Test the purpose-x-kill extension."
  (purpose-x-kill-test
    (let ((win (selected-window)))
      (set-window-buffer win "xxx-p1-0")
      (set-window-buffer win "xxx-p0-0")
      (set-window-dedicated-p nil t)
      (kill-buffer "xxx-p0-0")
      (should (eq (window-buffer win) (get-buffer "xxx-p1-0")))
      (should-not (buffer-live-p (get-buffer "xxx-p0-0"))))))

;; kill in perp-ded window -> replace with same purpose
(ert-deftest purpose-test-x-kill-3 ()
  "Test the purpose-x-kill extension."
  (purpose-x-kill-test
    (let ((win (selected-window)))
      (set-window-buffer win "xxx-p1-0")
      (set-window-buffer win "xxx-p0-0")
      (purpose-set-window-purpose-dedicated-p nil t)
      (kill-buffer "xxx-p0-0")
      (should (eq (window-buffer win) (get-buffer "xxx-p0-1")))
      (should-not (buffer-live-p (get-buffer "xxx-p0-0"))))))

;; kill in purp-ded window (sole window, sole buf) -> replace with other purpose, buf is dead
(ert-deftest purpose-test-x-kill-4 ()
  "Test the purpose-x-kill extension."
  (purpose-x-kill-test
    (let ((win (selected-window)))
      (set-window-buffer win "xxx-p0-0")
      (set-window-buffer win "xxx-p1-0")
      (purpose-set-window-purpose-dedicated-p nil t)
      (kill-buffer "xxx-p1-0")
      (should (eq (window-buffer win) (get-buffer "xxx-p0-0")))
      (should-not (buffer-live-p (get-buffer "xxx-p1-0"))))))

;; kill in buf-ded window (multi window) -> kill window
(ert-deftest purpose-test-x-kill-5 ()
  "Test the purpose-x-kill extension."
  (purpose-x-kill-test
    (set-window-buffer nil "xxx-p0-0")
    (set-window-dedicated-p nil t)
    (switch-to-buffer-other-window "xxx-p1-0")
    (kill-buffer "xxx-p0-0")
    (should (equal (length (window-list)) 1))
    (should (eq (current-buffer) (get-buffer "xxx-p1-0")))
    (should-not (buffer-live-p (get-buffer "xxx-p0-0")))))

;; kill in purp-ded window (multi window, sole buf) -> kill window
(ert-deftest purpose-test-x-kill-6 ()
  "Test the purpose-x-kill extension."
  (purpose-x-kill-test
    (set-window-buffer nil "xxx-p1-0")
    (purpose-set-window-purpose-dedicated-p nil t)
    (switch-to-buffer-other-window "xxx-p0-0")
    (kill-buffer "xxx-p1-0")
    (should (equal (length (window-list)) 1))
    (should (eq (current-buffer) (get-buffer "xxx-p0-0")))
    (should-not (buffer-live-p (get-buffer "xxx-p1-0")))))

(provide 'extensions-test)

;;; extensions-test.el ends here
