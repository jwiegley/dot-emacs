;;; window-purpose-test.el --- Tests for window-purpose.el -*- lexical-binding: t -*-

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
;; This file contains tests for window-purpose.el

;;; Code:

(ert-deftest purpose-test-mode-line ()
  "Test `purpose--modeline-string' returns correct string."
  (save-window-excursion
    (unwind-protect
	(purpose-with-temp-config
      nil '(("xxx-test" . test)) nil
    (set-window-buffer nil (get-buffer-create "xxx-test"))
    (purpose-set-window-purpose-dedicated-p nil t)
    (should (equal (purpose--modeline-string) " [test!]"))
    (purpose-set-window-purpose-dedicated-p nil nil)
    (should (equal (purpose--modeline-string) " [test]")))
      (purpose-kill-buffers-safely "xxx-test")
      (purpose-set-window-purpose-dedicated-p nil nil))))

(provide 'window-purpose-test)

;;; window-purpose-test.el ends here
