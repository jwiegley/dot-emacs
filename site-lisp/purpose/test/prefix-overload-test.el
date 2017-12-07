;;; prefix-overload-test.el --- Tests for window-purpose-prefix-overload.el -*- lexical-binding: t -*-

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
;; This file contains tests for window-purpose-prefix-overload.el

;;; Code:

(ert-deftest purpose-test-prefix-overload ()
  "Test `define-purpose-prefix-overload' works correctly."
  (define-purpose-prefix-overload --purpose-prefix-test
    '((lambda () (interactive) 0)
      (lambda () (interactive) 1)
      (lambda () (interactive) 2)
      (lambda () (interactive) 3)))
  (should (equal 0 (purpose-call-with-prefix-arg nil '--purpose-prefix-test)))
  (should (equal 0 (purpose-call-with-prefix-arg 0 '--purpose-prefix-test)))
  (should (equal 1 (purpose-call-with-prefix-arg 1 '--purpose-prefix-test)))
  (should (equal 2 (purpose-call-with-prefix-arg 2 '--purpose-prefix-test)))
  (should (equal 3 (purpose-call-with-prefix-arg 3 '--purpose-prefix-test)))
  (should-error (purpose-call-with-prefix-arg 4 '--purpose-prefix-test))
  (should (equal 1 (purpose-call-with-prefix-arg '(4) '--purpose-prefix-test)))
  (should (equal 2 (purpose-call-with-prefix-arg '(16) '--purpose-prefix-test)))
  (should (equal 3 (purpose-call-with-prefix-arg '(64) '--purpose-prefix-test)))
  (should-error (purpose-call-with-prefix-arg '(256) '--purpose-prefix-test)))

(provide 'prefix-overload-test)

;;; prefix-overload-test.el ends here
