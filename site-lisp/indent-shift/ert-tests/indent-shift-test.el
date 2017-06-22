;;; indent-shift-test.el --- Tests for indent-shift  -*- lexical-binding: t; -*-

;; Copyright (C) 2014  Tom Willemse

;; Author: Tom Willemse <tom@ryuslash.org>
;; Keywords:

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

(require 'indent-shift)

(ert-deftest indent-shift-left-4 ()
  "Check that shifting left works with 4 spaces."
  (with-temp-buffer
    (insert "    foo\n    bar\n    baz")
    (let ((tab-width 4)
          (indent-tabs-mode nil))
      (indent-shift-left (point-min) (point-max)))
    (should (looking-back "\\`foo\nbar\nbaz\\'"))))

(ert-deftest indent-shift-left-8 ()
  "Check that shifting left works with 8 spaces."
  (with-temp-buffer
    (insert "        foo\n        bar\n        baz")
    (let ((tab-width 8)
          (indent-tabs-mode nil))
      (indent-shift-left (point-min) (point-max)))
    (should (looking-back "\\`foo\nbar\nbaz\\'"))))

(ert-deftest indent-shift-left-err ()
  "Check that an error occurs when shifting left and no spaces exist."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((tab-width 4)
          (indent-tabs-mode nil))
      (should-error (indent-shift-left (point-min) (point-max))))))

(ert-deftest indent-shift-left-err-partial ()
  "Check that an error occurs when shifting left and not all spaces exist."
  (with-temp-buffer
    (insert "    foo\n    bar\nbaz")
    (let ((tab-width 4)
          (indent-tabs-mode nil))
      (should-error (indent-shift-left (point-min) (point-max))))))

(ert-deftest indent-shift-right-4 ()
  "Check that shifting right works with 4 spaces."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((tab-width 4)
          (indent-tabs-mode nil))
      (indent-shift-right (point-min) (point-max)))
    (should (looking-back "\\`    foo\n    bar\n    baz\\'"))))

(ert-deftest indent-shift-right-8 ()
  "Check that shifting right works with 8 spaces."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((tab-width 8)
          (indent-tabs-mode nil))
      (indent-shift-right (point-min) (point-max)))
    (should
     (looking-back "\\`        foo\n        bar\n        baz\\'"))))

(provide 'indent-shift-test)
;;; indent-shift-test.el ends here
