;;; eshell-z-test.el --- tests for eshell-z

;; Copyright (C) 2015  Chunyang Xu

;; Author: Chunyang Xu <xuchunyang56@gmail.com>

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

(require 'ert)
(require 'eshell-z)

(defvar user-home-path (getenv "HOME"))

(ert-deftest eshell-z--expand-directory-name ()
  (should (equal (eshell-z--expand-directory-name "~")
                 user-home-path))
  (should (equal (eshell-z--expand-directory-name "~/.emacs.d/")
                 (expand-file-name (concat user-home-path "/" ".emacs.d")))))

(ert-deftest eshell-z--directory-within-p ()
  (should (equal (eshell-z--directory-within-p "~/.emacs.d/elpa" "~/.emacs.d") t))
  (should (equal (eshell-z--directory-within-p "/tmp/" "/tmp") t))
  (should (equal (eshell-z--directory-within-p "~/tmp" "/tmp") nil))
  (should (equal (eshell-z--directory-within-p "foobar" "/foo") nil)))

(ert-deftest eshell-z--common-root ()
  (let ((dirs '("/Users/xcy/repos/mu/lib"
                "/Users/xcy/repos/mu"
                "/Users/xcy/repos/mu/guile")))
    (should (equal (eshell-z--common-root dirs) "/Users/xcy/repos/mu"))))
