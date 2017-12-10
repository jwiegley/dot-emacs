;;; private-functions.el --- test for dired-k private functions

;; Copyright (C) 2017 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>

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

;;; Code:

(require 'ert)
(require 'dired-k)

(ert-deftest child-directory ()
  "Return child directory path"
  (let ((got (dired-k--child-directory "/foo/" "/foo/bar/baz")))
    (should (string= got "/foo/bar"))))

(ert-deftest update-subdirectory-state-already-modified ()
  "Update subdirectory state whose state is already modified"
  (dolist (s '(modified added normal untracked))
    (should (eq (dired-k--subdir-status 'modified s) 'modified))))

(ert-deftest update-subdirectory-state-overwrite-by-new-state ()
  "Update subdirectory state, overwrite by new state"
  (should (eq (dired-k--subdir-status 'normal 'added) 'added))

  (dolist (s '(modified added untracked))
    (should (eq (dired-k--subdir-status nil s) s))))

(ert-deftest update-subdirectory-state-set-new-state ()
  "Update subdirectory state, set to new state"
  (dolist (s '(modified added untracked))
    (should (eq (dired-k--subdir-status nil s) s))))

(ert-deftest file-is-in-child-directory ()
  "Whether specified path is in child directory"
  (let ((here "/foo/bar")
        (path "/foo/bar/baz/a.txt"))
    (should (dired-k--is-in-child-directory here path)))

  (let ((here "/foo/bar")
        (path "/foo/bar/a/b/c/d.txt"))
    (should (dired-k--is-in-child-directory here path)))

  (let ((here "/foo/bar")
        (path "/foo/bar/bar.txt"))
    (should-not (dired-k--is-in-child-directory here path))))

;;; private-functions.el ends here
