;;; lentic-script-test.el --- Tests -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014, 2015, 2016, Phillip Lord, Newcastle University

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

;;; Code:

(require 'lentic-script)
(require 'assess)

(ert-deftest lentic-script-lentic-file ()
  (should
   (assess=
    "/tmp/home/phillord/file.org"
    (lentic-script--lentic-file-2
     "/home/phillord/file.py"))))


(ert-deftest lentic-script-conf-test ()
  (should
   (with-temp-buffer
     (set-visited-file-name "/tmp/lentic-script-test-filename.py")
     (lentic-python-script-init)
     (set-visited-file-name nil)))
  (should
   (with-temp-buffer
     (set-visited-file-name "/tmp/lentic-script-test-filename.sh")
     (lentic-bash-script-init)
     (set-visited-file-name nil))))

(defun lentic-script-test-file (filename)
  (assess-file
   (lentic-test-file filename)))

(ert-deftest lentic-script-python-clone ()
  (should
   (assess=
    (lentic-script-test-file "fullpython.org")
    (lentic-test-clone
     "fullpython.py"
     #'lentic-python-script-init))))

(ert-deftest lentic-script-bash-clone ()
  (should
   (assess=
    (lentic-script-test-file "fullsh.org")
    (lentic-test-clone
     "fullsh.sh"
     #'lentic-bash-script-init))))


(ert-deftest lentic-script-lua-clone ()
  (should
   (assess=
    (lentic-script-test-file "fulllua.org")
    (lentic-test-clone
     "fulllua.lua"
     #'lentic-lua-script-init))))


(ert-deftest lentic-script-lua-clone-change ()
  (should
   (lentic-test-clone-and-change=
    #'lentic-lua-script-init
    "fulllua.lua"
    "fulllua.org"
    (lambda ()
      (forward-line)
      (insert "-- hello")
      (beginning-of-line)
      (kill-line))))
  (should
   (lentic-test-clone-and-change=
    #'lentic-lua-script-init
    "fulllua.lua"
    "fulllua.org"
    nil
    (lambda ()
      (forward-line)
      (insert "hello")
      (beginning-of-line)
      (kill-line))))
  )




(provide 'lentic-script-test)
;;; lentic-script-test.el ends here
