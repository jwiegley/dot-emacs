;;; test-helper.el --- EPL: Unit test helpers -*- lexical-binding: t; -*-

;; Copyright (C) 2013  Sebastian Wiesner

;; Author: Sebastian Wiesner <lunaryorn@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>
;;     Sebastian Wiesner <lunaryorn@gmail.com>
;; URL: http://github.com/cask/epl

;; This file is NOT part of GNU Emacs.

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

(require 'find-func)
(require 'cl-lib)
(require 'f)


;;;; Directories

(eval-and-compile
  (defconst epl-test-directory (f-parent (f-this-file))
    "Directory of the EPL test suite.")

  (defconst epl-test-resource-directory (f-join epl-test-directory "resources")
    "Directory of resources for the EPL testsuite.")

  (defconst epl-test-source-directory (f-parent epl-test-directory)
    "Source directory of EPL."))


;;;; Load EPL

;; Load compatibility libraries first
(load (f-join epl-test-source-directory "compat" "load.el") nil 'no-message)

(require 'epl (f-join epl-test-source-directory "epl"))

;; Check that it is really the right EPL
(let ((source (symbol-file 'epl-initialize 'defun)))
  (cl-assert (f-same? source (f-join epl-test-source-directory "epl.elc")) nil
             "ERROR: EPL not loaded from byte-compiled source, but from %s! \
Please run make compile" source))


;;;; Utilities

(defun epl-test-resource-file-name (resource)
  "Get the file name of a RESOURCE."
  (f-join epl-test-resource-directory resource))

;;; test-helper.el ends here
