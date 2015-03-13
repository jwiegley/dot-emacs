;;; f-init.el --- F: Initialization for the tests  -*- lexical-binding: t; -*-

;; Copyright (C) 2013-2014 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>
;; URL: http://github.com/rejeep/f.el

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

;;; Code:

(defvar f-test/test-path
  (directory-file-name (file-name-directory load-file-name))
  "Path to tests directory.")

(defvar f-test/root-path
  (directory-file-name (file-name-directory f-test/test-path))
  "Path to root directory.")

(defvar f-test/vendor-path
  (expand-file-name "vendor" f-test/root-path)
  "Path to vendor directory.")

;; TODO: WHERE CAN WE PUT THIS?
;; (unload-feature 'f 'force)

(load (expand-file-name "f" f-test/root-path) 'noerror 'nomessage)

(unless (require 'ert nil t)
  (require 'ert (expand-file-name "ert" f-test/vendor-path)))

(provide 'f-init)

;;; f-init.el ends here
