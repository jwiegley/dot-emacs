;;; test-helper.el ---                               -*- lexical-binding: t; -*-

;; Copyright (C) 2015-2017  Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>

;; Author: Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>
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
;;; Code:

(when (require 'cl-lib 'no-error)
  (defalias 'incf 'cl-incf))

(require 'undercover)
(undercover "*.el"
            (:exclude "*-tests.el")
            (:report-file "/tmp/undercover-report.json"))

(require 'org-trello)

;;; test-helper.el ends here
