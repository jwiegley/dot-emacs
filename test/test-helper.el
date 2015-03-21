;;; test-helper.el --- helm-company: Test helpers

;; Copyright (C)  2014 Yasuyuki Oka <yasuyk@gmail.com>

;; Author: Yasuyuki Oka <yasuyk@gmail.com>

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

(require 'f)

(defvar helm-company-test/test-path
  (f-parent (f-this-file)))

(defvar helm-company-test/root-path
  (f-parent helm-company-test/test-path))

(require 'helm-company (f-expand "helm-company" helm-company-test/root-path))
(require 'ert)
(eval-when-compile
  (require 'cl))

(provide 'test-helper)

;;; test-helper.el ends here
