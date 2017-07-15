;;; esh-assert.el --- Alternative to cl-assert       -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
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

;; cl-assert is broken (it calls `debug' directly) in all version of Emacs until
;; 25 (included)

;;; Code:

(defmacro esh-assert (form)
  "Raise an error if FORM evaluates to nil."
  `(unless ,form
     (error "Assertion failed: %S" ',form)))

(provide 'esh-assert)
;;; esh-assert.el ends here
