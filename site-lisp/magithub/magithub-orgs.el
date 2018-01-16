;;; magithub-orgs.el --- Organization handling  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: tools

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

;; Utilities for dealing with organizations.

;;; Code:

(require 'magithub-core)

(defun magithub-orgs-list ()
  "List organizations for the currently authenticated user."
  (magithub-cache :user-demographics
    `(magithub-request
      (ghubp-get-user-orgs))))

(provide 'magithub-orgs)
;;; magithub-orgs.el ends here
