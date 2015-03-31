;;; filesets-tellib.el --- filesets supplement for tellib users

;; Copyright (C) 2002 Free Software Foundation, Inc.

;; Author: Thomas Link aka samul at web dot de
;; Time-stamp: <2003-04-06>
;; Keywords: filesets

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

;;; Commentary:

;; This is a supplement to filesets.el.

;;; Change log:

;;; To do:

;;; Code:

(require 'tellib)
(tellib-version-check-with-name "tellib" "0.2.1")

(defalias 'filesets-error 'tellib-error)
(defalias 'filesets-split-string-by-char 'tellib-split-string-by-char)
(defalias 'filesets-message 'tellib-message)

(defalias 'filesets-member 'tellib-member)
(defalias 'filesets-some 'tellib-some)
(defalias 'filesets-filter-list 'tellib-filter-list)
(defalias 'filesets-sublist 'tellib-sublist)

(defalias 'filesets-alist-get 'tellib-alist-get)
(defalias 'filesets-directory-files 'tellib-directory-files)
(defalias 'filesets-file-name-break-up 'tellib-file-name-break-up)
(defalias 'filesets-file-name-last-bit 'tellib-file-name-last-bit)

(require 'filesets2)

(provide 'filesets-tellib)

;;; filesets-tellib.el ends here

;;; Local Variables:
;;; time-stamp-format:"%y-%02m-%02d"
;;; auto-recompile: 1
;;; End:
