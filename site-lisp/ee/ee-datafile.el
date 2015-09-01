;;; ee-datafile.el --- display and edit data files

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee

;; This file is [not yet] part of GNU Emacs.

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this package; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; See the file README and documentation for more information.

;;; Code:

(require 'ee)

;;; Constants

(defconst ee-datafile-mode-name "ee-datafile")

;;; Customizable Variables

(defgroup ee-datafile nil
  "Display and edit data files."
  :prefix "ee-datafile-"
  :group 'ee)

;;; Top-Level Functions

;;;###autoload (add-to-list 'auto-mode-alist '("\\.ee\\'" . emacs-lisp-mode))
;;;###autoload
(defun ee-datafile-mode (&optional arg)
  "Datafile view mode.
The purpose of this function is to create the view buffer,
when user visits a file with -*- mode: ee-datafile -*-."
  (interactive "P")
  (emacs-lisp-mode)
  ;; Call ee-datafile only when ee-datafile-mode is called by some
  ;; interactive command. This covers two cases:
  ;; 1. ee-datafile-mode is called directly by M-x;
  ;; 2. user calls some interactive command for visiting files
  ;;    and after file is visited, ee-datafile-mode is called as
  ;;    a result of file having -*- ee-datafile -*- in the first row.
  ;; But ee-datafile isn't called if file is visited during
  ;; Emacs startup (by package "desktop.el", etc.),
  ;; because this will report startup error.
  ;; This is BAD hack. TODO: BETTER hack :-)
  (if (and this-command (not (eq this-command 'ee)))
    (ee-datafile arg)))

;;;###autoload
(defun ee-datafile (&optional arg file)
  "Display and edit data files."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*/%s"
           ee-datafile-mode-name
           (or file (file-name-nondirectory (buffer-file-name))))
   ee-datafile-mode-name
   nil
   nil
   nil
   nil
   nil
   (or file (buffer-file-name))))

(provide 'ee-datafile)

;;; ee-datafile.el ends here
