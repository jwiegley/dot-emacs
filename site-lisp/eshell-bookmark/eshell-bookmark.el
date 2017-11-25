;;; eshell-bookmark.el --- Integrate bookmarks with eshell.  -*- lexical-binding: t -*-

;; Copyright (C) 2017 Matúš Goljer

;; Author: Matúš Goljer <matus.goljer@gmail.com>
;; Maintainer: Matúš Goljer <matus.goljer@gmail.com>
;; Version: 2.0.0
;; Created:  6th September 2017
;; Package-requires: ((emacs "24.3"))
;; Keywords: convenience, files
;; URL: https://github.com/Fuco1/eshell-bookmark

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provides bookmark.el integration for eshell.  It is
;; especially useful for quickly jumping to remote/TRAMP hosts.

;; To enable, add (add-hook 'eshell-mode-hook 'eshell-bookmark-setup)
;; to your configuration.

;;; Code:

(require 'bookmark)
(require 'eshell)

(defun eshell-bookmark--make-record ()
  "Create a eshell bookmark.

The bookmark will try to open an eshell session with the pwd set
to the location when the bookmark was created."
  (let ((bookmark `((handler . eshell-bookmark--restore)
                    (filename . ,default-directory))))
    bookmark))

(defun eshell-bookmark--restore (bookmark)
  "Restore eshell buffer according to BOOKMARK."
  (let ((eshell-buffer-name
         (or (bound-and-true-p shell-pop-last-shell-buffer-name)
             eshell-buffer-name)))
    (eshell)
    (setq default-directory (cdr (assq 'filename bookmark)))
    (eshell-reset)))

;;;###autoload
(defun eshell-bookmark-setup ()
  "Setup eshell-bookmark."
  (setq-local bookmark-make-record-function 'eshell-bookmark--make-record))

(provide 'eshell-bookmark)
;;; eshell-bookmark.el ends here
