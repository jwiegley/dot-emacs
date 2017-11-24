;;; lentic-script.el -- Config for scripts -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>
;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2016, Phillip Lord, Newcastle University

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

;;; Commentary:

;; #+begin_src emacs-lisp
(require 'lentic-cookie)
(require 'lentic-chunk)
(require 'lentic-org)

(defvar lentic-script-temp-location
  temporary-file-directory "/lentic-script")

;;;###autoload
;; We need to copy this entire form into the autoloads file. If we use a
;; normal autoload, it force loading of the entire package when it is called
;; during autoload which defeats the point. Unfortunately, autoload files are
;; normally dynamically bound, and we use closures. The eval form addresses
;; both of these simultaneously.
(eval
 '(defun lentic-script-hook (mode-hook init)
    (add-to-list 'lentic-init-functions init)
    (add-hook mode-hook
              (lambda nil
                (unless lentic-init
                  (setq lentic-init init)))))
 t)

(defun lentic-script--lentic-file-2 (file)
  (concat
   lentic-script-temp-location
   (substring
    (file-name-sans-extension file)
    1)
   ".org"))

(defun lentic-script--lentic-file-1 (file)
  (let ((l
         (lentic-script--lentic-file-2 file)))
    (make-directory (file-name-directory l) t)
    l))

(defun lentic-script-lentic-file ()
  (lentic-script--lentic-file-1 (buffer-file-name)))

;;;###autoload
(defun lentic-python-script-init ()
  (lentic-org-python-oset
   (lentic-cookie-unmatched-commented-chunk-configuration
    "temp"
    :lentic-file
    (lentic-script-lentic-file))))

;;;###autoload
(lentic-script-hook 'python-mode-hook
                    'lentic-python-script-init)

;;;###autoload
(defun lentic-bash-script-init ()
  (lentic-cookie-unmatched-commented-chunk-configuration
   "temp"
   :this-buffer (current-buffer)
   :comment "## "
   :comment-stop "#\\\+BEGIN_SRC sh"
   :comment-start "#\\\+END_SRC"
   :lentic-file
   (lentic-script-lentic-file)))

;;;###autoload
(lentic-script-hook 'shell-mode-hook
                    'lentic-bash-script-init)

;;;###autoload
(defun lentic-lua-script-init ()
  (lentic-cookie-unmatched-commented-chunk-configuration
   "temp"
   :this-buffer (current-buffer)
   :comment "-- "
   :comment-stop "#\\\+BEGIN_SRC lua"
   :comment-start "#\\\+END_SRC"
   :case-fold-search nil
   :lentic-file
   (lentic-script-lentic-file)))

;;;###autoload
(lentic-script-hook 'lua-mode-hook
                    #'lentic-lua-script-init)

(provide 'lentic-script)
;;; lentic-script ends here
;; #+end_src
