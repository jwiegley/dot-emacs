;;; lentic-latex-code.el -- Latex literate programming -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>
;; Version: 0.1

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014, 2015, 2016, Phillip Lord, Newcastle University

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

;; A `lentic-chunk-configuration' environment where one buffer is latex
;; and the other is some programming language, with code chunks marked up with
;; a =\begin{code}\end{code}= environment.

;; The code environment is not normally defined and has been picked for this
;; reason. It avoids defining multiple init functions for different macros;
;; instead the code chunks can be interpreted using what ever environment the
;; author wants, by defining the code environment first.

;;; Code:

;; #+begin_src emacs-lisp
(require 'lentic-chunk)

(defun lentic-latex-clojure-oset (conf)
  (lentic-m-oset
   conf
   :this-buffer (current-buffer)
   :comment ";; "
   :comment-start "\\\\end{code}"
   :comment-stop "\\\\begin{code}"))

(defun lentic-clojure-to-latex-new ()
  (lentic-latex-clojure-oset
   (lentic-commented-chunk-configuration
    "lb-commented clojure latex"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name)) ".tex"))))

;;;###autoload
(defun lentic-clojure-latex-init ()
  (lentic-clojure-to-latex-new))

(add-to-list 'lentic-init-functions
             'lentic-clojure-latex-init)


(defun lentic-latex-to-clojure-new ()
  (lentic-latex-clojure-oset
   (lentic-uncommented-chunk-configuration
    "lb-commented latex clojure"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name)) ".clj"))))

;;;###autoload
(defun lentic-latex-clojure-init ()
  (lentic-latex-to-clojure-new))

(add-to-list 'lentic-init-functions
             'lentic-clojure-latex-init)

;;;###autoload
(defun lentic-clojure-latex-delayed-init ()
  (lentic-delayed-init 'lentic-clojure-latex-init))

(add-to-list 'lentic-init-functions
             'lentic-clojure-latex-delayed-init)

;;;###autoload
(defun lentic-haskell-latex-init ()
  (lentic-default-configuration
   "lb-haskell"
   :this-buffer (current-buffer)
   :lentic-file
   (concat
    (file-name-sans-extension
     (buffer-file-name))
    ".tex")))

(add-to-list
 'lentic-init-functions
 'lentic-haskell-latex-init)

(provide 'lentic-latex-code)

;;; lentic-latex-code ends here
;; #+end_src
