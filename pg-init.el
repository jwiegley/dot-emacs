;;; pg-init.el --- Init file used for compatibility with package.el and ELPA  -*- lexical-binding: t; -*-

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>

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
;;
;; Proof General's initialization code (in generic/proof-site) is relatively
;; complex, in part because it was written before package.el existed, and in
;; part because package.el still doesn't look for autoloads in subdirectories.
;; This file is a thin, package.el-friendly wrapper around generic/proof-site,
;; suitable for execution on Emacs start-up.  It serves two purposes:
;;
;; * Setting up the load path when byte-compiling PG.
;; * Loading a minimal PG setup on startup (not all of Proof General, of course;
;;   mostly mode hooks and autoloads).

;;; Code:

;;;###autoload
(eval-and-compile
  (defvar pg-init--script-full-path
    (or (and load-in-progress load-file-name)
        (bound-and-true-p byte-compile-current-file)
        (buffer-file-name)))
  (defvar pg-init--pg-root
    (file-name-directory pg-init--script-full-path)))

;;;###autoload
(unless (bound-and-true-p byte-compile-current-file)
  ;; This require breaks compilation, so it must only run when loading the package.
  (require 'proof-site (expand-file-name "generic/proof-site" pg-init--pg-root)))

(eval-when-compile
  (let ((byte-compile-directories
         '("generic" "lib"
           "coq" "easycrypt" "pghaskell" "pgocaml" "pgshell")))
    (dolist (dir byte-compile-directories)
      (add-to-list 'load-path (expand-file-name dir pg-init--pg-root)))))

(provide 'pg-init)
;;; pg-init.el ends here
