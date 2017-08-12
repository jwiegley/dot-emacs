;;; lego-site.el --- Site-specific Emacs support for LEGO

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;;; Author: Thomas Kleymann <T.Kleymann@ed.ac.uk>
;;; Maintainer: lego@dcs.ed.ac.uk

;; Proof General is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; Proof General is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Proof General. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;

;;; Code:

(let ((version (getenv "PROOFGENERAL")))
  (cond ((not version)		;default
	 (setq load-path
	       (cons "/usr/local/share/elisp/script-management" load-path))
	 (setq load-path
	       (cons "/usr/local/share/elisp/script-management/lego" load-path))
	 (setq auto-mode-alist (cons '("\\.l$" . lego-mode) auto-mode-alist))
	 (autoload 'lego-mode "lego" "Major mode for editing Lego proof scripts." t))
	((string= version "ancient") 
	 (setq load-path (cons "/usr/local/share/elisp/lego" load-path))
	 (setq auto-mode-alist (cons '("\\.l$" . lego-mode) auto-mode-alist))
	 (autoload 'lego-mode "lego" "Major mode for editing Lego proof scripts." t)
	 (autoload 'lego-shell "lego" "Inferior shell invoking lego." t))
	((string= version "latest")
	 (load-file "/usr/local/share/elisp/ProofGeneral/generic/proof-site.el"))))
	 

	 
