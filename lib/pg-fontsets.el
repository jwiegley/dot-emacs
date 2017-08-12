;;; pg-fontsets.el --- Define fontsets useful for Proof General

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>

;; License:   GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Define some fontsets to try to select fonts that display many symbols.
;;
;; Select one of these fontsets via the menu Options -> Set Font/Fontset
;; or, with M-x set-default-font
;;
;; Recommended & free fonts to install on your system are:
;;
;;  DejaVu LGC (Sans and Sans Mono).  See http://dejavu.sourceforge.net
;;  Liberation (Sans and Mono).  See https://fedorahosted.org/liberation-fonts/
;;

;;; Code:

(require 'fontset)

(defcustom pg-fontsets-default-fontset nil
  "*Name of default fontset to use with Proof General."
  :type 'string
  :group 'proof-user-options)

(defvar pg-fontsets-names nil
  "*List of fontsets to use with Proof General.")

(defun pg-fontsets-make-fontsetsizes (basefont)
  (dolist (size '(10 12 14 18 22))
    (add-to-list 'pg-fontsets-names
	(create-fontset-from-fontset-spec
	 (replace-regexp-in-string
	  "%T" (car (split-string basefont))
	 (replace-regexp-in-string
	  "%S" (int-to-string size)
	  (replace-regexp-in-string
	   "%F" basefont
"-*-%F-*-*-*--%S-*-*-*-*-*-fontset-PG%T,
gnu-unifont:-*-%F-*-*-*--%S-*-*-*-*-*-iso10646-1"
;ascii:-*-%F-medium-r-normal--%S-*-*-*-*-*-mac-roman,
;latin-iso8859-1:-*-%F-medium-r-normal--%S-*-*-*-*-*-mac-roman,
;mule-unicode-0100-24ff:-*-%F-medium-r-normal--%S--*-*-*-*-*-iso10646-1,
;mule-unicode-2500-33ff:-*-%F-medium-r-normal--%S--*-*-*-*-*-iso10646-1,
;mule-unicode-e000-ffff:-*-%F-medium-r-normal--%S--*-*-*-*-*-iso10646-1"
)))))))

(defconst pg-fontsets-base-fonts
  '("dejavu lgc sans mono"
    "liberation mono"
    "stixregular"
    "lucidasanstypewriter"))

(defun pg-fontsets-make-fontsets ()
  (setq pg-fontsets-names nil)
  (mapcar 'pg-fontsets-make-fontsetsizes
	  pg-fontsets-base-fonts))

(pg-fontsets-make-fontsets)


(provide 'pg-fontsets)
;;; pg-fontsets.el ends here
