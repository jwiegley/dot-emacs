;;; pg-fontsets.el --- Define fontsets useful for Proof General
;;
;; Copyright (C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
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
;;

;;; Code:

(defvar pg-fontsets-names nil)

(defcustom pg-fontsets-default-fontset nil
  "*Name of default fontset to use with Proof General."
  :type 'string
  :group 'proof-user-options)

(defconst pg-fontsets-base-font "dejavu lgc sans")
;(defconst pg-fontsets-base-font "liberation mono")

(defun pg-fontsets-make-fontsets ()
  (setq pg-fontsets-names nil)
  (dolist (size '(10 12 14 18 22))
    (add-to-list 'pg-fontsets-names
	(create-fontset-from-fontset-spec
	 (replace-regexp-in-string 
	  "%S" (int-to-string size)
	  (replace-regexp-in-string 
	   "%F" pg-fontsets-base-font
"-*-%F-medium-r-normal--%S-*-*-*-*-*-fontset-PG5%S,
ascii:-*-%F-medium-r-normal--%S-*-*-*-*-*-mac-roman,
latin-iso8859-1:-*-%F-medium-r-normal--%S-*-*-*-*-*-mac-roman,
mule-unicode-0100-24ff:-*-%F-medium-r-normal--%S--*-*-*-*-*-iso10646-1,
mule-unicode-2500-33ff:-*-%F-medium-r-normal--%S--*-*-*-*-*-iso10646-1,
mule-unicode-e000-ffff:-*-%F-medium-r-normal--%S--*-*-*-*-*-iso10646-1")))))
;    (custom-initialize-default 'pg-fontsets-default-fontset 
;			       (nth 2 pg-fontsets-names))
  (setq pg-fontsets-default-fontset (nth 2 pg-fontsets-names))
  (set-default-font pg-fontsets-default-fontset))

;;  (pg-fontsets-make-fontsets)



;;; pg-fontsets.el ends here
