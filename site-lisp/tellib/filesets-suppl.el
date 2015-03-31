;;; filesets-suppl.el --- functions to make filesets.el work with older
;;; Emacsens

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link aka samul at web dot de
;; Time-stamp: <2003-03-02>
;; Keywords:

(defconst filesets-suppl-version "1.0.0")
 
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

;;; Change log:

;;; To do:

;;; Code:

(eval-and-compile
  (when (not (fboundp 'valid-plist-p))
    (defun valid-plist-p (plist)
      "XEmacs' valid-plist-p mimicry."
      (= (mod (length plist) 2) 0)))

  (when (not (fboundp 'lax-plist-get))
    (defun lax-plist-get (lax-plist property &optional default)
      "Support for XEmacs' lax-plists."
      (if (valid-plist-p lax-plist)
	  (let ((this (member property lax-plist)))
	    (if this
		(if (= (mod (length this) 2) 0)
		    (cadr this)
		  (lax-plist-get (cdr this) property default))
	      default))
	(filesets-error 'malformed-property-list
			'lax-plist-get lax-plist))))
      
  (when (not (fboundp 'lax-plist-put))
    (defun lax-plist-put (lax-plist property value)
      "Support for XEmacs' lax-plists."
      (if (valid-plist-p lax-plist)
	  (let ((this (member property lax-plist)))
	    (if this
		(progn
		  (if (= (mod (length this) 2) 0)
		      (setcdr this (cons value (cddr this)))
		    (setcdr this (lax-plist-put (cdr this)
						property value)))
		  lax-plist)
	      (append (list property value) lax-plist)))
	(filesets-error 'malformed-property-list
			'lax-plist-put lax-plist))))

  (cond
   ;; This should work for 21.1 Emacs
   ((fboundp 'easy-menu-define)
    (defun filesets-add-submenu (menu-path submenu &optional
					   before in-menu)
      "`easy-menu-define' wrapper."
      (easy-menu-define
       filesets-submenu global-map "Filesets menu" submenu)))
   ((fboundp 'easy-menu-create-keymaps)
    ;; This is based on a proposal kindly made by Christoph Conrad.
    ;; Untested.
    (defun filesets-add-submenu (menu-path submenu &optional
					   before in-menu)
      "`easy-menu-create-keymaps' wrapper."
      (define-key
	global-map
	[menu-bar filesets]
	(cons "Filesets"
	      (easy-menu-create-keymaps "Filesets" (cdr submenu))))))
   (t
    (message "Filesets: I don't know how to build menus -- will be using dummy function.")
    (defun filesets-add-submenu (menu-path submenu &optional
					   before in-menu)
      "This is a dummy function."
      nil))))


(provide 'filesets-suppl)

;;; filesets-suppl.el ends here

;;; Local Variables:
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
