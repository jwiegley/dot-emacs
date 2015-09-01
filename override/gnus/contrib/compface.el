;;; compface.el --- functions for converting X-Face headers
;; Copyright (C) 2002, 2003, 2004 Free Software Foundation, Inc.

;; Author: Lars Magne Ingebrigtsen <larsi@gnus.org>
;;	TAKAI Kousuke <tak@kmc.gr.jp>
;; Keywords: news

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(defgroup compface nil
  "X-Face image conversion."
  :group 'extensions)

(defcustom uncompface-use-external (and (not noninteractive)
					(executable-find "uncompface")
					(executable-find "icontopbm")
					'undecided)
  "*Specify which of the internal or the external decoder should be used.
nil means to use the internal ELisp-based uncompface program.  t means
to use the external decoder.  In the later case, you need to have the
external `uncompface' and `icontopbm' programs installed.  The default
value is nil if those external programs aren't available, otherwise
`undecided' which means to determine it by checking whether the host
machine is slow.  See also `uncompface-use-external-threshold'.  You
can skip that check by setting this value as nil or t explicitly."
  :type '(choice (const :tag "Use the internal decoder" nil)
		 (const :tag "Use the external decoder" t)
		 (const :tag "Autodetection" undecided))
  :group 'compface)

(defcustom uncompface-use-external-threshold 0.1
  "*Number of seconds to check whether the host machine is slow.
If the host takes time larger than this value for decoding an X-Face
using the internal ELisp-based uncompface program, it will be changed
to using the external `uncompface' and `icontopbm' programs if they
are available.  Note that the measurement may never be exact."
  :type 'number
  :group 'compface)

(eval-when-compile
  (defmacro uncompface-float-time (&optional specified-time)
    (if (fboundp 'float-time)
	`(float-time ,specified-time)
      `(let ((time (or ,specified-time (current-time))))
	 (+ (* (car time) 65536.0)
	    (cadr time)
	    (cond ((consp (setq time (cddr time)))
		   (/ (car time) 1000000.0))
		  (time
		   (/ time 1000000.0))
		  (t
		   0)))))))

(defun uncompface (face)
  "Convert FACE to pbm.
If `uncompface-use-external' is t, it requires the external programs
`uncompface', and `icontopbm'.  On a GNU/Linux system these might be
in packages with names like `compface' or `faces-xface' and `netpbm'
or `libgr-progs', for instance."
  (cond ((eq uncompface-use-external nil)
	 (uncompface-internal face))
	((eq uncompface-use-external t)
	 (with-temp-buffer
	   (unless (featurep 'xemacs) (set-buffer-multibyte nil))
	   (insert face)
	   (let ((coding-system-for-read 'raw-text)
		 ;; At least "icontopbm" doesn't work with Windows because
		 ;; the line-break code is converted into CRLF by default.
		 (coding-system-for-write 'binary))
	     (and (eq 0 (apply 'call-process-region (point-min) (point-max)
			       "uncompface"
			       'delete '(t nil) nil))
		  (progn
		    (goto-char (point-min))
		    (insert "/* Format_version=1, Width=48, Height=48,\
 Depth=1, Valid_bits_per_item=16 */\n")
		    ;; I just can't get "icontopbm" to work correctly on its
		    ;; own in XEmacs.  And Emacs doesn't understand un-raw pbm
		    ;; files.
		    (if (not (featurep 'xemacs))
			(eq 0 (call-process-region (point-min) (point-max)
						   "icontopbm"
						   'delete '(t nil)))
		      (shell-command-on-region (point-min) (point-max)
					       "icontopbm | pnmnoraw"
					       (current-buffer) t)
		      t))
		  (buffer-string)))))
	(t
	 (let* ((gc-cons-threshold (eval '(lsh -1 -1)))
		(start (current-time)))
	   (prog1
	       (uncompface-internal face)
	     (setq uncompface-use-external
		   (and (> (- (uncompface-float-time (current-time))
			      (uncompface-float-time start))
			   uncompface-use-external-threshold)
			(executable-find "uncompface")
			(executable-find "icontopbm")
			t))
	     (message "Setting `uncompface-use-external' to `%s'"
		      uncompface-use-external))))))

;; The following section is a bug-for-bug compatible version of
;; `uncompface' program entirely implemented in Emacs-Lisp.

(eval-when-compile
  ;; The size of 48x48 is actually hard-coded into the code itself,
  ;; so you cannot simply change those values.  So we hard-code
  ;; them into the compiled code.
  (defconst uncompface-width 48
    "Width of X-Face bitmap image.")
  (defconst uncompface-height 48
    "Height of X-Face bitmap image.")

  ;; Again, this is also hard-coded into the compiled code.
  (defconst uncompface-guesses
    (mapcar (lambda (x)
	      (mapcar (lambda (x)
			(let ((vector (make-vector (length x) nil))
			      (i 0))
			  (while x
			    (or (zerop (car x))
				(aset vector i t))
			    (setq x (cdr x)
				  i (1+ i)))
			  vector))
		      x))
	    '((;; g_00
	       (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		1 1 1 0 0 0 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 1 0 1 0 0 0 1 0 1 1 1
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 1 1 0 1 1
		0 0 0 0 1 1 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 1 1 0 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 1 1 1 0 1
		0 1 0 0 0 1 0 1 0 0 1 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1
		0 0 0 0 0 0 0 1 0 0 1 1 1 1 1 1
		1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1
		1 0 0 0 0 0 0 0 1 1 0 0 1 0 0 1
		0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 1 1 0 1 1 0 0 0 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 0 1 0 1 0 0
		0 0 0 0 0 1 1 1 0 0 0 1 1 1 1 1
		0 1 0 1 0 1 1 1 0 1 0 0 0 1 1 1
		1 1 0 1 0 1 1 1 0 0 1 1 1 1 0 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 1 1 1 1 1 0 0 0 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		1 0 0 1 1 0 1 1 1 1 0 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 1 1 1 1 1 0 0 0 1 1 1 0 1
		0 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 0 0 0 1 1 1 1 1
		0 0 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		1 1 1 1 0 1 1 1 0 1 1 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 0 1 0 0 0 0 1 1 1 1
		1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 0 1 1 1 1 0 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 0 1 0 0 1 1 1 1
		1 1 0 1 0 1 1 1 0 0 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 0 0 1 1 1 1 0 1 1 1 1 1 1
		0 1 0 1 0 1 1 0 0 0 1 0 0 1 0 1
		0 0 0 1 1 1 1 1 0 1 1 1 1 1 1 1
		1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1
		0 1 0 1 1 1 1 1 0 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 1 1 1 0 1 1 1 1 1
		0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 1 1 1 1 0 1 0 0 0 1 0
		0 0 0 0 1 0 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		0 0 0 1 1 0 0 0 1 1 0 1 0 1 1 1
		1 0 0 1 0 1 0 0 0 1 1 1 0 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1
		0 0 0 1 1 1 1 1 1 0 1 1 0 1 1 1
		0 0 0 0 1 1 0 0 0 0 0 0 0 1 1 1
		0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 1 1 1 1 0 0 0 1 1 1 1 1
		1 0 0 0 0 1 0 0 1 0 0 0 1 1 1 1
		0 0 0 0 0 1 0 1 0 0 0 1 0 1 0 1
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 0 0 0 0 1 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 1
		0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
		0 0 0 0 0 1 0 1 0 0 0 0 0 1 0 0
		0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 0 0 1 1 1 1 1 1 0 0 0 1 1 1 1
		0 1 0 0 1 0 1 0 0 1 0 0 0 0 0 0
		0 1 0 1 1 1 1 1 0 1 0 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1
		1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 1 1 1 0 1
		1 1 0 1 0 1 1 1 0 1 0 1 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 0 1 1 1 0 1 1 1
		1 1 0 1 1 1 1 1 0 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 0 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 0 1 0 0 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 0 0 1 1 1 0 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 0 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1
		0 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 0 0 1 1 0 1 0 0 0 0 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 1
		0 0 0 0 0 1 0 1 0 0 0 0 0 0 1 0
		0 0 0 0 0 0 1 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0
		0 0 0 0 0 0 0 1 0 0 0 0 0 1 1 0
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		0 1 0 0 0 0 0 0 0 0 0 0 1 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
		0 0 0 0 1 1 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0
		1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0
		0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 1
		0 0 0 0 0 0 0 1 0 0 0 1 0 1 0 1
		1 0 1 0 1 1 1 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
		0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0
		0 1 0 0 0 1 1 0 0 0 0 0 1 1 0 0
		0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
		1 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 1 1 1 0 0 0 1 0 1 0 1
		1 1 1 1 1 1 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 1 1 1 1 1 1 1 0 1 0 1 1 1 1 1
		1 1 0 1 1 0 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 0 0 1 1 1 1 1 0
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1
		1 0 0 1 0 1 0 1 0 1 0 0 1 1 1 1
		0 0 0 0 1 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 1 0 0 0 0 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		1 0 0 1 1 1 1 1 1 1 0 1 1 1 1 1
		0 0 1 0 0 1 0 1 0 0 0 0 1 1 1 0
		0 0 0 0 1 1 0 1 0 0 0 0 1 1 0 1
		0 1 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		1 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 1 1 0 1 0
		0 0 0 0 0 1 0 0 0 1 0 0 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 0 1 1 1 0 1 1 1 0 1 1 1
		0 1 0 0 0 1 1 1 1 1 1 0 1 1 0 1
		0 0 0 0 0 1 0 1 0 0 0 0 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 1 0 1 1 1 1
		1 1 0 1 1 0 0 0 0 1 0 1 1 1 1 1
		0 0 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		1 1 0 1 1 1 1 1 0 1 0 1 1 1 1 1
		0 0 0 0 0 1 1 1 0 0 0 0 1 1 1 1
		1 0 0 1 0 1 0 0 0 0 0 0 1 1 0 1
		0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1
		0 1 0 0 0 1 1 0 0 1 0 1 0 1 1 1
		0 0 0 0 0 0 0 1 0 0 0 0 1 1 0 1
		0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0
		0 0 0 0 0 0 0 1 0 0 0 0 1 1 1 1
		0 1 0 0 0 1 1 1 0 1 1 0 1 1 0 0
		0 0 0 0 1 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 0 1 1 0 1 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
		0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0
		1 0 0 1 0 1 0 1 0 0 0 0 0 0 0 1
		0 0 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		0 0 0 0 1 1 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 1 0 0 0 0 1 1 1 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 1 1 1 1 0 1 0 0 0 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 1 0 0 0 0 1 0 0 1 0 0
		0 0 0 0 1 1 0 1 0 0 0 0 1 1 1 1
		0 0 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		1 1 0 0 1 1 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 1 1 0 0 0 1 0 0 1 1 0
		1 1 0 0 1 1 1 1 0 0 0 0 0 1 0 1
		1 1 0 0 1 1 1 1 0 1 1 1 1 1 1 1
		1 1 0 1 1 1 1 1 1 1 0 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 1 0 1 1 1 0 1 0 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 0 1 1 0 0 0 0 0 1 0 0 1
		0 1 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 0 1 0 1 0 0 0 1 0 0 0
		1 0 1 0 0 1 1 1 0 1 1 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 0 0 0 0 0 1 0 0
		1 1 0 1 1 1 1 1 0 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 0 1 1 1 0 0 1 1 0
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 0 1 1 0 0
		1 0 0 0 1 1 1 1 0 1 0 0 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 0 0 1 1 1 1
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 1 0 1 1 1 1 0 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 1 1 0 0 0 0 1 1 0 0
		1 0 0 1 1 1 0 1 0 0 0 0 1 1 1 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)
	       ;; g_10
	       (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0
		1 1 1 1 0 0 1 1 0 1 0 1 1 1 1 1
		1 0 0 0 0 1 0 0 0 0 0 0 0 1 0 0
		0 0 0 1 0 1 1 1 1 0 0 1 1 1 1 1
		0 0 0 0 0 1 0 0 0 0 1 0 0 0 1 1
		0 0 0 0 0 1 0 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
		0 0 0 0 0 0 1 1 0 0 0 0 0 0 1 1
		0 0 1 1 0 0 1 1 1 1 0 1 0 1 1 1
		0 0 0 0 0 1 0 1 0 0 0 0 0 0 1 1
		0 1 0 1 1 1 1 1 0 0 1 1 1 1 1 1
		0 0 0 1 0 1 1 1 0 0 1 1 0 0 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0
		0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 0
		0 0 0 1 0 0 1 0 0 0 0 0 0 0 0 0
		0 0 0 1 0 0 0 1 0 1 0 1 0 1 1 1
		0 0 0 0 0 1 0 1 0 0 1 0 0 1 0 1
		0 0 0 0 0 1 0 1 0 0 0 0 0 0 1 1
		0 0 1 1 0 1 0 1 1 0 1 1 1 1 1 1
		1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 1 1 1 0 1 1 0 1 1 1 1
		0 0 1 0 0 0 0 0 0 1 0 0 0 0 0 0
		0 0 0 1 0 1 1 1 0 0 0 0 0 1 1 0
		1 1 1 1 1 0 1 0 1 1 1 0 1 0 0 0
		0 0 0 0 0 0 0 1 0 0 0 0 0 1 1 1
		0 0 0 1 1 1 1 1 1 0 0 1 1 1 1 1
		0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)
	       ;; g_20
	       (0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1
		0 1 0 0 0 0 1 1 0 0 1 0 1 1 1 0
		1 1 1 1 1 1 1 1 0 0 1 1 1 1 1 1)
	       ;; g_40
	       (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 1 0 0 1 1 1 0
		1 1 1 0 0 1 0 0 0 0 0 0 1 1 0 1
		0 0 0 1 0 0 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 1 0 0 0 1 0 0 0 1 0 0 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 0
		0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1
		1 0 1 0 1 1 1 0 1 0 1 0 1 1 1 1
		0 1 0 0 0 1 0 1 0 1 1 1 1 1 1 1
		1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1
		0 0 0 0 0 0 0 1 0 0 0 1 0 0 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
		0 0 0 1 1 1 0 0 1 1 0 1 1 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1
		0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0
		0 0 0 0 0 0 0 0 1 1 1 1 1 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1
		0 1 0 0 1 1 1 1 0 1 0 1 1 1 1 1
		0 0 1 1 1 1 0 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 1 1 1 0 0 1 1 1 1 1 1 1 1
		1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1
		0 0 0 0 0 0 0 1 0 0 0 0 0 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
		0 0 0 0 0 0 1 0 0 0 0 1 1 1 1 1
		0 0 0 0 0 0 0 1 0 0 0 1 0 0 0 1
		0 0 0 0 0 1 0 1 0 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1
		0 1 0 0 0 0 0 1 0 1 0 1 0 1 1 1
		0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 1 0 1 0 1 1 1 0 1 1 1
		0 0 0 0 1 1 0 1 0 1 0 1 1 1 1 1
		0 1 0 0 1 1 0 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
		0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 1
		0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 1
		0 0 0 0 0 1 0 1 0 1 1 1 1 1 0 1
		0 0 0 1 0 0 0 0 0 0 0 1 0 1 0 1
		0 0 1 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 0 0 0 0 0 1 0 1 0 0 0 0
		0 0 0 0 1 1 0 1 1 1 1 1 1 1 0 1
		0 0 0 0 0 1 0 0 0 0 0 0 1 1 1 1
		0 0 0 0 0 1 1 1 0 0 0 1 1 1 1 1
		0 0 0 0 0 1 1 1 0 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 0 1 1 1 1 1 1
		0 0 0 0 1 1 0 1 0 1 1 1 1 1 1 1
		0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1
		0 1 0 0 1 1 0 1 0 1 1 1 1 1 0 1
		0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1))
	      (;; g_01
	       (0 0 1 1 0 1 1 1 0 1 1 1 0 0 1 1
		0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 1
		0 1 0 1 0 1 1 1 0 1 1 1 1 1 1 1
		1 1 1 1 0 1 0 1 1 1 1 1 1 0 1 1
		0 1 1 1 0 0 0 0 0 0 1 1 0 0 1 1
		1 1 1 1 0 0 0 0 1 1 1 1 1 0 0 1
		0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
		1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1)
	       ;; g_11
	       (0 0 0 0 0 0 0 1 0 0 0 1 0 0 1 1
		0 0 0 0 0 0 1 1 0 1 1 1 1 1 1 1)
	       ;; g_21
	       (0 0 0 1 0 1 1 1)
	       ;; g_41
	       (0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1
		0 0 0 0 0 0 0 1 0 0 0 1 1 1 1 1
		0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1
		0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1))
	      (;; g_02
	       (0 1 0 1)
	       ;; g_12
	       (0 1)
	       ;; g_22
	       (0)
	       ;; g_42
	       (0 0 0 1))))
    "Static prediction table for X-Face image compression algorithm.")

  ;; Macros for inlining critical values. 
  (defmacro uncompface-width () (list 'quote uncompface-width))
  (defmacro uncompface-height () (list 'quote uncompface-height))
  (defmacro uncompface-guesses () (list 'quote uncompface-guesses))

  (defmacro uncompface-loop (&rest body)
    "Eval BODY and repeat if last expression of BODY yields non-nil."
    (list 'while (cons 'progn body))))

;; (defun uncompface-print-bignum (bignum &optional prefix)
;;   (princ (format (concat prefix "<%s>\n")
;; 		 (mapconcat (lambda (x) (format "%02x" x))
;; 			    (reverse bignum) " "))))

;; Shut up the byte-compiler.
;; These variables are once bound in `uncompface' and all subfunctions
;; accesses them directly rather than creating their own bindings.
(eval-when-compile
  (defvar bignum)
  (defvar face))

;; Big-number facilities.
;; These functions were used to be implemented with `lsh' and `logand',
;; but rewritten to use `/' and `%'.  The last two are mapped into
;; byte-code directly, but the formers are normal functions even in
;; compiled code which involve expensive `funcall' operations.
(eval-when-compile
  (defsubst uncompface-big-mul-add (multiplier adder)
    "Multiply BIGNUM by MULTIPLIER and add ADDER and put result in `bignum'."
    (setq bignum (if (= multiplier 0)
		     (cons 0 bignum)
		   (prog1 bignum
		     (while (progn
			      (setcar bignum (% (setq adder (+ (* (car bignum)
								  multiplier)
							       adder))
						256))
			      (setq adder (/ adder 256))
			      (cdr bignum))
		       (setq bignum (cdr bignum)))
		     (or (= adder 0)
			 (setcdr bignum (list adder))))))))

;; This trick is for XEmacs 21.4 which doesn't allow inlining a function
;; using `defsubst' into another function also defined with `defsubst'.
(eval-when-compile
  (when (featurep 'xemacs)
    (defvar uncompface-big-mul-add (symbol-function 'uncompface-big-mul-add))
    (defmacro uncompface-big-mul-add (multiplier adder)
      `(,uncompface-big-mul-add ,multiplier ,adder))))

;; Separate `eval-when-compile' for the byte compiler
;; to properly define `uncompface-big-mul-add' before `uncompface-big-pop'.
(eval-when-compile
  (defsubst uncompface-big-pop (prob)
    (let ((n (car bignum)) (i 0))
      (if (cdr bignum)
	  (setq bignum (cdr bignum))
	(setcar bignum 0))
      (while (or (< n (cdr (car prob)))
		 (>= n (+ (cdr (car prob)) (car (car prob)))))
	(setq prob (cdr prob)
	      i (1+ i)))
      (uncompface-big-mul-add (car (car prob)) (- n (cdr (car prob))))
      i)))

;; This function cannot be inlined due to recursive calls.
(defun uncompface-pop-grays (offset size)
  (if (<= size 3)
      (let ((bits (uncompface-big-pop
		   ;; This is freqs[16] in compface_private.h.
		   '(( 0 .   0) (38 .   0) (38 .  38) (13 . 152)
		     (38 .  76) (13 . 165) (13 . 178) ( 6 . 230)
		     (38 . 114) (13 . 191) (13 . 204) ( 6 . 236)
		     (13 . 217) ( 6 . 242) ( 5 . 248) ( 3 . 253)))))
;; 	(if (/= (logand bits 1) 0)
;; 	    (aset face offset t))
;; 	(if (/= (logand bits 2) 0)
;; 	    (aset face (1+ offset) t))
;; 	(if (/= (logand bits 4) 0)
;; 	    (aset face (+ offset (uncompface-width)) t))
;; 	(if (/= (logand bits 8) 0)
;; 	    (aset face (+ offset (uncompface-width) 1) t))
	(when (>= bits 8)
	  (aset face (+ offset (uncompface-width) 1) t)
	  (setq bits (- bits 8)))
	(when (>= bits 4)
	  (aset face (+ offset (uncompface-width)) t)
	  (setq bits (- bits 4)))
	(or (eq (if (< bits 2)
		    bits
		  (aset face (1+ offset) t)
		  (- bits 2))
		0)
	    (aset face offset t))
	)
    (setq size (/ size 2))
    (uncompface-pop-grays offset size)
    (uncompface-pop-grays (+ offset size) size)
    (uncompface-pop-grays (+ offset (* (uncompface-width) size)) size)
    (uncompface-pop-grays (+ offset (* (uncompface-width) size) size) size)))

;; Again, this function call itself recursively.
(defun uncompface-uncompress (offset size level)
  ;; This used to be (funcall (aref [(lambda ...) ...] (u-big-pop ...)))
  ;; but this was slow due to function call.
  (let ((i (uncompface-big-pop (car level))))
    (cond ((eq i 0)			; black
	   (uncompface-pop-grays offset size))
	  ((eq i 1)			; gray
	   (setq size (/ size 2)
		 level (cdr level))
	   (uncompface-uncompress offset size level)
	   (uncompface-uncompress (+ offset size) size level)
	   (uncompface-uncompress (+ offset (* size (uncompface-width)))
				  size level)
	   (uncompface-uncompress (+ offset (* size (uncompface-width)) size)
				  size level))
	  ;; ((eq i 2) nil)
	  ;; (t (error "Cannot happen"))
	  )))

(eval-when-compile
  (defmacro uncompface-shift-in (k dy dx)
    `(+ k k (if (aref face (+ i (* ,dy (uncompface-width)) ,dx)) 1 0))))

(defun uncompface-internal (string &optional raw)
  "Decode X-Face data STRING and return an image in the pbm format.
If the optional RAW is non-nil, return a raw bitmap as a vector."
  (let (;; `bignum' and `face' are semi-global variables.
	;; Do not use '(0) below, because BIGNUM is modified in-place.
	(bignum (list 0))
	(face (make-vector (* (uncompface-width) (uncompface-height)) nil))
	;;(uncompface-big-shift -16)
	;;(uncompface-big-mask 65535)
	(y 0) x)
    (mapc (lambda (c)
	    (and (>= c ?!) (<= c ?~)
		 (uncompface-big-mul-add (1+ (- ?~ ?!)) (- c ?!))))
	  string)
    ;;(uncompface-print-bignum bignum)
    ;;(setq y 0)
    (uncompface-loop
      (setq x 0)
      (uncompface-loop
	(uncompface-uncompress (+ (* (uncompface-width) y) x) 16
			       ;; This is levels[4][3] in compface_private.h.
			       '(;; Top of tree almost always grey
				 ((  1 . 255) (251 .   0) (  4 . 251))
				 ((  1 . 255) (200 .   0) ( 55 . 200))
				 (( 33 . 223) (159 .   0) ( 64 . 159))
				 ;; Grey disallowed at bottom
				 ((131 .   0) (  0 .   0) (125 . 131))))
	(< (setq x (+ x 16)) (uncompface-width)))
      (< (setq y (+ y 16)) (uncompface-height)))
    (setq y 0)
    (let ((i 0) guesses k)
      (uncompface-loop
	(setq guesses (cond ((= y 1) (nth 2 (uncompface-guesses)))
			    ((= y 2) (nth 1 (uncompface-guesses)))
			    (t	     (nth 0 (uncompface-guesses))))
	      x 0)
	(uncompface-loop
	  (setq k 0)
	  (when (>= x 1)
	    (when (>= x 2)
	      (when (>= x 3)
		(when (>= y 1)
		  (when (>= y 2)
		    (when (>= y 3)
		      (setq k (uncompface-shift-in k -2 -2)))
		    (setq k (uncompface-shift-in k -1 -2)))
		  (setq k (uncompface-shift-in k 0 -2))))
	      (when (>= y 1)
		(when (>= y 2)
		  (when (>= y 3)
		    (setq k (uncompface-shift-in k -2 -1)))
		  (setq k (uncompface-shift-in k -1 -1)))
		(setq k (uncompface-shift-in k 0 -1))))
	    (when (>= y 2)
	      (when (>= y 3)
		(setq k (uncompface-shift-in k -2 0)))
	      (setq k (uncompface-shift-in k -1 0)))
	    (when (>= y 2)
	      (when (>= y 3)
		(setq k (uncompface-shift-in k -2 1)))
	      (setq k (uncompface-shift-in k -1 1)))
	    (when (<= x (- (uncompface-width) 2))
	      (when (>= y 2)
		(when (>= y 3)
		  (setq k (uncompface-shift-in k -2 2)))
		(setq k (uncompface-shift-in k -1 2)))))
	  (if (aref (car (cond ((= x 1)
				(cdr (cdr guesses)))
			       ((= x 2)
				(cdr guesses))
			       ((= x (1- (uncompface-width)))
				(cdr (cdr (cdr guesses))))
			       (t
				guesses))) k)
	      (aset face i (not (aref face i))))
	  (setq i (1+ i))
	  (< (setq x (1+ x)) (uncompface-width)))
	(< (setq y (1+ y)) (uncompface-height))))
    (if raw
	face
      (concat (eval-when-compile
		(format "P1\n%d %d\n" uncompface-width uncompface-height))
	      (mapconcat (lambda (bit) (if bit "1" "0")) face " ")
	      "\n"))))

(provide 'compface)

;; Local variables:
;; eval: (put 'uncompface-loop 'lisp-indent-hook 0)
;; End:

;;; compface.el ends here
