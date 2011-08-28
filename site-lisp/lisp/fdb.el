;;; fdb.el --- Debug filter (Sanity saver)

;; Copyright (C) 1995 Anders Lindgren

;; Author : Anders Lindgren <andersl@csd.uu.se>
;; Maintainer: Anders Lindgren <andersl@csd.uu.se>
;; Created: 20 Jun 95
;; Version: 0.6
;; Keywords: debug
;; Date: 19 Dec 95

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;;{{{ Documentation

;; I, like most Emacs Lisp developers, have the variable
;; `debug-on-error' set to `t' to be able to debug my packages
;; whenever an error occur.  However, I am not so happy when I am
;; thrown into the debugger for something which could have been a
;; simple message.
;;
;; This package alows me to specify, by the help of regexps, a set of
;; errors which shouldn't activate the debugger.
;;
;; The signals which shouldn't activate the debugger is stored in the
;; association list `fdb-ignored-signals-alist'.  The car part of each
;; entry in the list is the error symbol.  The cdr part can be either
;; a list of regexps, or the atom t.
;;
;; In the former case the debugger is not invoked if the error message
;; matches a regexp in the list, in the latter case the debugger is
;; never invoked.
;;
;; When loaded, the hook `fdb-load-hook' is runed.
;;
;; This package has been tested on Emacs 19.28, Emacs 19.30,
;; XEmacs 19.12, and (believe it or not) Emacs 18.59.

;; To make this a really good package, more error messages to ignore
;; must be added.  Feel free to send me a list of your favorite hate
;; objects, together with references to the package they are in.
;; (Make sure the string "fdb" is somewere in the subject line.)

;; Install:
;;
;; Byte-compile the file `fdb.el'.  It MUST be byte-compiled!  (Share
;; the same compiled file between Emacs version at your own risk!)
;;
;; Place the following in the appropriate init file:
;;
;; 	(require 'fdb)
;;	(setq debug-on-error t)

;; Emacs 18: 
;; When runed on Emacs 18 replace, in the file `debug.el',
;; the line `(forward-sexp 8)' with `(search-forward "\n debug(")'.
;; The folloing is the output of `diff' when applied to the original
;; and modified files. (In Emacs 18.59, the expression is on line 56.)
;;
;; Byte compile the file `debug.el'.
;;
;; This patch will not affect the operation of the debugger when used
;; witout fdb.

;; 56c56
;; <                            (forward-sexp 8)
;; ---
;; >                            (search-forward "\n  debug(")


;; Usage:
;;
;; Fdb gets activated as soon as it is loaded.
;;
;; To add your own personal haft objects, you can use the function
;; `fdb-add-signal'.  It takes a signal as it's first argument.  If a
;; second is supplied it is treated as a regexp; should it match the
;; message supplied with a signal, the signal does not invoke the
;; debugger.
;;
;; Example:
;;	(fdb-add-signal 'error "^Temperature to high!$")
;;	(fdb-add-signal 'out-of-air)

;; I have submitted the core of a previous version of `fdb', as a
;; patch to debug.el, to the authors of GNU Emacs 19 and XEmacs.  If
;; it should become accepted this package will become obsolete.


;; Q: What on earth are the `{{{' and `}}}' things all over the source
;;    code?
;;
;; A: Fold marks used by Folding Mode.  You can get folding mode from
;;    the Ohio Emacs Lisp archive.  If you feel like testing beta
;;    software, you can get a version me and two friends have been
;;    tinkering with a bit:
;;          ftp://ftp.csd.uu.se/pub/users/andersl/emacs/folding.el
;;	                   -------- '' -----------     /fold-isearch.el
;;
;; While you're at it, take a look at my Emacs pages:
;;          http://www.csd.uu.se/~andersl/emacs.shtml
;;          http://www.csd.uu.se/~andersl/follow.shtml

;;}}}

;;; Code:

;;{{{ A collection of common errors

(defvar fdb-ignored-signals-alist
  (list
   '(beginning-of-line . t)
   '(beginning-of-buffer . t)
   '(end-of-line . t)
   '(end-of-buffer . t)
   '(end-of-file . t)
   '(buffer-read-only . t)
   '(undefined-keystroke-sequence . t)    ;; XEmacs...
   '(file-error . ("^Opening directory$"))
   (cons 'error
	 (list
	  ;; Emacs 19
	  "^Previous command was not a yank$"
	  "^Command attempted to use minibuffer while in minibuffer$"
	  "^Minibuffer window is not active$"
	  "^End of history; no next item$"
	  "^Beginning of history; no preceding item$"
	  "^No recursive edit is in progress$"
	  "^Changes to be undone are outside visible portion of buffer$"
	  "^No undo information in this buffer$"
	  "^No further undo information$"
	  "^Save not confirmed$"
	  "^Recover-file cancelled\\.$"
	  "^Attempt to save to a file which you aren't allowed to write$"
	  
	  ;;XEmacs
	  "^No preceding item in "
	  "^No following item in "
	  "^Unbalanced parentheses$"
	  "^no selection$"
	  "^No selection or cut buffer available$"
   
	  ;; comint
	  "^Not at command line$"
	  "^Empty input ring$"
	  "^No history$"
	  "^Not found$";; To common?
	  "^Current buffer has no process$"
   
	  ;; dabbrev
	  "^No dynamic expansion for \".*\" found\\.$"
	  "^No further dynamic expansions for \".*\" found\\.$"
	  "^No further dynamic expansions for `.*' found$"
   
	  ;; Completion
	  (concat "^To complete, the point must be after a symbol at "
		  "least [0-9]* character long\\.$")
	  "^The string \".*\" is too short to be saved as a completion\\.$"
   
	  ;; Compile
	  "^No more errors\\( yet\\|\\)$"
   
	  ;; Gnus
	  "^NNTP: Connection closed\\.$"
   
	  ;; info
	  "^Node has no Previous$"
	  "^No \".*\" in index$"
   
	  ;; imenu
	  "^No items suitable for an index found in this buffer\\.$"
	  "^The mode \".*\" does not take full advantage of imenu\\.el yet\\.$"
   
	  ;; ispell
	  "^No word found to check!$"
   
	  ;; mh-e
	  "^Cursor not pointing to message$"
	  "^There is no other window$"
   
	  ;; man
	  "^No manpage [0-9]* found$"
   
	  ;; etags
	  "^No tags table in use!  Use .* to select one\\.$"
	  "^There is no default tag$"
	  "^No previous tag locations$"
	  "^File .* is not a valid tags table$"
	  "^No \\(more \\|\\)tags \\(matching\\|containing\\) "
	  "^Rerun etags: `.*' not found in "
	  "^All files processed\\.$"
	  (concat 
	   "^"
	   (regexp-quote
	    (substitute-command-keys
	     "No \\[tags-search] or \\[tags-query-replace] in progress."))
	   "$")
	  "^File .* not in current tags tables$"
	  (concat 
	   "^"
	   (regexp-quote
	    (substitute-command-keys
	     "No tags table loaded.  Try \\[visit-tags-table]."))
	   "$")
	  "^Nothing to complete$"
   
	  ;; BBDB
	  "^no previous record$"
	  "^no next record$"
	  )))
  "*An alist of signals and messages which should not invoke the debugger.

The elements in the alist have the error symbol as the car part.  The
cdr part can either be a list of regexps, or the atom t.  In the
former case the debugger is not invoked if the message matches a
regexp in the list, in the latter case the debugger is never invoked.

Normal error messages, generated by calls to the `error' function,
use the error symbol `error'.

Please see the source file `fdb.el' for an example.")

;;}}}
;;{{{ debug

;; Load the debug package so that we can patch it.
(load "debug" 'noerror 'nomessage)


;; Store a reference to the original version of `debug'
(if (not (fboundp 'fdb-orig-debug))
    (fset 'fdb-orig-debug (symbol-function 'debug)))


;; Call the debugger on real errors only. 
;; Display the rest using `signal'. (Yes, even errors.)
;;
;; Note that is the signal is not in the alist, tail will end
;; up bound to nil, and hence the debugger will be invoked.

(defun debug (&rest debugger-args)
  "Patched by fdb. Please see the documentation on `fdb-orig-debug'."
  (interactive)
  ;;        Cut here if you would like to incorporate
  ;; -----8<----- this into the file `debug.el'. ----->8-----
  ;;          Just drop it into the function `debug'.
  (let ((dont-debug nil)
	(debug-on-error nil))
    (if (eq (car-safe debugger-args) 'error)
	(let ((tail (cdr-safe (assq (car-safe (car-safe (cdr debugger-args)))
				    fdb-ignored-signals-alist)))
	      (msg (car-safe (cdr-safe (car-safe (cdr debugger-args))))))
	  (cond ((eq tail 't)
		 (setq dont-debug t))
		((stringp msg)
		 (let ((data (match-data)))
		   (unwind-protect
		       (while (and (not dont-debug) tail)
			 (if (string-match (car tail) msg)
			     (setq dont-debug t))
			 (setq tail (cdr tail)))
		     (store-match-data data)))))))
    (if dont-debug
	(condition-case nil
	    ;; XEmacs
	    (throw 'debugger t)
	  (no-catch
	   ;; Emacs 19
	   (signal (car (car (cdr debugger-args))) 
		   (cdr (car (cdr debugger-args))))))))
  ;; -----8<-----  Stop cutting here. ----->8-----
  (apply 'fdb-orig-debug debugger-args))

;;}}}
;;{{{ backtrace-debug

;; Replace the `backtrace-debug' function. This makes sure that the
;; debugger compensates for the number of stack frames used by
;; our filter.

;; Just a quick hack to get it to roll on Emacs 18.  (The
;; eval-and-compile call is needed to keep the Emacs 19 byte-compiler
;; happy.)

(if (string-match " 18" emacs-version)
    (defun eval-and-compile (&rest args) nil))

(eval-and-compile
  (if (not (fboundp 'fdb-orig-backtrace-debug))
      (fset 'fdb-orig-backtrace-debug (symbol-function 'backtrace-debug))))


;; `6' Emacs-18.  (Tested on Gayle Emacs 18.59)
;;
;; `2' For XEmacs 19.12
;; `3' For Emacs 19.28 and Emacs 19.30.
;;
;; Please experiment with other values for your Emacs.

(defvar fdb-frame-offset
  (cond
   ((string-match "Lucid" emacs-version) 2)
   ((string-match "^19" emacs-version)   3)
   (t                                    6))
  "The extra stack frame offset needed for compensating the `fdb' patch.")


(defun backtrace-debug (frame flag)
  "Patched. Please see the documentation on `fdb-orig-backtrace-debug'."
  (funcall 'fdb-orig-backtrace-debug (+ frame fdb-frame-offset) flag))

;;}}}
;;{{{ Support function

(defun fdb-add-signal (signal &optional regexp)
  "Make sure SIGNAL does not invoke the debugger.

If called with an optional argument REGEXP, a signal
with a message matching REGEXP will not invoke the debugger."
  (interactive 
   "SName of signal: \nsMessage to ignore (regexp, or return for all): \n")
  (if (not (boundp 'fdb-ignored-signals-alist))
      ;; Just in case `fdb-ignored-signals-alist' isn't defined.
      (setq fdb-ignored-signals-alist nil))
  ;; The user just pressed return, treat it is "all messages"
  (if (equal regexp "") 
      (setq regexp nil))
  (let ((pair (assq signal fdb-ignored-signals-alist)))
    (if (not regexp)
	;; Add the signal.
	(cond (pair (setcdr pair t))
	      (t (setq fdb-ignored-signals-alist
		       (cons (cons signal t) fdb-ignored-signals-alist))))
      ;; Add the signal with a regexp.
      (cond ((and pair (eq (cdr pair) t)))
	    ;; Do nothing, we already ignore everything.
	    ((and pair (member regexp (cdr pair))))
	    ;; Do nothing, we already ignore this regexp.
	    (pair
	     (setcdr pair (cons regexp (cdr pair))))
	    (t
	     (setq fdb-ignored-signals-alist
		   (cons (cons signal (list regexp))
			 fdb-ignored-signals-alist)))))))

;;}}}
;;{{{ The end

(run-hooks 'fdb-load-hook)

(provide 'fdb)

;;}}}

;;; fdb.el ends here
