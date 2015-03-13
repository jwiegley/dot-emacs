;;; initsplit --- code to split customizations into different files

;; Copyright (C) 2000, 2001 John Wiegley
;; Copyright (C) 2010, 2011 Dave Abrahams
;; Copyright (C) 2011       Mat Marcus

;; Author: John Wiegley <johnw@gnu.org>, Dave Abrahams <dave@boostpro.com>
;; Created:  8 Feb 2000
;; Version: 1.6
;; Keywords: lisp
;; X-URL: http://www.gci-net.com/users/j/johnw/emacs.html

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This file allows you to split Emacs customizations (set via M-x
;; customize) into different files, based on the names of the
;; variables.  It uses a regexp to match against each face and
;; variable name, and associates with a file that the variable should
;; be stored in.

;; To use it, just load the file in your .emacs:
;;
;;   (load "initsplit")
;;
;; If you want configuration files byte-compiled, add this after it:
;;
;;   (add-hook 'after-save-hook 'initsplit-byte-compile-files t)

;; Note that that you *must* load each file that contains your various
;; customizations from your .emacs.  Otherwise, the variables won't
;; all be set, and the next time you use the customize interface, it
;; will delete the settings in those other files.

;; Then, customize the variable `initsplit-customizations-alist', to
;; associate various configuration names with their respective
;; initialization files.

;; I find this module most useful for splitting up Gnus and Viper
;; customizations.

;;; History:

;;; Code:

(require 'cl)
(require 'find-func)
(require 'simple) ;; for delete-blank-lines
(require 'cus-edit)

(defconst initsplit-version "1.7"
  "This version of initsplit.")

(defgroup initsplit nil
  "Code to split customizations into different files."
  :group 'initialization)

;;; User Variables:

(defcustom initsplit-load-hook nil
  "*A hook that gets run after \"initsplit.el\" has been loaded."
  :type 'hook
  :group 'initsplit)

(defcustom initsplit-customizations-alist nil
  "*Alist of (REGEXP FILE BYTECOMP PRE-LOAD)

Variables and faces matching REGEXP will be written to FILE.

If BYTECOMP is nil, `initsplit-byte-compile-files' will
not byte-compile FILE.

If PRE-LOAD is nil, initsplit will not try to ensure FILE is
loaded at startup."
  :type '(repeat
          (list (regexp  :tag "Var regexp")
                (file    :tag "Custom file")
                (boolean :tag "Byte-compile")
                (boolean :tag "Pre-load" :value t)))
  :group 'initsplit)

(defvar initsplit-dynamic-customizations-alist nil
  "List of dynamic initsplit customizations that is appended to
`initsplit-customizations-alist'.  Each element may be
a (PATTERN, FILE) pair or a FUNCTION that is expected to return a
list of (PATTERN, FILE) pairs.

Used to programmatically add initsplit files that are not to be
saved as part of the customization of
`initsplit-customizations-alist' itself.  Note: Elements of
`initsplit-customizations-alist' take precedence.")

(defcustom initsplit-default-directory
  (file-name-as-directory user-emacs-directory)
  "*The directory for writing new customization files and the
first place initsplit will look when loading a customization file
specified with a non-absolute path"
  :group 'initsplit
  :type 'directory)

(defcustom initsplit-pretty-print
  nil
  "If t, initsplit will write reformat customizations with
`indent-pp-sexp'.  Especially useful if you keep your
customizations in version control, as it tends to result in diffs
that cover only the actual changes."
  :group 'initsplit
  :type 'boolean)

;;; User Functions:

;;; Helper Functions:

(defun initsplit-filter (list pred)
  "Return the subset of LIST that satisfies PRED"  
  (reduce (lambda (elt lst) (if (funcall pred elt) (cons elt lst) lst))
          list :from-end t :initial-value nil))

(defun initsplit-custom-alist ()
  "Return an alist of (PATTERN, FILE) pairs containing all
customization FILEs and the PATTERNs matching variable values
they store, accounting for initsplit-customizations-alist,
initsplit-dynamic-customizations-alist, and custom-file"
  (let* ((dynamic-lists
          (mapcar (lambda (e) ;; a sequence of lists to concatenate
                    (if (functionp e) (funcall e) (list e)))
                  initsplit-dynamic-customizations-alist))
         (unmerged
          (append initsplit-customizations-alist
                  (apply 'append dynamic-lists) ;; flattened
                  (when (initsplit-custom-file)
                    `(("" ,(initsplit-custom-file))))))
         (index (make-hash-table :test 'equal))
         result)

    (dolist (s unmerged)
      (let* ((f (initsplit-filename s))
             (match (gethash f index)))
        (if match
            (progn
              ;; merge the patterns in-place
              (setcar match (concat (car match) "\\|" (car s)))
              ;; "or" the flags together
              (setcdr (cdr match)
                      `(,(or (caddr s) (caddr match))
                        ,(or (cadddr s) (cadddr match)))))

          ;; else build a new element to add to the result
          (push (cons (car s) (cons f (cddr s))) result)
          (puthash f (car result) index))))
    (nreverse result)))

(defun initsplit-customizations-subset (file-pred)
  "Return the subset of `(initsplit-custom-alist)' whose
FILE element satisfies FILE-PRED"
  (initsplit-filter (initsplit-custom-alist)
                    (lambda (s) (funcall file-pred (initsplit-filename s)))))

(defun initsplit-preload-p (filespec)
  "Return non-nil if the file given by filespec should be preloaded."
  (cadddr filespec))

(defun initsplit-filename (filespec)
  "Return the truename of the file associated with the
`(initsplit-custom-alist)' element FILESPEC"
  (let* ((file (cadr filespec))
         (default-directory initsplit-default-directory)
         (load-path (cons default-directory load-path)))
    (file-truename
     (or (ignore-errors (find-library-name file)) file))))

;;
;; Protection against overwriting valuable customizations
;;
(defun initsplit-known-p (file)
  "Return non-nil iff the file named by FILE has been loaded or
does not exist"
  (or (not (file-exists-p file))
      (load-history-filename-element (load-history-regexp file))))

(defun initsplit-known-file-alist ()
  "Return the subset of `(initsplit-custom-alist)' that we
can write safely (without lossage)"
  (initsplit-customizations-subset 'initsplit-known-p))

(defun initsplit-unknown-file-alist ()
  "Return the subset of `(initsplit-custom-alist)' that
might contain customizations we haven't seen yet."
  (initsplit-customizations-subset '(lambda (x) (not (initsplit-known-p x)))))

(defun initsplit-load-if-exists (file)
  "Load the given file if it exists."
  (load file 'ignore-non-existent-file))

(defvar initsplit-load-function 'initsplit-load-if-exists
  "The function that's actually used by initsplit to load
customization files before their customizations are operated on.")
(eval-when-compile
  (defvar initsplit-stanza-position nil)
  (defvar initsplit-buffer-checksum nil))

(defun initsplit-load (filespec)
  "If the file specified by (initsplit-custom-alist)' element
FILESPEC exists, load it.  Preference will be given to variations
of the filename as with `load-library'."
  (funcall initsplit-load-function
           (initsplit-strip-lisp-suffix
            (initsplit-filename filespec))))

(defun initsplit-find-option-match (pattern options)
  "Where OPTIONS are an alist as accepted by
`custom-buffer-create', return nil unless they specify
customization of a symbol whose name matches PATTERN."
  (find-if 
   (lambda (option)
     (if (eq (cadr option) 'custom-group)
         (initsplit-find-option-match pattern (custom-group-members (car option) nil))
       (string-match pattern (symbol-name (car option)))))
   options))
  
(defadvice custom-buffer-create-internal
  (before initsplit-custom-buffer-create-internal
          (options &optional description) activate compile preactivate)
  "Load up all relevant customization files before any customization starts"
  (dolist (filespec (initsplit-unknown-file-alist))
    (when (and (not (initsplit-known-p (cadr filespec)))
               (initsplit-find-option-match (car filespec) options))
      (initsplit-load filespec))))

(defadvice customize-saved (before initsplit-load-all
                                   activate compile preactivate)
  "Before attempting to customize all saved settings, let's make
sure we've loaded all those settings"
  (dolist (pat-file (initsplit-unknown-file-alist))
    (initsplit-load pat-file)))

;;
;; Remove empty stanzas after writing.  It would be nicer to not write
;; empty stanzas, but the current design of custom-save-variables and
;; custom-save-faces doesn't really let us do that.
;;
(defun initsplit-remove-empty-stanza (symbol)
  "If the call to SYMBOL just written by customize
has no arguments, delete it.

Used to remove empty custom-set-* stanzas."
  (save-excursion
    ;; our custom-save-delete advice saved the position of the call as
    ;; initsplit-stanza-position
    (goto-char initsplit-stanza-position)
    (unwind-protect
        (let ((sexp (read (current-buffer))))
          (assert (eq (car sexp) symbol))
          (if (= 1 (length sexp))
              (progn
                (custom-save-delete symbol)
                (delete-blank-lines))
            (when initsplit-pretty-print
              (goto-char initsplit-stanza-position)
              (indent-pp-sexp t))))

      ;; clean up marker we no longer need.
      (set-marker initsplit-stanza-position nil))))

(defadvice custom-save-delete (after initsplit-custom-save-set-markers
                                        activate compile preactivate)
  "Remember the position where custom is about to write its stanza"
  (when (boundp (make-local-variable 'initsplit-stanza-position))
    (set-marker initsplit-stanza-position nil))
  (setq initsplit-stanza-position (point-marker)))

(defadvice custom-save-variables (around no-empty-stanzas
                                        activate compile preactivate)
  "Delete empty customization stanzas for variables.  Also
remember the state of the buffer before custom-save-variables was
invoked so we can avoid writing it when there's been no real
modification."

  (set (make-local-variable 'initsplit-buffer-checksum)
       (unless (buffer-modified-p) (md5 (current-buffer))))

  ad-do-it

  (initsplit-remove-empty-stanza 'custom-set-variables))

(defadvice custom-save-faces (after no-empty-stanzas
                                     activate compile preactivate)
  "Delete empty customization stanzas for faces."
  (initsplit-remove-empty-stanza 'custom-set-faces))

(defadvice save-buffer (before initsplit-correct-modified-p compile)
  (if (and
       (bound-and-true-p initsplit-buffer-checksum)
       (string= initsplit-buffer-checksum (md5 (current-buffer))))
      (set-buffer-modified-p nil)))

(defun initsplit-enable-modified-p-correction (enable)
  (funcall (if enable 'ad-enable-advice 'ad-disable-advice)
           'save-buffer 'before 'initsplit-correct-modified-p)
  (ad-activate 'save-buffer))


;;
;; Where the hard work is done
;;
(defadvice custom-save-all (around initsplit-custom-save-all
                                   activate compile preactivate)
  "Wrapper over custom-save-all that saves customizations into
multiple files per (initsplit-custom-alist)"

  ;; Store up the saved-value/face properties of all symbols
  ;; and remember that we haven't saved them yet
  (mapatoms
   (lambda (symbol)
     (when (or
            (put symbol 'initsplit-saved-value (get symbol 'saved-value))
            (put symbol 'initsplit-saved-face (get symbol 'saved-face)))
       (put symbol 'initsplit-saved-to nil))))

  (initsplit-enable-modified-p-correction t)

  (unwind-protect
      ;; For each customization file whose contents are known, save
      ;; appropriate symbols
      (dolist (s (initsplit-known-file-alist))
        (let ((custom-file (file-truename (initsplit-filename s))))

          ;; As-yet-unsaved symbols that match the regexp
          ;; get a saved-value/face property.  Others get nil.
          (mapatoms

           (lambda (symbol)
             (let* ((saved-to (get symbol 'initsplit-saved-to))

                    (save-here
                     (if (null saved-to)
                         (string-match (car s) (symbol-name symbol))
                       (string= custom-file saved-to))))

               (if save-here
                   (progn ; let custom have its way
                     (put symbol 'saved-value
                          (get symbol 'initsplit-saved-value))
                     (put symbol 'saved-face
                          (get symbol 'initsplit-saved-face))
                     (put symbol 'initsplit-saved-to custom-file))
                 ; else, let custom think it hasn't been changed.
                 (put symbol 'saved-value nil)
                 (put symbol 'saved-face nil)))))

          ad-do-it))

    ;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; unwind-protect cleanup
    ;;;;;;;;;;;;;;;;;;;;;;;;;

    ;; Remove save-buffer advice
    (initsplit-enable-modified-p-correction nil)

    ;; restore the saved-value properties
    (mapatoms
     (lambda (symbol)
       (put symbol 'saved-value (get symbol 'initsplit-saved-value))
       (put symbol 'saved-face (get symbol 'initsplit-saved-face))
       (put symbol 'initsplit-saved-value nil)
       (put symbol 'initsplit-saved-face nil)))))

(defun initsplit-current-file-truename ()
  (file-truename (buffer-file-name (current-buffer))))

(defun initsplit-custom-file ()
  (or custom-file user-init-file))

(defun initsplit-in-file-p (file)
  (string= (file-truename file) (initsplit-current-file-truename)))

(defun initsplit-in-custom-file-p ()
  (initsplit-in-file-p (initsplit-custom-file)))

(defun initsplit-byte-compile-current ()
  (byte-compile-file (initsplit-current-file-truename)))

(defun initsplit-byte-compile-files ()
  (if (initsplit-in-custom-file-p)
      (initsplit-byte-compile-current)
    (let ((cal (initsplit-custom-alist)))
      (while cal
        (if (and (nth 2 (car cal))
                 (initsplit-in-file-p (nth 1 (car cal))))
            (initsplit-byte-compile-current))
        (setq cal (cdr cal))))))

;; (add-hook 'after-save-hook 'initsplit-byte-compile-files t)

;;; Internal Functions:

(defconst initsplit-load-suffix-regexp
  (concat (mapconcat 'regexp-quote (get-load-suffixes) "\\|") "\\'"))

(defun initsplit-strip-lisp-suffix (path)
  (replace-regexp-in-string initsplit-load-suffix-regexp "" path))

(provide 'initsplit)

;; Ensure customization files marked pre-load have been loaded
;; already.
(dolist (s (initsplit-unknown-file-alist))
  (when (initsplit-preload-p s)
    (initsplit-load s)))

(run-hooks 'initsplit-load-hook)

;;; initsplit.el ends here
