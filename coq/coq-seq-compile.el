;;; coq-seq-compile.el --- sequential compilation of required modules

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Authors: Hendrik Tews
;; Maintainer: Hendrik Tews <hendrik@askra.de>

;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; This file implements compilation of required modules. The
;; compilation is done synchonously and sequentially. That is, Proof
;; General blocks before putting newly asserted items into
;; proof-action-list and compiles one module after the other.
;;

;;; Code:

(eval-when-compile
  (require 'proof-compat))

(eval-when-compile
  (defvar queueitems))       ; dynamic scope in p-s-extend-queue-hook

(require 'coq-compile-common)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling -- sequential compilation of required modules
;;


;;; ancestor locking
;;; (unlocking is shared in coq-compile-common.el)

(defun coq-seq-lock-ancestor (span ancestor-src)
  "Lock ancestor ANCESTOR-SRC and register it in SPAN.
Lock only if `coq-lock-ancestor' is non-nil. Further, do nothing,
if ANCESTOR-SRC is already a member of
`proof-included-files-list'. Otherwise ANCESTOR-SRC is locked and
registered in the 'coq-locked-ancestors property of the SPAN to
properly unlock ANCESTOR-SRC on retract."
  (if coq-lock-ancestors
      (let ((true-ancestor-src (file-truename ancestor-src)))
        (unless (member true-ancestor-src proof-included-files-list)
          (proof-register-possibly-new-processed-file true-ancestor-src)
          (span-set-property
           span 'coq-locked-ancestors
           (cons true-ancestor-src
                 (span-property span 'coq-locked-ancestors)))))))

;;; handle Require commands when queue is extended

(defun coq-seq-get-library-dependencies (lib-src-file &optional command-intro)
  "Compute dependencies of LIB-SRC-FILE.
Invoke \"coqdep\" on LIB-SRC-FILE and parse the output to
compute the compiled coq library object files on which
LIB-SRC-FILE depends. The return value is either a string or a
list. If it is a string then an error occurred and the string is
the core of the error message. If the return value is a list no
error occurred and the returned list is the (possibly empty) list
of file names LIB-SRC-FILE depends on.

If an error occurs this funtion displays
`coq--compile-response-buffer' with the complete command and its
output. The optional argument COMMAND-INTRO is only used in the
error case. It is prepended to the displayed command.

LIB-SRC-FILE should be an absolute file name. If it is, the
dependencies are absolute too and the simplified treatment of
`coq-load-path-include-current' in `coq-include-options' won't
break."
  (let ((coqdep-arguments
         ;; FIXME should this use coq-coqdep-prog-args?
         (nconc (coq-include-options coq-load-path (file-name-directory lib-src-file) (coq--pre-v85))
		(list lib-src-file)))
        coqdep-status coqdep-output)
    (when coq--debug-auto-compilation
      (message "call coqdep arg list: %S" coqdep-arguments))
    (with-temp-buffer
      (setq coqdep-status
            (apply 'call-process
                   coq-dependency-analyzer nil (current-buffer) nil
                   coqdep-arguments))
      (setq coqdep-output (buffer-string)))
    (when coq--debug-auto-compilation
      (message "coqdep status %s, output on %s: %s"
	       coqdep-status lib-src-file coqdep-output))
    (if (or
         (not (eq coqdep-status 0))
         (string-match coq-coqdep-error-regexp coqdep-output))
        (let* ((this-command (cons coq-dependency-analyzer coqdep-arguments))
               (full-command (if command-intro
                                 (cons command-intro this-command)
                               this-command)))
          ;; display the error
          (coq-init-compile-response-buffer
           (mapconcat 'identity full-command " "))
          (let ((inhibit-read-only t))
            (with-current-buffer coq--compile-response-buffer
              (insert coqdep-output)))
          (coq-display-compile-response-buffer)
          "unsatisfied dependencies")
      (if (string-match ": \\(.*\\)$" coqdep-output)
          (cdr-safe (split-string (match-string 1 coqdep-output)))
        ()))))

(defun coq-seq-compile-library (src-file)
  "Recompile coq library SRC-FILE.
Display errors in buffer `coq--compile-response-buffer'."
  (message "Recompile %s" src-file)
  (let ((coqc-arguments
         (nconc
          (coq-coqc-prog-args coq-load-path (file-name-directory src-file) (coq--pre-v85))
	  (list src-file)))
        coqc-status)
    (coq-init-compile-response-buffer
     (mapconcat 'identity (cons coq-compiler coqc-arguments) " "))
    (when coq--debug-auto-compilation
      (message "call coqc arg list: %s" coqc-arguments))
    (setq coqc-status
          (apply 'call-process
                 coq-compiler nil coq--compile-response-buffer t coqc-arguments))
    (when coq--debug-auto-compilation
      (message "compilation %s exited with %s, output |%s|"
	       src-file coqc-status
	       (with-current-buffer coq--compile-response-buffer
		 (buffer-string))))
    (unless (eq coqc-status 0)
      (coq-display-compile-response-buffer)
      (let ((terminated-text (if (numberp coqc-status)
                                 "terminated with exit status"
                               "was terminated by signal")))
        (error "ERROR: Recompiling coq library %s %s %s"
               src-file terminated-text coqc-status)))))

(defun coq-seq-compile-library-if-necessary (max-dep-obj-time src obj)
  "Recompile SRC to OBJ if necessary.
This function compiles SRC to the coq library object file OBJ
if one of the following conditions is true:
- a dependency has just been compiled
- OBJ does not exist
- SRC is newer than OBJ
- OBJ is older than the the youngest object file of the dependencies.

Argument MAX-DEP-OBJ-TIME provides the information about the
dependencies. It is either
- 'just-compiled if one of the dependencies of SRC has just
  been compiled
- the time value (see`time-less-or-equal') of the youngest (most
  recently created) object file among the dependencies
- nil if there are no dependencies, or if they are all ignored

If this function decides to compile SRC to OBJ it returns
'just-compiled. Otherwise it returns the modification time of
OBJ.

Note that file modification times inside Emacs have only a
precisision of 1 second. To avoid spurious recompilations we do
not recompile if the youngest object file of the dependencies and
OBJ have identical modification times."
  (let (src-time obj-time)
    (if (eq max-dep-obj-time 'just-compiled)
        (progn
          (coq-seq-compile-library src)
          'just-compiled)
      (setq src-time (nth 5 (file-attributes src)))
      (setq obj-time (nth 5 (file-attributes obj)))
      (if (or
           (not obj-time)                     ; obj does not exist
           (time-less-or-equal obj-time src-time) ; src is newer
           (and
            max-dep-obj-time            ; there is a youngest dependency
                                        ; which is newer than obj
            (time-less-p obj-time max-dep-obj-time)))
          (progn
            (coq-seq-compile-library src)
            'just-compiled)
        (when coq--debug-auto-compilation
	  (message "Skip compilation of %s" src))
        obj-time))))

(defun coq-seq-make-lib-up-to-date (coq-obj-hash span lib-obj-file)
  "Make library object file LIB-OBJ-FILE up-to-date.
Check if LIB-OBJ-FILE and all it dependencies are up-to-date
compiled coq library objects. Recompile the necessary objects, if
not. This function returns 'just-compiled if it compiled
LIB-OBJ-FILE. Otherwise it returns the modification time of
LIB-OBJ-FILE as time value (see `time-less-or-equal').

Either LIB-OBJ-FILE or its source file (or both) must exist when
entering this function.

Argument SPAN is the span of the \"Require\" command.
LIB-OBJ-FILE and its dependencies are locked and registered in
the span for for proper unlocking on retract.

Argument COQ-OBJ-HASH remembers the return values of this
function."
  (let ((result (gethash lib-obj-file coq-obj-hash)))
    (if result
        (progn
          (when coq--debug-auto-compilation
	    (message "Checked %s already" lib-obj-file))
          result)
      ;; lib-obj-file has not been checked -- do it now
      (message "Check %s" lib-obj-file)
      (if (coq-compile-ignore-file lib-obj-file)
          ;; return minimal time for ignored files
          (setq result '(0 0))
        (let* ((lib-src-file
                (expand-file-name
		 (coq-library-src-of-vo-file lib-obj-file)))
               dependencies deps-mod-time)
          (if (file-exists-p lib-src-file)
              ;; recurse into dependencies now
              (progn
                (setq dependencies
		      (coq-seq-get-library-dependencies lib-src-file))
                (if (stringp dependencies)
                    (error "File %s has %s" lib-src-file dependencies))
                (setq deps-mod-time
                      (mapcar
                       (lambda (dep)
                         (coq-seq-make-lib-up-to-date coq-obj-hash span dep))
                       dependencies))
                (setq result
                      (coq-seq-compile-library-if-necessary
                       (coq-max-dep-mod-time deps-mod-time)
                       lib-src-file lib-obj-file)))
            (message "coq-auto-compile: no source file for %s" lib-obj-file)
            (setq result
                  ;; 5 value: last modification time
                  (nth 5 (file-attributes lib-obj-file))))
          (coq-seq-lock-ancestor span lib-src-file)))
      ;; at this point the result value has been determined
      ;; store it in the hash then
      (puthash lib-obj-file result coq-obj-hash)
      result)))

(defun coq-seq-auto-compile-externally (span qualified-id
					     absolute-module-obj-file)
  "Make MODULE up-to-date according to `coq-compile-command'.
Start a compilation to make ABSOLUTE-MODULE-OBJ-FILE up-to-date.
The compilation command is derived from `coq-compile-command' by
substituting certain keys, see `coq-compile-command' for details.
If `coq-confirm-external-compilation' is t then the user
must confirm the external command in the minibuffer, otherwise
the command is executed without confirmation.

Argument SPAN is the span of the \"Require\" command. The
ancestor ABSOLUTE-MODULE-OBJ-FILE is locked and registered in the
span for for proper unlocking on retract.

This function uses the low-level interface `compilation-start',
therefore the customizations for `compile' do not apply."
  (unless (coq-compile-ignore-file absolute-module-obj-file)
    (let* ((local-compile-command coq-compile-command)
           (physical-dir (file-name-directory absolute-module-obj-file))
           (module-object (file-name-nondirectory absolute-module-obj-file))
           (module-source (coq-library-src-of-vo-file module-object))
           (requiring-file buffer-file-name))
      (mapc
       (lambda (substitution)
         (setq local-compile-command
               (replace-regexp-in-string
                (car substitution) (eval (car (cdr substitution)))
                local-compile-command)))
       coq-compile-substitution-list)
      (if coq-confirm-external-compilation
          (setq local-compile-command
                (read-shell-command
                 "Coq compile command: " local-compile-command
                 (if (equal (car coq-compile-history) local-compile-command)
                     '(coq-compile-history . 1)
                   'coq-compile-history))))
      ;; buffers have already been saved before we entered this function
      ;; the next line is probably necessary to make recompile work
      (setq-default compilation-directory default-directory)
      (compilation-start local-compile-command)
      (coq-seq-lock-ancestor
       span
       (coq-library-src-of-vo-file absolute-module-obj-file)))))

(defun coq-seq-map-module-id-to-obj-file (module-id span &optional from)
  "Map MODULE-ID to the appropriate coq object file.
The mapping depends of course on `coq-load-path'. The current
implementation invokes coqdep with a one-line require command.
This is probably slower but much simpler than modelling coq file
loading inside ProofGeneral. Argument SPAN is only used for error
handling. It provides the location information of MODULE-ID for a
decent error message.

A peculiar consequence of the current implementation is that this
function returns () if MODULE-ID comes from the standard library."
  (let ((coq-load-path
         (if coq-load-path-include-current
             (cons default-directory coq-load-path)
           coq-load-path))
        (coq-load-path-include-current nil)
        (temp-require-file (make-temp-file "ProofGeneral-coq" nil ".v"))
        (coq-string (concat (if from (concat "From " from " ") "") "Require " module-id "."))
        result)
    (unwind-protect
        (progn
          (with-temp-file temp-require-file
            (insert coq-string))
          (setq result
                (coq-seq-get-library-dependencies
                 temp-require-file
                 (concat "echo \"" coq-string "\" > " temp-require-file))))
      (delete-file temp-require-file))
    (if (stringp result)
        ;; Error handling: coq-seq-get-library-dependencies was not able to
        ;; translate module-id into a file name. We insert now a faked error
        ;; message into coq--compile-response-buffer to make next-error happy.
        (let ((error-message
               (format "Cannot find library %s in loadpath" module-id))
              (inhibit-read-only t))
          ;; Writing a message into coq--compile-response-buffer for next-error
          ;; does currently not work. We do have exact position information
          ;; about the span, but we don't know how much white space there is
          ;; between the start of the span and the start of the command string.
          ;; Check that coq--compile-response-buffer is a valid buffer!
          ;; (with-current-buffer coq--compile-response-buffer
          ;;   (insert
          ;;    (format "File \"%s\", line %d\n%s.\n"
          ;;            (buffer-file-name (span-buffer span))
          ;;            (with-current-buffer (span-buffer span)
          ;;              (line-number-at-pos (span-start span)))
          ;;            error-message)))
          ;; (coq-display-compile-response-buffer)
          (error error-message)))
    (assert (<= (length result) 1)
            "Internal error in coq-seq-map-module-id-to-obj-file")
    (car-safe result)))

(defun coq-seq-check-module (coq-object-local-hash-symbol span module-id &optional from)
  "Locate MODULE-ID and compile if necessary.
If `coq-compile-command' is not nil the whole task of checking which
modules need compilation and the compilation itself is done by an external
process. If `coq-compile-command' is nil ProofGeneral computes the
dependencies with \"coqdep\" and compiles modules as necessary. This internal
checking does currently not handle ML modules.

Argument SPAN is the span of the \"Require\" command. Locked
ancestors are registered in its 'coq-locked-ancestors property
for proper unlocking on retract.

Argument COQ-OBJECT-LOCAL-HASH-SYMBOL provides a place to store
the coq-obj-hash, which is used during internal
compilation (see `coq-seq-make-lib-up-to-date'). This way one hash
will be used for all \"Require\" commands added at once to the
queue."
  (let ((module-obj-file (coq-seq-map-module-id-to-obj-file module-id span from)))
    ;; coq-seq-map-module-id-to-obj-file currently returns () for
    ;; standard library modules!
    (when module-obj-file
      (if (> (length coq-compile-command) 0)
          (coq-seq-auto-compile-externally span module-id module-obj-file)
        (unless (symbol-value coq-object-local-hash-symbol)
          (set coq-object-local-hash-symbol (make-hash-table :test 'equal)))
        (coq-seq-make-lib-up-to-date (symbol-value coq-object-local-hash-symbol)
                                 span module-obj-file)))))

(defun coq-seq-preprocess-require-commands ()
  "Coq function for `proof-shell-extend-queue-hook'.
If `coq-compile-before-require' is non-nil, this function performs the
compilation (if necessary) of the dependencies."
  (if coq-compile-before-require
      (let (;; coq-object-hash-symbol serves as a pointer to the
            ;; coq-obj-hash (see coq-seq-make-lib-up-to-date). The hash
            ;; will be initialized when needed and stored in the value
            ;; cell of coq-object-hash-symbol. The symbol is initialized
            ;; here to use one hash for all the requires that are added now.
            (coq-object-hash-symbol nil)
            string)
        (dolist (item queueitems)
          (let ((string (mapconcat 'identity (nth 1 item) " ")))
            (when (and string
                       (string-match coq-require-command-regexp string))
              (let ((span (car item))
                    (start (match-end 0))
                    (prefix (match-string 1 string)))
                (span-add-delete-action
                 span
                 `(lambda ()
                    (coq-unlock-all-ancestors-of-span ,span)))
                (coq-compile-save-some-buffers)
                ;; now process all required modules
                (while (string-match coq-require-id-regexp string start)
                  (setq start (match-end 0))
                  (coq-seq-check-module 'coq-object-hash-symbol span
                                    (match-string 1 string) prefix)))))))))


(provide 'coq-seq-compile)



;;   Local Variables: ***
;;   coding: utf-8 ***
;;   End: ***

;;; coq-seq-compile.el ends here
