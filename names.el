;;; names.el --- Namespaces for emacs-lisp. Avoid name clobbering without hiding symbols.  -*- lexical-binding:t -*-

;; Copyright (C) 2014-2015 Free Software Foundation, Inc.

;; Author: Artur Malabarba <emacs@endlessparentheses.com>
;; URL: https://github.com/Malabarba/names
;; Version: 20151201.0
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: extensions lisp

;;; Commentary:
;;
;; The description is way too large to sanely write here, below is a
;; summary. For a complete description, please visit the package's
;; frontpage with `M-x names-view-manual', or see the Readme file on
;; https://raw.githubusercontent.com/Malabarba/names/master/Readme.org

;;; License:
;;
;; This file is part of GNU Emacs.
;;
;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; News:
;;; Code:


(require 'cl-lib)
;;; This is a patch because edebug binds under `C-x'.
;; If `C-x' is not a prefix.
(unless (consp (key-binding "\C-x"))
  ;; Disable the `C-xC-a' binds.
  (defvar edebug-inhibit-emacs-lisp-mode-bindings)
  (setq edebug-inhibit-emacs-lisp-mode-bindings t)
  ;; And the `C-xX' binds.
  (defvar global-edebug-prefix)
  (when (ignore-errors
          (or (null (boundp 'global-edebug-prefix))
              (eq ?\C-x (elt global-edebug-prefix 0))))
    (setq global-edebug-prefix "")))
(require 'edebug)
(require 'bytecomp)
(require 'advice)

;;; Support
(declare-function names--autoload-do-load "names" 2)
(defalias 'names--function-get
  (if (fboundp 'function-get) #'function-get

    (defun names--autoload-do-load (def name)
      "Load autoloaded definition DEF from function named NAME."
      (unless (load (cadr def) 'noerror)
        (error "Macro `%s' is autoloaded, but its file (%s) couldn't be loaded"
          name (cadr def)))
      (symbol-function name))

    (lambda (f prop &rest _)
      "Return the value of property PROP of function F.
If F is an autoloaded macro, try to autoload it in the hope that
it will set PROP."
      (let ((val nil))
        (while (and (symbolp f)
                    (null (setq val (get f prop)))
                    (fboundp f))
          (let ((fundef (symbol-function f)))
            (if (and (names--autoloadp fundef)
                     (not (equal fundef (names--autoload-do-load fundef f))))
                nil                     ;Re-try `get' on the same `f'.
              (setq f fundef))))
        val))))

(defalias 'names--compat-macrop
  (if (fboundp 'macrop) #'macrop
    (lambda (object)
      "Non-nil if and only if OBJECT is a macro."
      (let ((def (or (ignore-errors (indirect-function object t))
                     (ignore-errors (indirect-function object)))))
        (when (consp def)
          (or (eq 'macro (car def))
              (and (names--autoloadp def) (memq (nth 4 def) '(macro t)))))))))

(defalias 'names--autoloadp
  (if (fboundp 'autoloadp) #'autoloadp
    (lambda (object)
      "Non-nil if OBJECT is an autoload."
      (eq 'autoload (car-safe object)))))

(unless (get-edebug-spec 'cl-defun)
  (def-edebug-spec cl-defun defun*))
(unless (get-edebug-spec 'cl-defmacro)
  (def-edebug-spec cl-defmacro defmacro*))
(unless (get-edebug-spec 'setq-local)
  (def-edebug-spec setq-local setq))
(unless (get-edebug-spec 'loop)
  (def-edebug-spec loop
    (&rest &or
           ;; These are usually followed by a symbol, but it can
           ;; actually be any destructuring-bind pattern, which
           ;; would erroneously match `form'.
           [[&or "for" "as" "with" "and"] sexp]
           ;; These are followed by expressions which could
           ;; erroneously match `symbolp'.
           [[&or "from" "upfrom" "downfrom" "to" "upto" "downto"
                 "above" "below" "by" "in" "on" "=" "across"
                 "repeat" "while" "until" "always" "never"
                 "thereis" "collect" "append" "nconc" "sum"
                 "count" "maximize" "minimize" "if" "unless"
                 "return"] form]
           ;; Simple default, which covers 99% of the cases.
           symbolp form)))


;;; ---------------------------------------------------------------
;;; Variables
(defconst names-version "20151201.0" "Version of the names.el package.")

(defvar names--name nil
  "Name of the current namespace inside the `define-namespace' macro.")
(defvar names--regexp nil "Regexp matching `names--name'.")

(defvar names--load-file (and load-file-name (expand-file-name load-file-name))
  "The file where the current version of Names was loaded.
This is used by `names--check-for-update' to check if a new
version has been installed.")

(defvar names--bound nil
  "List of variables defined in this namespace.")
(defvar names--fbound nil
  "List of functions defined in this namespace.")
(defvar names--macro nil
  "List of macros defined in this namespace.")

(defvar names--keywords nil
  "Keywords that were passed to the current namespace.
See `names--keyword-list' for a list and description of possible
keywords.")

(defvar names--local-vars nil
  "Non-global vars that are let/lambda bound at the moment.
These won't be namespaced, as local takes priority over namespace.")

(defvar names--protection nil
  "Leading chars used to identify protected symbols.
Don't customise this.
Instead use the :protection keyword when defining the
namespace.")

(defvar names--current-run nil
  "Either 1 or 2, depending on which runthrough we're in.")

(defvar names--var-list
  '(names--name names--regexp names--bound
                names--version
                names--package names--group-parent
                names--macro names--current-run
                names--fbound names--keywords
                names--local-vars names--protection)
  "List of variables the user shouldn't touch.")

;;;###autoload
(defvar names--inside-make-autoload nil
  "Used in `make-autoload' to indicate we're making autoloads.")

(defvar names--package nil
  "Package, name to be used by the :group and :version keywords.
Is derived from `load-file-name', unless the :package keyword is
passed to `define-namespace'.")

(defvar names--group-parent nil
  "The name of the parent to be given to `defgroup'.
Is only non-nil if the :group keyword is passed to `define-namespace'.")

(defvar names--version nil
  "The version number given by :version.
Used to define a constant and a command.")

(defvar names--functionlike-macros nil
  "Function-like macros, even if their debug-spec says otherwise.
When expanding the namespace, these macros will be treated
exactly like functions. This means that their contents will be
namespaced like regular function arguments.

To add macros to this list, pass the :functionlike-macros keyword
to your namespace along with a list of macro names (as unquoted
symbols).
Example:

    (define-namespace foo-
    :functionlike-macros (-> ->> thread-first thread-last)
    ;; Rest of code
    )")

(defconst names--keyword-list
  `((:group
     1 ,(lambda (x)
          (if (or (symbolp x) (listp x))
              (setq names--group-parent x)
            (names--warn
             "Argument given to :group is not a symbol: %s" x)))
     "Indicate `define-namespace' should make a `defgroup' for you.
The name of the group is the package name (see :package keyword).
This keyword should be given one argument, the name of the PARENT
group as an unquoted symbol.

Alternatively, the argument can be a list, in which case it is a
list of arguments to be passed to `defgroup' (essentially, a full
group definition without the leading `defgroup').

If this keyword is provided, besides including a defgroup, Names
will also include a :group keyword in every `defcustom' (and
similar forms) that don't already contain one.")

    (:version
     1
     ,(lambda (x)
        (if (stringp x)
            (setq names--version x)
          (names--warn
           "Argument given to :version is not a string: %s" x)))
     "Indicate `define-namespace' should define the version number.
This keyword should be given one argument, a string describing
the package's version number.

With this, Names will generate a `defconst' and an interactive
`defun', each named `PACKAGE-NAME-version'. The function messages
and returns the version number. See the :package keyword.")

    (:package
     1
     ,(lambda (x)
        (if (symbolp x)
            (setq names--package x)
          (names--warn
           "Argument given to :package is not a symbol: %s" x)))
     "Set the name of this package to the given symbol.
This keyword should be given one argument, a symbol corresponding
to the name of this package.

If this keyword isn't used, the package name is taken as the the
file's basename, but only if its actually needed. This name is
needed by the :version and :group keywords.")

    (:protection
     1
     ,(lambda (x)
        (let ((val (symbol-name x)))
          (setq names--protection
                (format "\\`%s" (regexp-quote val)))))
     "Change the value of the `names--protection' variable.")

    (:functionlike-macros
     1
     ,(lambda (x) (setq names--functionlike-macros
                   (append x names--functionlike-macros)))
     "A list of values to be appended to `names--functionlike-macros'.")

    (:no-let-vars
     0 nil
     "Indicates variables assigned in let-bind are NOT candidates for namespacing.")

    (:verbose
     0 nil
     "Cause a message to be called on each special form.")

    (:global
     0 nil
     "Accept namespaced names from outside current namespace definition.")

    (:assume-var-quote
     0 nil
     "Indicate symbols quoted with `quote' should be considered variable names.")

    (:dont-assume-function-quote
     0 nil
     "Indicate symbols quoted with `function' should NOT be considered function names.")

    (:clean-output
     0 nil
     "Indicate only forms actually inside the namespace should be present in the output.
This is for internal use. It is used by `names-eval-defun' to
prevent `define-namespace' from adding things like `defgroup' or
`defconst's to the output."))
  "List of keywords used by `define-namespace'.
Each element is a list containing
    (KEYWORD N DEFINITION DOCUMENTATION)
where:

- KEYWORD is the keyword's name, a symbol satifying `keywordp'.
- N is the number of arguments it takes, an integer.
- DEFINITION is a function (symbol or lambda) that takes N
arguments and does whatever you need for implementing the
keyword.
- DOCUMENTATION is a string explaining the keyword's
behaviour.")

(defmacro names--prepend (sbl)
  "Return namespace+SBL."
  (declare (debug (symbolp)))
  `(intern (format "%s%s" names--name ,sbl)))


(defmacro names--filter-if-bound (var &optional pred)
  "If VAR is bound and is a list, take the car of its elements which satify PRED."
  (declare (debug (symbolp &optional function-form)))
  `(when (boundp ',var)
     (remove
      nil
      (mapcar (lambda (x) (when (funcall (or ,pred #'identity) (or (car-safe x) x))
                            (or (car-safe x) x)))
              ,var))))

(defmacro names--next-keyword (body)
  "If car of BODY is a known keyword, `pop' it (and its arguments) from body.
Returns a list (KEYWORD . ARGUMENTLIST)."
  (declare (debug sexp))
  `(let ((kar (car-safe ,body))
         out n)
     (and kar
          (keywordp kar)
          (setq n (assoc kar names--keyword-list))
          (setq n (cadr n))
          (dotimes (_ (1+ n) out)
            (push (pop ,body) out))
          (nreverse out))))

(defvar names--has-reloaded nil
  "Whether `names--reload-if-upgraded' has already been called in this run.")


;;; ---------------------------------------------------------------
;;; The Main Macro and Main Function.
;;;###autoload
(defmacro define-namespace (name &rest body)
  "Inside the namespace NAME, execute BODY.
NAME can be any symbol (not quoted), but it's highly recommended
to use some form of separator (such as :, /, or -). For a
complete description of this macro, please visit the frontpage
with \\[names-view-manual].

In summary, this macro has two main effects:

1. Any definitions inside BODY will have NAME prepended to the
symbol given. Ex:

    (define-namespace foo-
    (defvar bar 1 \"docs\")
    )

expands to

    (defvar foo-bar 1 \"docs\")


2. Any function calls and variable names get NAME prepended to
them if such a variable or function exists. Ex:

    (define-namespace foo:
    (defun message (x y) nil)
    (message \"%s\" my-var)
    )

expands to

    (defun foo:message (x y) nil)
    (foo:message \"%s\" my-var)

Note how `message' is expanded to `foo:message' in the second
form, because that function exists. Meanwhile, `bar' is left
untouched because `foo:bar' is not a known variable name.

===============================

AUTOLOAD

In order for `define-namespace' to work with \";;;###autoload\"
comments must replace all instances of \";;;###autoload\" inside
your `define-namespace' with `:autoload'.
Afterwards, add an \";;;###autoload\" comment just above your
`define-namespace'.

===============================

KEYWORDS

Immediately after NAME you may add keywords which customize the
behaviour of `define-namespace'. For a list of possible keywords
and a description of their effects, see the variable
`names--keyword-list'.

\(fn NAME [KEYWORD ...] BODY)"
  (declare (indent (lambda (&rest x) 0))
           (debug (&define name [&rest keywordp &optional [&or symbolp (symbolp . symbolp)]] body)))
  (let ((names--has-reloaded names--has-reloaded))
    ;; This was to avoid an infinite recursion, but the bug turned out
    ;; to be somewhere else. Still, I see no reason to erase this.
    (unless names--has-reloaded
      (setq names--has-reloaded t)
      (names--reload-if-upgraded))
    (names--error-if-using-vars)
    (names--define-namespace-implementation name body)))

(defun names--define-namespace-implementation (name body)
  "Namespace BODY using NAME.
See `define-namespace' for more information."
  (unwind-protect
      (let* ((names--name name)
             (names--regexp
              (concat "\\`" (regexp-quote (symbol-name name))))
             (names--current-run 0)
             ;; Use the :protection keyword to change this.
             (names--protection "\\`::")
             (names--bound
              (names--remove-namespace-from-list
               (names--filter-if-bound byte-compile-bound-variables)
               (names--filter-if-bound byte-compile-variables)))
             (names--fbound
              (names--remove-namespace-from-list
               (names--filter-if-bound byte-compile-macro-environment 'names--compat-macrop)
               (names--filter-if-bound byte-compile-function-environment 'names--compat-macrop)))
             (names--macro
              (names--remove-namespace-from-list
               (names--filter-if-bound byte-compile-macro-environment (lambda (x) (not (names--compat-macrop x))))
               (names--filter-if-bound byte-compile-function-environment (lambda (x) (not (names--compat-macrop x))))))
             (names--functionlike-macros names--functionlike-macros)
             names--keywords names--local-vars key-and-args
             names--version names--package names--group-parent)
        ;; Read keywords
        (while (setq key-and-args (names--next-keyword body))
          (names--handle-keyword key-and-args)
          (push key-and-args names--keywords))

        ;; First have to populate the bound and fbound lists. So we read
        ;; the entire form (without return it).
        (if names--inside-make-autoload
            ;; Dependencies haven't been loaded during autoload
            ;; generation, so we better ignore errors here. Ideally we
            ;; would only go through the forms marked for autoloading,
            ;; but then we wouldn't know what symbols are var/function
            ;; names.
            (mapc (lambda (form) (ignore-errors (names-convert-form form))) body)
          (mapc #'names-convert-form body))
        (setq names--current-run (1+ names--current-run))

        ;; Then we go back and actually namespace the entire form, which
        ;; we'll later return so that it can be evaluated.
        (setq body
              (cons
               'progn
               (append
                (when (and names--group-parent
                           (null (names--keyword :clean-output)))
                  (list (names--generate-defgroup)))
                (when (and names--version
                           (null (names--keyword :clean-output)))
                  ;; `names--generate-version' returns a list.
                  (names--generate-version))
                (mapcar 'names-convert-form
                        ;; Unless we're in `make-autoload', then just return autoloads.
                        (if names--inside-make-autoload
                            (names--extract-autoloads body)
                          body)))))

        ;; On emacs-version < 24.4, the byte-compiler cannot expand a
        ;; macro if it is being called in the same top-level form as
        ;; it was defined. That's a problem for us, since the entire
        ;; namespace is a single top-level form (we return a `progn').
        ;; The solution is for us to add the macros to
        ;; `byte-compile-macro-environment' ourselves.
        (if (and (boundp 'byte-compile-current-buffer)
                 byte-compile-current-buffer
                 (null names--inside-make-autoload)
                 (version< emacs-version "24.4"))
            (let ((byte-compile-macro-environment
                   (when (boundp 'byte-compile-macro-environment)
                     byte-compile-macro-environment)))
              (mapc #'names--add-macro-to-environment (cdr body))
              (macroexpand-all body byte-compile-macro-environment))
          body))

    ;; Exiting the `unwind-protect'.
    (mapc (lambda (x) (set x nil)) names--var-list)))

(defun names--reload-if-upgraded ()
  "Verify if there's a more recent version of Names in the `load-path'.
If so, evaluate it."
  (ignore-errors
    (require 'find-func)
    (let ((lp (expand-file-name (find-library-name "names")))
          new-version)
      (when (and lp
                 (not (string= lp names--load-file))
                 (file-readable-p lp))
        (with-temp-buffer
          (insert-file-contents-literally lp)
          (goto-char (point-min))
          (setq new-version
                (save-excursion
                  (when (search-forward-regexp
                         "(defconst\\s-+names-version\\s-+\"\\([^\"]+\\)\"" nil t)
                    (match-string-no-properties 1))))
          (when (and new-version (version< names-version new-version))
            (eval-buffer nil lp)))))))

(defun names-convert-form (form)
  "Do namespace conversion on FORM.
FORM is any legal elisp form.
Namespace name is defined by the global variable `names--name'.

See macro `namespace' for more information."
  (cond
   ((null form) form)
   ;; Function calls
   ((consp form)
    (let ((kar (car form))
          func)
      (cond
       ;; If symbol is protected, clean it.
       ((and (symbolp kar)
             (setq func (names--remove-protection kar)))
        (names--message "Protected: %s" kar)
        ;; And decide what to do with it.
        (names--handle-args func (cdr form)))

       ;; If kar is a list, either 1) it's a lambda form, 2) it's a
       ;; macro we don't know about yet, 3) we have a bug.
       ((consp kar)
        (when (and (null (functionp kar))
                   (> names--current-run 1))
          (names--warn "Ran into the following strange form.
Either it's an undefined macro, a macro with a bad debug declaration, or we have a bug.\n%s" form))
        (mapcar 'names-convert-form form))

       ;; Namespaced Functions/Macros
       ((names--fboundp kar)
        (names--message "Namespaced: %s" kar)
        (names--args-of-function-or-macro
         (names--prepend kar) (cdr form) (names--macrop kar)))

       ;; General functions/macros/special-forms
       (t (names--handle-args kar (cdr form))))))
   ;; Variables
   ((symbolp form)
    (names--message "Symbol handling: %s" form)
    ;; If symbol is protected, clean it and don't namespace it.
    (or (names--remove-protection form)
        ;; Otherwise, namespace if possible.
        (if (names--boundp form)
            (names--prepend form)
          form)))
   ;; Values
   (t form)))


;;; ---------------------------------------------------------------
;;; Some auxiliary functions
(defun names-view-manual ()
  "Call `browse-url' to view the manual of the Names package."
  (interactive)
  (browse-url "http://github.com/Malabarba/names"))

(defun names--package-name ()
  "Return the package name as a symbol.
Decide package name based on several factors. In order:
    1. The :package keyword,
    2. The namespace NAME, removing the final char."
  (or names--package
      (let ((package (symbol-name names--name)))
        (prog1 (setq names--package
                     (intern (substring package 0 -1)))
          (names--warn "No :package given. Guessing `%s'"
                       names--package)))))

(defun names--generate-defgroup ()
  "Return a `defgroup' form for the current namespace."
  (if (listp names--group-parent)
      (cons 'defgroup names--group-parent)
    (list 'defgroup (names--package-name) nil
          (format "Customization group for %s." (names--package-name))
          :prefix (symbol-name names--name)
          :group `',names--group-parent)))

(defun names--generate-version ()
  "Return a `defun' and a `defconst' forms declaring the package version.
Also adds `version' to `names--fbound' and `names--bound'."
  (add-to-list 'names--fbound 'version)
  (add-to-list 'names--bound 'version)
  (list
   (list 'defconst (names--prepend 'version)
         names--version
         (format "Version of the %s package." (names--package-name)))
   (list 'defun (names--prepend 'version) nil
         (format "Version of the %s package." (names--package-name))
         '(interactive)
         `(message
           ,(format "%s version: %s" (names--package-name) names--version))
         names--version)))

(defun names--add-macro-to-environment (form)
  "If FORM declares a macro, add it to `byte-compile-macro-environment'."
  (let ((expansion form))
    (while (names--compat-macrop (car-safe expansion))
      (setq expansion
            (ignore-errors (macroexpand
                            expansion byte-compile-macro-environment))))
    (and expansion
         (car-safe expansion)
         (or (and (memq (car-safe expansion) '(progn prog1 prog2))
                  (mapc #'names--add-macro-to-environment (cdr expansion)))
             (and (eq 'defalias (car-safe expansion))
                  (let ((def (ignore-errors (eval (nth 2 expansion)))))
                    (and (names--compat-macrop def)
                         (push (cons (ignore-errors
                                       (eval (nth 1 expansion)))
                                     (cdr-safe def))
                               byte-compile-macro-environment))))))))

;;;###autoload
(eval-after-load 'find-func
  '(defadvice find-function-search-for-symbol
       (around names-around-find-function-search-for-symbol-advice
               (symbol type library) activate)
     "Make sure `find-function-search-for-symbol' understands namespaces."
     ad-do-it
     (ignore-errors
       (unless (cdr ad-return-value)
         (with-current-buffer (car ad-return-value)
           (search-forward-regexp "^(define-namespace\\_>")
           (skip-chars-forward "\r\n[:blank:]")
           (let* ((names--regexp
                   (concat "\\`" (regexp-quote
                                  (symbol-name (read (current-buffer))))))
                  (short-symbol
                   ;; We manually implement `names--remove-namespace'
                   ;; because it might not be loaded.
                   (let ((name (symbol-name symbol)))
                     (when (string-match names--regexp name)
                       (intern (replace-match "" nil nil name))))))
             (when short-symbol
               (ad-set-arg 0 short-symbol)
               ad-do-it)))))))

(defun names--extract-autoloads (body)
  "Return a list of the forms in BODY preceded by :autoload."
  (let (acons)
    (when (setq acons (memq :autoload body))
      (cons
       (cadr acons)
       (names--extract-autoloads (cdr (cdr acons)))))))

;;;###autoload
(defadvice make-autoload (around names-before-make-autoload-advice
                                 (form file &optional expansion) activate)
  "Make sure `make-autoload' understands `define-namespace'.
Use the `names--inside-make-autoload' variable to indicate to
`define-namespace' that we're generating autoloads."
  ;; We used to have a letbind here, but this was causing a void
  ;; variable bug on Emacs 24.3.
  (require 'names)
  (if (null (eq (car-safe form) 'define-namespace))
      ad-do-it
    (setq names--inside-make-autoload t)
    (setq form (macroexpand form))
    (setq names--inside-make-autoload nil)
    ;; Up to 24.2 `make-autoload' couldn't handle `progn's.
    (if (version< emacs-version "24.3")
        (setq ad-return-value
              (cons 'progn
                    (mapcar (lambda (x) (names--make-autoload-compat x file))
                            (cdr form))))
      (ad-set-arg 2 'expansion)
      (ad-set-arg 0 form)
      ad-do-it)))

(defun names--make-autoload-compat (form file)
  (if (eq (car-safe form) 'defalias)
      form
    (make-autoload form file)))

(defvar names--ignored-forms '(declare)
  "The name of functions/macros/special-forms which we return without reading.")

(defun names--handle-args (func args)
  "Generic handling for the form (FUNC . ARGS), without namespacing FUNC."
  (if (memq func names--ignored-forms)
      (cons func args)
    ;; TODO: Speed this up. Just change it to an alist or a hash-table.
    (let ((handler (intern-soft (format "names--convert-%s" func))))
      ;; Some function-like forms get special handling.
      ;; That's anything with a names--convert-%s function defined.
      (if (fboundp handler)
          (progn (names--message "Special handling: %s" handler)
                 (funcall handler (cons func args)))
        ;; If it isn't special, it's either a function or a macro.
        (names--args-of-function-or-macro func args (names--compat-macrop func))))))

(defun names--message (f &rest rest)
  "If :verbose is on, pass F and REST to `message'."
  (when (names--keyword :verbose)
    (apply #'message (concat "[names] " f) rest)))

(defun names--warn (f &rest rest)
  "Pass F and REST to `message', unless byte-compiling or non-interactive."
  (unless (and (null (names--keyword :verbose))
               (and (boundp 'byte-compile-function-environment)
                    byte-compile-function-environment))
    (apply #'message (concat "[names] " f) rest)))

(defun names--error-if-using-vars ()
  "Remind the developer that variables are not customizable."
  (mapcar
   (lambda (x)
     (when (eval x)
       (error "[names] Global value of variable %s should be nil! %s"
              x "Set it using keywords instead")))
   names--var-list))

(defun names--remove-namespace-from-list (&rest lists)
  "Return a concatenated un-namespaced version of LISTS.
Symbols in LISTS that aren't namespaced are removed, symbols that
are namespaced become un-namespaced."
  (delq nil (mapcar 'names--remove-namespace (apply #'append lists))))

(defun names--remove-namespace (symbol)
  "Return SYMBOL with namespace removed, or nil if it wasn't namespaced."
  (names--remove-regexp symbol names--regexp))

(defun names--remove-protection (symbol)
  "Remove the leading :: from SYMBOL if possible, otherwise return nil."
  (names--remove-regexp symbol names--protection))

(defun names--remove-regexp (s r)
  "Return S with regexp R removed, or nil if S didn't match."
  (let ((name (symbol-name s)))
    (when (string-match r name)
      (intern (replace-match "" nil nil name)))))

(defun names--quote-p (sbl)
  "Is SBL a function which quotes its argument?"
  (memq sbl '(quote function)))

(defun names--fboundp (sbl)
  "Is namespace+SBL a fboundp symbol?"
  (or (memq sbl names--fbound)
      (memq sbl names--macro)
      (and (names--keyword :global)
           (fboundp (names--prepend sbl)))))

(defun names--macrop (sbl)
  "Is namespace+SBL a fboundp symbol?"
  (or (memq sbl names--macro)
      (and (names--keyword :global)
           (names--compat-macrop (names--prepend sbl)))))

(defun names--keyword (keyword)
  "Was KEYWORD one of the keywords passed to the `namespace' macro?"
  (assoc keyword names--keywords))

(defun names--boundp (sbl)
  "Is namespace+SBL a boundp symbol?
If SBL has a let binding, that takes precendence so this also
returns nil."
  (and (null (memq sbl names--local-vars))
       (or (memq sbl names--bound)
           (and (names--keyword :global)
                (boundp (names--prepend sbl))))))

(defvar names--verbose nil
  "If non-nil, verbose message are printed regardless of the :verbose keyword.
Use this to easily turn on verbosity during tests.")

(defun names--args-of-function-or-macro (function args macro)
  "Namespace FUNCTION's arguments ARGS, with special treatment if MACRO is non-nil."
  (if macro
      (let ((it (names--get-edebug-spec function))
            (names--verbose (eq function 'push)))
        (names--message "Edebug-spec of `%s' is %s" function it)
        ;; Macros where we evaluate all arguments are like functions.
        (if (or (equal it t)
                (memq function names--functionlike-macros))
            (names--args-of-function-or-macro function args nil)
          ;; Macros where nothing is evaluated we can just return.
          (if (equal it 0)
              (cons function args)
            ;; Other macros are complicated. Ask edebug for help.
            (names--macro-args-using-edebug (cons function args)))))
    ;; We just convert the arguments of functions.
    (cons function (mapcar 'names-convert-form args))))

(defun names--get-edebug-spec (name)
  "Get 'edebug-form-spec property of symbol NAME."
  ;; Get the spec of symbol resolving all indirection.
  (let ((spec nil)
        (indirect name))
    (while (progn
             (and (symbolp indirect)
                  (setq indirect
                        (names--function-get
                         indirect 'edebug-form-spec 'macro))))
      ;; (edebug-trace "indirection: %s" edebug-form-spec)
      (setq spec indirect))
    spec))

(defvar names--is-inside-macro nil
  "Auxiliary var used in `names--macro-args-using-edebug'.")

(defvar names--gensym-counter 0
  "Counter used to uniquify symbols generated `names--gensym'.")

(defun names--macro-args-using-edebug (form)
  "Namespace the arguments of macro FORM by hacking into edebug.
This takes advantage of the fact that macros (should) declare a
`debug' specification which tells us which arguments are actually
Elisp forms.

Ideally, we would read this specification ourselves and see how
it matches (cdr FORM), but that would take a lot of work and
we'd be reimplementing something that edebug already does
phenomenally. So we hack into edebug instead."
  (require 'edebug)
  (require 'cl-lib)
  (cl-letf
      ((max-lisp-eval-depth 3000)
       (edebug-all-forms t)
       (edebug-all-defs t)
       (names--is-inside-macro form)
       ;; Prevent excessive messaging.
       ;; TODO: Don't do this if `message' is advised.
       ((symbol-function 'message) #'names--edebug-message)
       ;; Older edebugs have poor `get-edebug-spec'.
       ((symbol-function 'get-edebug-spec) #'names--get-edebug-spec)
       ;; Give symbols our own name.
       ((symbol-function 'cl-gensym) #'names--gensym)
       ;; Stop at one level deep.
       ((symbol-function 'edebug-form) #'names--edebug-form)
       ;; Don't actually wrap anything.
       ((symbol-function 'edebug-make-enter-wrapper)
        #'names--edebug-make-enter-wrapper))
    (condition-case er
        (with-temp-buffer
          (pp form 'insert)
          (goto-char (point-min))
          ;; Do the magic!
          (edebug-read-top-level-form))
      (invalid-read-syntax
       (names--warn
        "Couldn't namespace this macro using its (debug ...) declaration: %s"
        form)
       form)
      (error
       (when (equal (car-safe (cdr-safe er))
                    "Lisp nesting exceeds `max-lisp-eval-depth'")
         (names--warn
          "Lisp nesting exceeded `max-lisp-eval-depth' at the following form: %s"
          form))
       form))))

(defvar names--message-backup
  (if (ad-is-advised 'message)
      (ad-get-orig-definition 'message)
    (symbol-function 'message))
  "Where names stores `message's definition while overriding it.")

(defun names--edebug-message (&rest args)
  (if (or (names--keyword :verbose) names--verbose)
      (apply names--message-backup args)
    (when args (apply #'format args))))

(defun names--edebug-make-enter-wrapper (forms)
  (setq edebug-def-name
        (or edebug-def-name
            edebug-old-def-name
            (names--gensym "edebug-anon")))
  (cons 'progn forms))

(defun names--gensym (prefix)
  "Generate a new uninterned symbol.
The name is made by appending a number to PREFIX and preppending \"names\", default \"G\"."
  (let ((num (prog1 names--gensym-counter
               (setq names--gensym-counter
                     (1+ names--gensym-counter)))))
    (make-symbol (format "names-%s%d" (if (stringp prefix) prefix "G") num))))

(defun names--edebug-form (cursor)
  "Parse form given by CURSOR using edebug, and namespace it if necessary."
  (require 'edebug)
  ;; Return the instrumented form for the following form.
  ;; Add the point offsets to the edebug-offset-list for the form.
  (let* ((form (edebug-top-element-required cursor "Expected form"))
         (offset (edebug-top-offset cursor))
         ;; We don't want to convert the entire form that was passed
         ;; to `names--macro-args-using-edebug', since the head of
         ;; that was already converted and it would lead to an
         ;; infinite loop.
         ;; So we check for (equal names--is-inside-macro form)
         ;; Simply incrementing a depth counter didn't work, for a
         ;; reason I can no longer remember.

         ;; We DO want to convert the arguments that edebug identifies
         ;; as forms (level-1). And we do that ourselves, don't pass
         ;; them to edebug.
         (func (if (or (eq names--is-inside-macro t)
                       (equal names--is-inside-macro form))
                   'identity 'names-convert-form))
         (names--is-inside-macro
          (if (eq func 'names-convert-form)
              t names--is-inside-macro)))
    (names--message " [Edebug] Ran into this: %S" form)
    (names--message "          Cursor: %S" cursor)
    (prog1
        (cond
         ((consp form) ;; The first offset for a list form is for the list form itself.
          (if (eq func 'names-convert-form)
              (names-convert-form form)
            (let* ((head (car form))
                   (spec (and (symbolp head) (get-edebug-spec head)))
                   (new-cursor (edebug-new-cursor form offset)))
              ;; Find out if this is a defining form from first symbol.
              ;; An indirect spec would not work here, yet.
              (if (and (consp spec) (eq '&define (car spec)))
                  (edebug-defining-form
                   new-cursor
                   (car offset) ;; before the form
                   (edebug-after-offset cursor)
                   (cons (symbol-name head) (cdr spec)))
                ;; Wrap a regular form.
                (edebug-list-form new-cursor)))))

         ((symbolp form)
          (funcall func form))

         ;; Anything else is self-evaluating.
         (t form))
      (edebug-move-cursor cursor))))

(defun names--maybe-append-group (form)
  "Append (:group `names--package') to FORM.
Only if the :group keyword was passed to `define-namespace' and
if the form doesn't already have a :group."
  (if (or (null names--group-parent) (memq :group form))
      form
    (append form `(:group ',(names--package-name)))))


;;; ---------------------------------------------------------------
;;; Interpreting keywords passed to the main macro.
(defun names--handle-keyword (body)
  "Call the function that handles the keyword at the car of BODY.
Such function must be listed in `names--keyword-list'. If it is
nil, this function just returns.

Regardless of whether a function was called, the keyword is added
to the variable `names--keywords'.

The car of BODY is the keyword itself and the other elements are
the keyword arguments, if any."
  (let ((func (nth 2 (assoc (car body) names--keyword-list))))
    (if (functionp func)
        (apply func (cdr body))
      nil)))


;;; ---------------------------------------------------------------
;;; Interpreting the actual forms found in BODY of the main macro.
;;
;; This is where the heavy work is done.
;;
;; If you'd like to implement support for some special form, simply
;; define a function called `names--convert-FORM-NAME' along the
;; lines of the functions defined below. It will be automatically used
;; whenever that form is found.

;; Defun, defmacro, and defsubst macros are pretty predictable.
(defun names--convert-defmacro (form)
  "Special treatment for `defmacro' FORM."
  (let* ((name (cadr form))
         (spaced-name (names--prepend name))
         decl)
    (add-to-list 'names--macro name)
    (add-to-list 'names--fbound name)
    ;; Set the macros debug spec if possible. It will be relevant on
    ;; the next run.
    (when (setq decl (ignore-errors (cond
                                     ((eq (car-safe (nth 3 form)) 'declare)
                                      (nth 3 form))
                                     ((and (stringp (nth 3 form))
                                           (eq (car-safe (nth 4 form)) 'declare))
                                      (nth 4 form))
                                     (t nil))))
      (setq decl (car (cdr-safe (assoc 'debug (cdr decl)))))
      (when decl (put spaced-name 'edebug-form-spec decl)))
    ;; Then convert the macro as a defalias.
    (cons
     (car form)
     (names--convert-lambda
      (cons spaced-name (cddr form))))))
(defalias 'names--convert-defmacro* 'names--convert-defmacro)

(defun names--convert-defvaralias (form)
  "Special treatment for `defvaralias' FORM."
  (let ((form (cons (car form)
                    (mapcar #'names-convert-form (cdr form))))
        (name))
    (setq name (names--remove-namespace
                (ignore-errors (eval (cadr form)))))
    (when name
      (add-to-list 'names--bound name))
    form))

(defun names--convert-defalias (form)
  "Special treatment for `defalias' FORM."
  (let ((form (cons (car form)
                    (mapcar #'names-convert-form (cdr form))))
        (name))
    (setq name (names--remove-namespace
                (ignore-errors (eval (cadr form)))))
    (when name
      (add-to-list 'names--fbound name))
    form))

(defun names--convert-defvar (form &optional dont-add)
  "Special treatment for `defvar' FORM.
If DONT-ADD is nil, the FORM's `cadr' is added to `names--bound'."
  (let ((name (cadr form)))
    (unless dont-add
      (add-to-list 'names--bound name))
    (append
     (list
      (car form)
      (names--prepend name))
     (mapcar 'names-convert-form (cdr (cdr form))))))

(defalias 'names--convert-defconst 'names--convert-defvar
  "Special treatment for `defconst' FORM.")

(defun names--convert-defcustom (form)
  "Special treatment for `defcustom' FORM."
  (names--maybe-append-group
   (names--convert-defvar form)))

(defun names--convert-custom-declare-variable (form)
  "Special treatment for `custom-declare-variable' FORM."
  (let ((name (eval (cadr form))) ;;ignore-errors
        (val (car (cddr form))))
    (add-to-list 'names--bound name)
    (append
     (list
      (car form)
      (list 'quote (names--prepend name)) ;cadr
      ;; The DEFAULT argument is explicitly evaluated by
      ;; `custom-declare-variable', so it should be safe to namespace
      ;; even when quoted. Plus, we need to do this because
      ;; defcustom quotes this part.
      (if (names--quote-p (car-safe val))
          (list (car val) (names-convert-form (cadr val)))
        (names-convert-form val))
      (names-convert-form        (car (cdr (cdr (cdr form))))))
     (mapcar 'names-convert-form (cdr (cdr (cdr (cdr form))))))))

(defun names--convert-defface (form)
  "Special treatment for `defface' FORM.
Identical to defvar, just doesn't add the symbol to the boundp
list. And maybe use a :group."
  (names--maybe-append-group
   (names--convert-defvar form :dont-add)))

(defun names--convert-define-derived-mode (form)
  "Special treatment for `define-derived-mode' FORM."
  (let ((name (cadr form)))
    (add-to-list 'names--fbound name)
    (add-to-list 'names--bound name)
    (add-to-list 'names--bound
                 (intern (format "%s-map" name)))
    (add-to-list 'names--bound
                 (intern (format "%s-hook" name)))
    (append
     (names--maybe-append-group
      ;; And here we namespace it.
      (list
       (car form)
       (names--prepend name)
       (nth 2 form)
       (names-convert-form (nth 3 form))
       (names-convert-form (nth 4 form))))
     (mapcar #'names-convert-form (cddr (cl-cdddr form))))))

(defun names--convert-define-minor-mode (form)
  "Special treatment for `define-minor-mode' FORM."
  (let ((name (cadr form))
        (keymap (nth 5 form)))
    ;; Register the mode name
    (add-to-list 'names--fbound name)
    (add-to-list 'names--bound name)
    (add-to-list 'names--bound (intern (format "%s-hook" name)))
    ;; Register the keymap
    (if (or (null keymap) (null (symbolp keymap)))
        (add-to-list 'names--bound (intern (format "%s-map" name)))
      (when (setq keymap (names--remove-namespace keymap))
        (add-to-list 'names--bound keymap)))
    (append
     (names--maybe-append-group
      ;; And here we namespace it.
      (list
       (car form)
       (names--prepend name)
       (nth 2 form)
       (names-convert-form (nth 3 form))
       (names-convert-form (nth 4 form))
       (names-convert-form (nth 5 form))
       (names-convert-form (nth 6 form))))
     (mapcar #'names-convert-form (cddr form)))))

(defun names--convert-define-globalized-minor-mode (form)
  "Special treatment for `define-globalized-minor-mode' FORM.
The NAME of the global mode will NOT be namespaced, despite being
a definition. It is kept verbatim.
This is because people tend to name their global modes as
`global-foo-mode', and namespacing would make this impossible.

The MODE and TURN-ON arguments are converted as function names.
Everything else is converted as regular forms (which usually
means no conversion will happen since it's usually keywords and
quoted symbols)."
  (let ((name (names--remove-namespace (cadr form)))
        (copy (cl-copy-list form)))
    ;; Register the mode name
    (when name
      (add-to-list 'names--fbound name)
      (add-to-list 'names--bound name)
      (add-to-list 'names--bound (intern (format "%s-hook" name))))
    (names--maybe-append-group
     ;; And here we namespace it.
     (append
      (list
       (pop copy)
       (pop copy)
       (names--handle-symbol-as-function (pop copy))
       (names--handle-symbol-as-function (pop copy)))
      (mapcar #'names-convert-form copy)))))
(defalias 'names--convert-define-global-minor-mode
  #'names--convert-define-globalized-minor-mode)
(defalias 'names--convert-easy-mmode-define-global-mode
  #'names--convert-define-globalized-minor-mode)

(defun names--convert-quote (form)
  "Special treatment for `quote' FORM.
When FORM is (quote argument), argument too arbitrary to be
logically namespaced and is never parsed for namespacing
 (but see :assume-var-quote in `names--keyword-list').

When FORM is (function form), a symbol is namespaced as a
function name, a list is namespaced as a lambda form."
  (let ((kadr (cadr form))
        (this-name (car form)))
    (if (and (eq this-name 'function)
             (listp kadr))
        (list this-name (names-convert-form kadr))
      (if (symbolp kadr)
          (cond
           ;; A symbol inside a function quote should be a function,
           ;; unless the user disabled that.
           ((and (eq this-name 'function)
                 (null (names--keyword :dont-assume-function-quote)))
            (list 'function
                  (names--handle-symbol-as-function kadr)))

           ;; A symbol inside a regular quote should be a function, if
           ;; the user asked for that.
           ((and (eq this-name 'quote)
                 (names--keyword :assume-var-quote))
            (list 'quote
                  (or (names--remove-protection kadr)
                      (if (names--boundp kadr)
                          (names--prepend kadr)
                        kadr))))

           (t form))
        form))))

(defun names--handle-symbol-as-function (s)
  "Namespace symbol S as a function name."
  (or (names--remove-protection s)
      (if (names--fboundp s) (names--prepend s) s)))

(defalias 'names--convert-function 'names--convert-quote)

(defun names--convert-macro (form)
  "Special treatment for `macro' form.
Return (macro . (names-convert-form (cdr FORM)))."
  (cons 'macro (names-convert-form (cdr form))))

(defun names--convert-lambda (form)
  "Special treatment for `lambda' FORM."
  (let ((names--local-vars
         (append (names--vars-from-arglist (cadr form))
                 names--local-vars))
        (forms (cdr (cdr form))))
    (append
     (list (car form)
           (cadr form))
     (when (stringp (car forms))
       (prog1
           (list (car forms))
         (setq forms (cdr forms))))
     (when (eq 'interactive (car-safe (car forms)))
       (prog1
           (list (list (car (car forms))
                       (names-convert-form (cadr (car forms)))))
         (setq forms (cdr forms))))
     (progn
       ;; (message "%S" forms)
       (mapcar 'names-convert-form forms)))))

(defun names--convert-clojure (form)
  "Special treatment for `clojure' FORM."
  (names--warn "Found a `closure'! You should use `lambda's instead")
  (let ((names--local-vars
         (append (names--vars-from-arglist (cadr form))
                 names--local-vars)))
    (cons
     (car form)
     (names--convert-lambda (cdr form)))))

(defun names--vars-from-arglist (args)
  "Get a list of local variables from a generalized arglist ARGS."
  (remove
   nil
   (mapcar
    (lambda (x)
      (let ((symb (or (cdr-safe (car-safe x)) (car-safe x) x)))
        (when (and (symbolp symb)
                   (null (string-match "^&" (symbol-name symb)))
                   (null (eq symb t)))
          symb)))
    args)))

(defun names--convert-defun (form)
  "Special treatment for `defun' FORM."
  (let* ((name (cadr form)))
    (add-to-list 'names--fbound name)
    (cons (car form)
          (names--convert-lambda
           (cons (names--prepend name) (cddr form))))))
(defalias 'names--convert-defun* 'names--convert-defun)
(defalias 'names--convert-defsubst 'names--convert-defun)
(defalias 'names--convert-defsubst* 'names--convert-defun)

(defun names--let-var-convert-then-add (sym add)
  "Try to convert SYM unless :no-let-vars is in use.
If ADD is non-nil, add resulting symbol to `names--local-vars'."
  (let ((name (if (null (names--keyword :no-let-vars))
                  (names-convert-form sym)
                sym)))
    (when add (add-to-list 'names--local-vars name))
    name))

(defun names--convert-let (form &optional star)
  "Special treatment for `let' FORM.
If STAR is non-nil, parse as a `let*'."
  (let* ((names--local-vars names--local-vars)
         (vars
          (mapcar
           (lambda (x)
             (if (car-safe x)
                 (list (names--let-var-convert-then-add (car x) star)
                       (names-convert-form (cadr x)))
               (names--let-var-convert-then-add x star)))
           (cadr form))))
    ;; Each var defined in a regular `let' only becomes protected after
    ;; all others have been defined.
    (unless star
      (setq names--local-vars
            (append
             (mapcar (lambda (x) (or (car-safe x) x)) vars)
             names--local-vars)))
    (append
     (list (car form) vars)
     (mapcar 'names-convert-form (cddr form)))))

(defun names--convert-let* (form)
  "Special treatment for `let' FORM."
  (names--convert-let form t))

(defun names--convert-cond (form)
  "Special treatment for `cond' FORM."
  (cons
   (car form)
   (mapcar
    (lambda (x) (mapcar #'names-convert-form x))
    (cdr form))))

(defun names--convert-condition-case (form)
  "Special treatment for `condition-case' FORM."
  (append
   (list
    (car form)
    (cadr form)
    (names-convert-form (cadr (cdr form))))
   (mapcar
    (lambda (x)
      (cons (car x)
            (mapcar 'names-convert-form (cdr x))))
    (cddr (cdr form)))))

(provide 'names)
;;; names.el ends here
