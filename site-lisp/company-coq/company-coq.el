;;; company-coq.el --- A collection of extensions for Proof General's Coq mode -*- lexical-binding: t -*-

;; Copyright (C) 2015, 2016, 2017  Clément Pit-Claudel
;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; URL: https://github.com/cpitclaudel/company-coq
;; Keywords: convenience, languages
;; Package-Requires: ((cl-lib "0.5") (dash "2.12.1") (yasnippet "0.11.0") (company "0.8.12") (company-math "1.1"))
;; Version: 1.0

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
;; This package includes a collection of company-mode backends for
;; Proof-General's Coq mode, and many useful extensions to Proof-General.
;;
;; See https://github.com/cpitclaudel/company-coq/ for a detailed description,
;; including screenshots and documentation.  After installing, you may want to
;; use M-x company-coq-tutorial to open the tutorial.

;;; History:
;;
;; 2016-02-28 — Show input hints for Unicode and prettified symbols
;; 2016-02-28 — Prettify symbols in notation strings and code blocks
;; 2016-02-07 — Support for changing [Require]s to use fully qualified names
;; 2016-02-02 — Preserve names by inserting intros when extracting a lemma
;; 2016-01-31 — Fall back to regular autocompletion in comments (except in code blocks)
;; 2016-01-26 — Detect and display subscripts: a1 → a₁ and a__n → aₙ
;; 2016-01-20 — First stable release (~600 commits)
;; 2015-02-15 — First commit

;;; Code:
;;
;; Technical notes
;; ===============
;;
;; Sending  commands to  the prover  when it's  already busy  breaks everything.
;; 'proof-shell-handle-delayed-output-hook is  a good  place to  reload symbols,
;; except when an error occurs (in that case the hook runs before all output has
;; been processed.
;;
;; This problem is solved by refusing  to communicate with the prover, unless it
;; is reported as available. When it isn't, the interaction is either abandonned
;; (that's what happens  with documentation, and with completion  if the symbols
;; aren't available yet)) or delayed using  an idle timer (reload; in fact, this
;; one is always wrapped in an idle  timer). To prevent loops due to idle timers
;; firing in succession, reloads are only attempted once.
;;
;; The current implementation uses two hooks:
;;  * 'proof-shell-insert-hook
;;      In this one we check the input to see if it might introduce new symbols
;;      (e.g. [Require …])
;;  * 'proof-shell-handle-delayed-output-hook
;;      In this one we parse the output to see if it suggests that new symbols
;;      have been introduced (e.g. [… defined])
;;
;; Since these  two hooks are  called into even for  commands issued by  our own
;; code, we only execute their body if  we are not currently already waiting for
;; an answer from the prover (company-coq-talking-to-prover).

(require 'cl-lib)       ;; Compatibility
(require 'company)      ;; Autocompletion
(require 'company-math) ;; Math symbols
(require 'dash)         ;; -when-let, -if-let, -zip, -keep, etc.
(require 'diff-mode)    ;; Browsing through large error messages
(require 'outline)      ;; Outlines
(require 'hideshow)     ;; Code folding
(require 'paren)        ;; Find matching block start
(require 'shr)          ;; HTML rendering
(require 'smie)         ;; Move around the source code
(require 'yasnippet)    ;; Templates
(require 'pulse)        ;; Pulsing after jumping to definitions
(require 'button)       ;; Links in goals and error messages
(require 'menu-bar)     ;; `popup-menu'
(unless (require 'alert nil t) ;; Notifications
  (require 'notifications nil t))

(require 'company-coq-abbrev) ;; Tactics from the manual
(require 'company-coq-tg)     ;; Parsing code for tactic notations
(require 'company-coq-utils)  ;; Various utils

;;; Shims for old emacsen

(defvar company-coq-seconds-to-string
  (list (list 1 "ms" 0.001)
        (list 100 "s" 1)
        (list (* 60 100) "m" 60.0)
        (list (* 3600 30) "h" 3600.0)
        (list (* 3600 24 400) "d" (* 3600.0 24.0))
        (list nil "y" (* 365.25 24 3600)))
  "Formatting used by the function `company-coq-seconds-to-string'.")

(defun company-coq-seconds-to-string (delay)
  "Convert the time interval DELAY in seconds to a short string."
  (cond ((> 0 delay) (concat "-" (company-coq-seconds-to-string (- delay))))
        ((= 0 delay) "0s")
        (t (let ((sts company-coq-seconds-to-string) here)
             (while (and (car (setq here (pop sts)))
                         (<= (car here) delay)))
             (concat (format "%.2f" (/ delay (car (cddr here)))) (cadr here))))))

(eval-and-compile
  ;; Silence the byte-compiler in Emacs < 24.4
  (defvar shr-width)
  (defvar shr-internal-width)
  (defvar shr-target-id)
  (defvar shr-external-rendering-functions))

;; Shims for PG

(eval-and-compile
  (defvar company-coq--check-forward-declarations nil
    "Whether incorrect `company-coq--forward-declare' forms should throw errors.
This is useful for debugging, mostly.")

  (defun company-coq-forward-declare-var--verify (var value)
    "Check that the forward declaration of SYMBOL with VALUE is legitimate."
    (when company-coq--check-forward-declarations
      (unless (or (boundp var) value)
        (warn "Variable %S isn't declared" var))
      (when (and (boundp var) value (not (equal (symbol-value var) value)))
        (warn "Variable %S is declared to %S, but fallback is set to %S" var (symbol-value var) value))))

  (defmacro company-coq-forward-declare-var (var &optional value)
    "Forward-declare VAR.
If `company-coq--check-forward-declarations', check that the declaration is valid.
If VALUE is non-nil, assign it to the variable."
    (declare (indent defun))
    `(progn
       (company-coq-forward-declare-var--verify ',var ,value)
       (if ,value
           (defvar ,var ,value)
         (defvar ,var))))

  (defun company-coq-forward-declare-fun--verify (fun)
    "Check that the forward declaration of FUN is legitimate."
    (when (and company-coq--check-forward-declarations (not (fboundp fun)))
      (warn "Function %S isn't declared" fun)))

  (defmacro company-coq-forward-declare-fun (fun &rest args)
    "Forward-declare FUN with ARGS.
If `company-coq--check-forward-declarations' is set, do not
forward-declare; instead, check that the declaration is valid."
    (declare (indent defun))
    `(progn
       (company-coq-forward-declare-fun--verify ',fun)
       (declare-function ,fun ,@args)))

  (company-coq-forward-declare-var proof-goals-buffer)
  (company-coq-forward-declare-var proof-script-buffer)
  (company-coq-forward-declare-var proof-response-buffer)
  (company-coq-forward-declare-var proof-action-list)
  (company-coq-forward-declare-var proof-script-fly-past-comments)
  (company-coq-forward-declare-var proof-shell-proof-completed)
  (company-coq-forward-declare-var proof-shell-last-output)
  (company-coq-forward-declare-var proof-shell-last-output-kind)
  (company-coq-forward-declare-var proof-shell-last-goals-output)
  (company-coq-forward-declare-var proof-shell-last-response-output)
  (company-coq-forward-declare-var proof-shell-delayed-output-flags)
  (company-coq-forward-declare-var proof-shell-eager-annotation-start)
  (company-coq-forward-declare-var proof-shell-eager-annotation-end)
  (company-coq-forward-declare-var pg-span-context-menu-keymap)
  (company-coq-forward-declare-var coq-reserved)
  (company-coq-forward-declare-var coq-user-cheat-tactics-db)
  (company-coq-forward-declare-var coq-user-commands-db)
  (company-coq-forward-declare-var coq-user-reserved-db)
  (company-coq-forward-declare-var coq-user-solve-tactics-db)
  (company-coq-forward-declare-var coq-user-tacticals-db)
  (company-coq-forward-declare-var coq-user-tactics-db)
  (company-coq-forward-declare-fun proof-shell-invisible-command "ext:proof-shell.el" cmd)
  (company-coq-forward-declare-fun proof-shell-available-p "ext:proof-shell.el")
  (company-coq-forward-declare-fun proof-shell-live-buffer "ext:proof-shell.el")
  (company-coq-forward-declare-fun proof-shell-ready-prover "ext:proof-shell.el")
  (company-coq-forward-declare-fun proof-unprocessed-begin "ext:proof-script.el")
  (company-coq-forward-declare-fun proof-electric-terminator "ext:pg-user.el")
  (company-coq-forward-declare-fun proof-goto-point "ext:pg-user.el")
  (company-coq-forward-declare-fun proof-electric-terminator "ext:pg-user.el")
  (company-coq-forward-declare-fun coq-mode "ext:coq.el")
  (company-coq-forward-declare-fun coq-response-mode "ext:coq.el")
  (company-coq-forward-declare-fun coq-insert-match "ext:coq.el")
  (company-coq-forward-declare-fun coq-last-prompt-info-safe "ext:coq.el")
  (company-coq-forward-declare-fun coq-find-comment-start "ext:coq.el")
  (company-coq-forward-declare-fun coq-find-comment-end "ext:coq.el")
  (company-coq-forward-declare-fun coq-looking-at-comment "ext:coq-indent.el" cmd))

(defun company-coq--get-comment-region ()
  "Local copy of `coq-get-comment-region'.
It isn't available in old versions of PG."
  (save-excursion
    (cons (save-excursion (coq-find-comment-start))
          (save-excursion (coq-find-comment-end)))))

;; This doesn't run at compile time
(unless (require 'proof-site nil t)
  ;; No others `require's at this point: we don't want to start PG's machinery
  ;; just because a user `require'd company-coq.
  (error "Company-Coq: Unable to load proof-site.  Is Proof General installed properly?"))

(defgroup company-coq nil
  "Extensions for Proof General's Coq mode."
  :prefix "company-coq-"
  :group 'company)

(defgroup company-coq-obsolete nil
  "Company-Coq obsolete settings."
  :prefix "company-coq-"
  :group 'company-coq)

(defgroup company-coq-faces nil
  "Company-Coq faces."
  :prefix "company-coq-"
  :group 'company-coq)

(eval-and-compile
  (defvar company-coq-debug nil
    "Debug mode for company-coq."))

(defcustom company-coq-custom-snippets '("Section ${1:SectionName}.\n$0\nEnd $1."
                              "Module ${1:ModuleName}.\n$0\nEnd $1."
                              "Module Type ${1:ModuleTypeName}.\n$0\nEnd $1."
                              "match ${ident} with\n$0\nend"
                              "lazymatch ${ident} with\n$0\nend"
                              "multimatch ${ident} with\n$0\nend"
                              "match constr:($1) with\n$0\nend"
                              "lazymatch constr:($1) with\n$0\nend"
                              "match goal with\n$0\nend"
                              "lazymatch goal with\n$0\nend")
  "Custom snippets.
Feel free to share your snippets on company-coq's GitHub!"
  :group 'company-coq
  :type '(repeat string))

(defcustom company-coq-dynamic-autocompletion nil
  "Get suggestions by querying coq about defined identifiers.

This is an experimental feature.  It requires Coq 8.5 beta 3 or a
patched version of Coq 8.4 to work properly."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-dynamic-autocompletion 'company-coq-live-on-the-edge "company-coq 1.0")

(defconst company-coq--capability-detection-cmd "Test Search Output Name Only"
  "Command used to test for dynamic completion capabilities.
Two patches are required for proper completion of theorems:
=Redirect=ion to a file, and =Search Output Name Only=.  For
tactics, and extra patch is required.")

(defvar company-coq--coqtop-patched-result 'unknown
  "Whether coqtop supports advanced completion features.
One of 'unknown, 'yes, 'no.")

(defcustom company-coq-autocomplete-context t
  "Autocomplete hypotheses by parsing the latest Goals output.
This is an experimental feature."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-autocomplete-context 'company-coq-disabled-features "company-coq 1.0")

(defcustom company-coq-autocomplete-modules t
  "Autocomplete module names from Coq's load path."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-autocomplete-modules 'company-coq-disabled-features "company-coq 1.0")

(defcustom company-coq-autocomplete-block-end t
  "Autocomplete the name of the last opened block."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-autocomplete-block-end 'company-coq-disabled-features "company-coq 1.0")

(defcustom company-coq-autocomplete-search-results t
  "Autocomplete symbol names pulled from the results of the last search."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-autocomplete-search-results 'company-coq-disabled-features "company-coq 1.0")

(defcustom company-coq-autocomplete-symbols t
  "Autocomplete symbols by searching in the buffer for lemmas and theorems.
If the dynamic completion feature is on, query the proof
assistant in addition to searching."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-autocomplete-symbols 'company-coq-disabled-features "company-coq 1.0")

(defcustom company-coq-prettify-symbols t
  "Transparently replace keywords by the corresponding symbols.
The contents of the buffer are not changed."
  :group 'company-coq-obsolete
  :type 'boolean)
(make-obsolete-variable 'company-coq-prettify-symbols 'company-coq-disabled-features "company-coq 1.0")

(defcustom company-coq-snippet-default-hole-contents "_"
  "String to use to indicate holes in inserted snippets."
  :group 'company-coq
  :type '(string))

(defvar company-coq-enabled-backends nil
  "List of currently enabled company-coq completion backends.
Do not enable or disable backends by editing this list; instead,
customize `company-coq-disabled-features'.")

(defvar company-coq-excluded-pg-patterns '("without loss" "Fixpoint")
  "List of patterns that are not imported from Proof General's list.")

(defcustom company-coq-sorted-backends '(company-coq-reserved-keywords-backend
                              company-coq-block-end-backend
                              company-coq-user-snippets-backend
                              company-coq-modules-backend
                              company-coq-context-backend
                              company-coq-refman-ltac-abbrevs-backend
                              company-coq-refman-tactic-abbrevs-backend
                              company-coq-refman-vernac-abbrevs-backend
                              company-coq-refman-scope-abbrevs-backend
                              company-coq-pg-backend
                              company-coq-local-definitions-backend
                              company-coq-search-results-backend
                              company-coq-dynamic-tactics-backend
                              company-coq-dynamic-symbols-backend)
  "All completion backends, ordered by display priority.
Do not remove entries from this list (but feel free to reorder
them).  To disable backends, customize `company-coq-disabled-features'."
  :group 'company-coq
  :type '(repeat function))

(defvar company-coq-talking-to-prover nil
  "Indicates whether a interaction has been initiated with the prover, to disable the input and output hooks.")

(defvar company-coq-symbols-reload-needed t
  "Indicates whether the dynamic list of symbols is outdated.
This variable is set from places where immediate reloading is
impossible, for example in `proof-shell-insert-hook'")

(defvar company-coq-tactics-reload-needed t
  "Indicates whether the dynamic list of tactics is outdated.
This variable is set from places where immediate reloading is
impossible, for example in `proof-shell-insert-hook'")

(defvar company-coq-modules-reload-needed t
  "Indicates whether the dynamic list of modules is outdated.
This variable is set from places where immediate reloading is
impossible, for example in `proof-shell-insert-hook'")

(defvar company-coq-dynamic-symbols nil
  "Keeps track of defined symbols.")

(defvar company-coq-dynamic-tactics nil
  "Keeps track of defined tactics.")

(defvar company-coq-path-specs-cache nil
  "Cache tracking paths specs in Coq's load path.")

(defvar company-coq-last-search-results nil
  "Cache tracking symbols mentionned in search results.")

(defvar company-coq-last-search-scan-size nil
  "If the response buffer has this size, search results are deemed up to date.")

(defvar company-coq-definition-overlay nil
  "Overlay used to show inline definitions.")

(defconst company-coq-id-regexp "\\(?:[a-zA-Zα-ωΑ-Ω0-9_][a-zA-Zα-ωΑ-Ω0-9_']*\\)")
(defconst company-coq-prefix-regexp "\\(?:[a-zA-Zα-ωΑ-Ω0-9_][a-zA-Zα-ωΑ-Ω0-9_.']*!?\\)?") ;; '!' included for [intros!] etc.
(defconst company-coq-symbol-regexp "\\(?:[_a-zA-Zα-ωΑ-Ω]\\(?:[a-zA-Zα-ωΑ-Ω0-9_.']*[a-zA-Zα-ωΑ-Ω0-9_']\\)?\\)")
(defconst company-coq-symbol-regexp-no-dots "\\(?:_*[a-zA-Zα-ωΑ-Ω]\\(?:[a-zA-Zα-ωΑ-Ω0-9_']*[a-zA-Zα-ωΑ-Ω0-9_']\\)?\\)")
(defconst company-coq-symbol-regexp-no-dots-no-numbers "\\(?:_*[a-zA-Zα-ωΑ-Ω]\\(?:[a-zA-Zα-ωΑ-Ω0-9_']*[a-zA-Zα-ωΑ-Ω']\\)?\\)")
(defconst company-coq-module-chunk-regexp "\\(?:[A-Z][a-zA-Zα-ωΑ-Ω0-9_]*\\)")
(defconst company-coq-module-name-regexp (concat company-coq-module-chunk-regexp "\\(?:\\." company-coq-module-chunk-regexp "\\)*"))

(defconst company-coq-all-symbols-slow-regexp (concat "^\\(" company-coq-symbol-regexp "\\):")
  "Regexp matching symbol names in search results.")

(defconst company-coq--subgoal-header-regexp
  "\\(?:^\\(subgoal .* is:\\|  ============================\\)$\\)"
  "Regexp indicating the beginning of a subgoal.")

;; More powerful, but more tricky to match against:
;; "\\(?:^  \\|[^[:space:]]   +\\)\\(\\(?:[^:=, \t\r\n]\\|, \\)+\\) \\(:=?\\) "
(defconst company-coq--hypothesis-header-regexp
  "^  \\(\\(?:[^:=, \t\r\n]\\|, \\)+\\) \\(:=?\\) "
  "Regexp indicating the beginning of a hypothesis.")

(defconst company-coq--hypotheses-block-opener "\n\\s-*\n"
  "Regexp matching the beginning of hypotheses.")

(defconst company-coq--hypotheses-block-closer company-coq--subgoal-header-regexp
  "Regexp matching the end of hypotheses.")

(defconst company-coq-path-regexp  (concat "\\`\\(\\S-*\\) +\\(\\S-*\\)\\'"))

(defun company-coq-make-headers-regexp (headers &optional body)
  "Construct a regexp from HEADERS and BODY.
The result matches any symbol in HEADERS, followed by BODY."
  (concat "^[[:blank:]]*\\_<\\(" (regexp-opt headers) "\\)\\_>"
          (when body (concat "\\s-*\\(" body "\\)"))))

(defconst company-coq-definitions-kwds `("Class" "CoFixpoint" "CoInductive" "Coercion" "Corollary"
                              "Declare Module" "Definition" "Example" "Fact" "Fixpoint"
                              "Function" "Functional Scheme" "Global Instance" "Inductive"
                              "Instance" "Lemma" "Let" "Ltac" "Program" "Program Definition"
                              "Program Instance" "Program Fixpoint" "Record" "Scheme" "Theorem"
                              "Variant" "with")
  "Keywords that introduce a definition.")

(defconst company-coq-definitions-regexp (company-coq-make-headers-regexp company-coq-definitions-kwds
                                                    company-coq-id-regexp)
  "Regexp used to locate symbol definitions in the current buffer.")

(defconst company-coq-block-end-regexp (company-coq-make-headers-regexp '("End") company-coq-id-regexp)
  "Regexp used to find section endings.")

(defcustom company-coq-search-blacklist '("Raw" "Proofs") ;; "_refl" "_sym" "_trans" "_ind" "_rec" "_rect"
  "List of strings to add to Coq's search blacklist when loading completion candidates."
  :group 'company-coq
  :type '(repeat string))

(defconst company-coq-search-blacklist-str (mapconcat (lambda (str) (concat "\"" str "\""))
                                           company-coq-search-blacklist " "))

(defconst company-coq-search-blacklist-add-cmd (concat "Add Search Blacklist "
                                            company-coq-search-blacklist-str))

(defconst company-coq-search-blacklist-rem-cmd (concat "Remove Search Blacklist "
                                            company-coq-search-blacklist-str))

(defconst company-coq-all-symbols-prelude (cons company-coq-search-blacklist-add-cmd
                                     '("Set Search Output Name Only"))
  "Commands to run before asking the prover for symbols.")

(defconst company-coq-redirection-template "Redirect \"%s\" %s")

(defconst company-coq-all-symbols-cmd "SearchPattern _"
  "Command used to list all symbols.")

(defconst company-coq-all-ltacs-cmd "Print Ltac Signatures"
  "Command used to list all tactics.")

(defconst company-coq-all-notations-cmd "Print Grammar tactic"
  "Command used to list all tactic notations.")

(defvar company-coq-extra-symbols-cmd nil
  "Command used to list extra symbols ([SearchPattern _] doesn't search inside modules in 8.4).")

(defconst company-coq-all-symbols-coda (cons company-coq-search-blacklist-rem-cmd
                                  '("Unset Search Output Name Only"))
  "Command to run after asking the prover for symbols.")

(defconst company-coq-doc-cmd "About %s"
  "Command used to retrieve the documentation of a symbol.")

(defconst company-coq-def-cmd "Print %s"
  "Command used to retrieve the definition of a symbol.")

(defconst company-coq-type-cmd "Check %s"
  "Command used to retrieve the type of a symbol.")

(defconst company-coq-tactic-def-cmd "Print Ltac %s"
  "Command used to retrieve the documentation of a tactic.")

(defconst company-coq-symbols-meta-cmd "Check @%s."
  "Command used to retrieve a short description of a symbol.")

(defconst company-coq-modules-cmd "Print LoadPath."
  "Command used to retrieve module path specs (for module name completion).")

(defconst company-coq-locate-lib-cmd "Locate Library %s."
  "Command used to retrieve the qualified name of a library (to locate the corresponding source file).")

(defconst company-coq-locate-lib-output-format (replace-regexp-in-string
                                     " " "[[:space:]]+"
                                     (concat "\\`\\(" company-coq-module-name-regexp "\\)"
                                             " \\(?:has been loaded from\\|is bound to\\) file "
                                             "\\([^[:space:]]+\\)\\(\\.[^[:space:].]+\\)"))
  "Regexp matching the output of `company-coq-locate-lib-cmd'.")

(defconst company-coq-compiled-regexp "\\.vi?o\\'"
  "Regexp matching the extension of compiled Coq files.")

(defconst company-coq-end-of-def-regexp "\\(is\\|are\\) \\(recursively \\)?\\(defined\\|assumed\\|declared\\)"
  "Regexp used to detect signs that new symbols have been defined.")

(defconst company-coq-error-regexps `("^Error:"
                           "^Syntax error:"
                           "^No object of basename"
                           "^Toplevel input, characters"
                           "^No Ltac definition is referred to by"
                           "^Unable to locate library"
                           "^The command has indeed failed with message:"
                           " not a defined object.")
  "Regexps used to detect invalid output.")

(defconst company-coq-error-regexp (concat "\\(" (mapconcat #'identity company-coq-error-regexps "\\|") "\\)")
  "Regexp used to detect invalid output.")

(defconst company-coq-import-regexp (regexp-opt '("Require" "Import" "Export"))
  "Regexp used to detect signs that an import will be processed.")

(defconst company-coq-tac-notation-regexp (regexp-opt '("Tactic Notation"))
  "Regexp used to detect signs that a tactic notation will be defined.")

(defconst company-coq-load-regexp "\\(LoadPath\\)"
  "Regexp used to detect signs that new paths will be added to the load path.")

(defconst company-coq-doc-tagline "Documentation for symbol %s"
  "Format string for the header of the documentation buffer.")

(defconst company-coq-doc-def-sep "\n---\n\n"
  "Separation line between sections of the doc buffer.")

(defconst company-coq-dabbrev-to-yas-regexp "#\\|@{\\([^}]+\\)}"
  "Regexp matching holes in abbrevs.")

(defconst company-coq-yasnippet-choice-regexp "${\\([a-z]+\\( | [a-z]+\\)+\\)}"
  "Regexp matching alternatives in abbrevs.")

(defconst company-coq-section-kwds '("Chapter" "Module" "Module Type" "Section")
  "Keywords opening a new section.")

(defconst company-coq-named-outline-kwds `("Equations" "Remark"
                                "Add" ;; Add (Parametric)? Morphism
                                ,@company-coq-section-kwds ,@company-coq-definitions-kwds)
  "Headers used in outline mode and in `company-coq-occur'.")

(defconst company-coq-anonymous-outline-kwds
  '("Goal" "Notation" "Tactic Notation" "Hint" "Hint Constructors" "Hint Cut"
    "Hint Extern" "Hint Local" "Hint Rewrite" "Hint Unfold" "Hint Immediate"
    "Hint Resolve")
  "Extra headers to show in outline mode and in `company-coq-occur'.")

(defconst company-coq-section-regexp (company-coq-make-headers-regexp company-coq-section-kwds
                                                company-coq-id-regexp)
  "Regexp matching section openings.")

;; NOTE: Would be nice to fold [Require Import]s together instead of hiding them entirely
(defconst company-coq-outline-regexp-base
  (concat "\\(?:" (company-coq-make-headers-regexp company-coq-named-outline-kwds company-coq-id-regexp) "\\)" "\\|"
          "\\(?:" (company-coq-make-headers-regexp company-coq-anonymous-outline-kwds nil) "\\)")
  "Regexp matching terms to show in outline mode and in `company-coq-occur'.")

(defconst company-coq-outline-regexp
  ;; Include preceeding blank space, if any.
  (concat "\\(?:" "\n?" company-coq-outline-regexp-base "\\)"))

(defun company-coq-outline-level ()
  "Determine the current outline level (always 0)."
  0)

(defconst company-coq-outline-heading-end-regexp "\\.[ \t\n]"
  "Regexp used to locate the end of a heading.")

(defcustom company-coq-prettify-symbols-alist '(;; Disabled
                                     ;; ("*" . ?×)  ; Inconsistent (‘intros H *’, rewrite in *, etc.)
                                     ;; ("~" . ?¬)  ; Too invasive
                                     ;; ("+-" . ?±) ; Too uncommon
                                     ;; ("++" . ?⧺) ; Not present in TeX fonts
                                     ;; ("nat" . ?𝓝) ("Prop" . ?𝓟) ; Rather uncommon
                                     ;; ("N" . ?ℕ) ("Z" . ?ℤ) ("Q" . ?ℚ) ; Too invasive

                                     ;; Core Coq symbols
                                     ("|-" . ?⊢) ("||" . ?‖) ("/\\" . ?∧) ("\\/" . ?∨)
                                     ("->" . ?→) ("<-" . ?←) ("<->" . ?↔) ("=>" . ?⇒)
                                     ("<=" . ?≤) (">=" . ?≥) ("<>" . ?≠)
                                     ("True" . ?⊤) ("False" . ?⊥)
                                     ("fun" . ?λ) ("forall" . ?∀) ("exists" . ?∃)
                                     ("nat" . ?ℕ) ("Prop" . ?ℙ) ("Real" . ?ℝ) ("bool" . ?𝔹)

                                     ;; Extra symbols
                                     (">->" . ?↣)
                                     ("-->" . ?⟶) ("<--" . ?⟵) ("<-->" . ?⟷)
                                     ("==>" . ?⟹) ("<==" . ?⟸) ("~~>" . ?⟿) ("<~~" . ?⬳))
  "An alist of symbols to prettify.
Assigned to `prettify-symbols-alist' in Emacs >= 24.4."
  :group 'company-coq
  :type 'alist)

(defcustom company-coq-local-symbols nil
  "An alist of file-specific symbols to prettify.
Combined with `company-coq-prettify-symbols-alist' when loading
the file.  Most useful as a file-local variable."
  :group 'company-coq
  :type 'alist
  :safe 'listp)

(defcustom company-coq-dir-local-symbols nil
  "An alist of directory-specific symbols to prettify.
Combined with `company-coq-prettify-symbols-alist' when loading
the file.  Most useful as a dir-local variable."
  :group 'company-coq
  :type 'alist
  :safe 'listp)

(defcustom company-coq-completion-predicate #'company-coq-in-code-p
  "Function called before offering company-coq completions, or nil.
If nil, offer company-coq candidates everywhere.  If set to
`company-coq-not-in-comment-p', offer completions in source code,
but never in comments.  If set to `company-coq-in-code-p', offer
completion in source code, in code blocks in comments […], but
not in comment text.  This function should not change the point."
  :group 'company-coq
  :type '(choice (const :tag "Complete in code and code comments" company-coq-in-code-p)
                 (const :tag "Complete only in code" company-coq-not-in-comment-p)
                 (const :tag "Offer completions everywhere" nil)))

(defun company-coq-not-in-comment-p ()
  "Return nil if point is inside a comment.
Useful as a value for `company-coq-completion-predicate'"
  (not (coq-looking-at-comment)))

(defconst company-coq--notations-header
  (regexp-opt '("Infix" "Notation" "Tactic Notation" "Reserved Notation") 'symbols)
  "Regexp for keywords introducing notations.")

(defun company-coq--in-notation-string-1 (pp)
  "Use PP to check if point in in a “Notation” string.
That is, return non-nil in any string between “^Tactic? Notation”
and “:=”.  PP should be the result of calling `syntax-ppss' on
point."
  (and (nth 3 pp) ;; In a string
       (save-excursion
         (save-match-data
           (let ((bol (point-at-bol)))
             (and (not (re-search-backward "[^\"]:=" bol t))
                  (progn (goto-char bol)
                         (looking-at company-coq--notations-header))))))))

(defun company-coq--in-escaped-code-block-p (comment-beg)
  "Check if point is in a code block.
Point is assumed to be in a comment starting at COMMENT-BEG."
  (save-excursion
    (skip-chars-backward "^[]" (max comment-beg (point-at-bol)))
    (eq (char-before (point)) ?\[)))

(defun company-coq--in-code-p-1 (pp)
  "Helper for `company-coq--in-code-p'.
PP is the result of calling `syntax-ppss' on point."
  (let* ((in-comment-p (nth 4 pp))
         (comment-or-str-beg (nth 8 pp)))
    (or (not comment-or-str-beg) ;; In code
        (and in-comment-p ;; Or in a code block comment
             (company-coq--in-escaped-code-block-p comment-or-str-beg)))))

(defun company-coq-in-code-p ()
  "Return non-nil if point is in code context.
Code contexts are portions of the buffer outside comments and
strings, and code blocks in comments.  Thus this function returns
nil in “(* abc| ”, but t in “(* abc [p| ”.
Useful as a value for `company-coq-completion-predicate'."
  (company-coq--in-code-p-1 (syntax-ppss)))

(defalias 'company-coq-not-in-comment-text-or-string-p 'company-coq-in-code-p)

(defconst company-coq-unification-error-header
  "\\(?:The command has indeed failed with message\\|Error\\):"
  "Header of unification errors.")

(defconst company-coq-unification-error-quick-regexp
  (regexp-opt '("Refiner was given an argument"
                "Unable to unify"
                "Impossible to unify"
                "it is expected to have type"))
  "Fast regexp to check if current response is a unification error.")

(defconst company-coq-unification-error-messages
  '("Refiner was given an argument \".*\" of type \"\\(?1:.*?\\)\" instead of \"\\(?2:.*?\\)\"."
    "Unable to unify \"\\(?1:.*?\\)\" with \"\\(?2:.*?\\)\"."
    "Impossible to unify \"\\(?1:.*?\\)\" with \"\\(?2:.*?\\)\"."
    "\\(?:In environment.*\\)?The term \".*\" has type \"\\(?1:.*?\\)\" while it is expected to have type \"\\(?2:.*?\\)\".")
  "Bodies of unification errors.")

(defconst company-coq-unification-error-message
  (replace-regexp-in-string
   (regexp-quote ".") (replace-quote "\\(?:.\\|[\n]\\)")
   (replace-regexp-in-string
    "[ \n]" (replace-quote "\\s-*")
    (concat "\\(?:" company-coq-unification-error-header " \\)+" "\\(?:"
            (mapconcat #'identity company-coq-unification-error-messages "\\|")
            "\\)\\s-*\\(?:" "(cannot unify \"\\(?3:.*?\\)\" and \"\\(?4:.*?\\)\")." "\\)?")))
  "Rexep matching unification error messages.")

(defconst company-coq-deprecated-options '("Equality Scheme" "Record Elimination Schemes"
                                "Tactic Evars Pattern Unification" "Undo")
  "Deprecated options, as reported by [Print Tables].")

(defconst company-coq-options-header-re (regexp-opt '("Set " "Unset " "Test "))
  "Regexp matching keywords starting option-related vernacs.")

(defconst company-coq-deprecated-options-re (concat "\\(?1:" company-coq-options-header-re
                                         (regexp-opt company-coq-deprecated-options) "\\)")
  "Regexp matching uses of deprecated options.")

(defconst company-coq-deprecated-vernacs-re (concat "\\(?1:" (regexp-opt '("Include Type"
                                                              "Arguments Scope"
                                                              "Implicit Arguments")) "\\)")
  "Regexp matching uses of deprecated vernacs.")

(defconst company-coq-deprecated-man-re
  (mapconcat (lambda (x) (concat "\\(?:\\_<" x "\\)"))
             '("\\(?1:assert\\) ([a-zA-Z_]+ ?:= .*)" "\\(?1:double induction\\)"
               "\\(?1:appcontext\\_>\\)[ a-zA-Z]*\\[" "\\(?1:cutrewrite\\) \\(?:<-\\|->\\)"
               "\\(?1:Backtrack [[:digit:]]+ [[:digit:]]+ [[:digit:]]+\\)" "\\(?1:SearchAbout\\_>\\)"
               "\\(?1:Save\\_>\\(?: \\(?:Lemma\\|Theorem\\|Remark\\|Fact\\|Corollary\\|Proposition\\)\\_>\\)?\\)"
               "\\(?1:absurd_hyp\\_>\\) [A-Za-z]")
             "\\|")
  "Regexp matching deprecating forms described by the manual.")

(defconst company-coq-deprecated-re (concat "^[[:blank:]]*\\(?:"
                                 "\\(?:" company-coq-deprecated-options-re "\\)\\|"
                                 "\\(?:" company-coq-deprecated-vernacs-re "\\)\\|"
                                 "\\(?:" company-coq-deprecated-man-re "\\)"
                                 "\\)")
  "Regexp matching all deprecated forms.")

(defvar company-coq--reserved-keywords-regexp nil
  "Regexp matching Coq's reserved keywords.")

(defun company-coq--reserved-keywords-regexp ()
  "Construct and cache a regexp matching Coq's reserved keywords."
  (or company-coq--reserved-keywords-regexp
      (setq company-coq--reserved-keywords-regexp
            (concat "^" (regexp-opt (append coq-reserved '("Set" "Prop" "Type"))) "$"))))

(defconst company-coq--doc-buffer "*company-coq: documentation*"
  "Name to give to company-coq documentation buffers.")

(defconst company-coq--goal-diff-buffer "*goal-diff*"
  "Name to give to company-coq goal diff buffers.")

(defconst company-coq--unification-diff-buffer "*unification-diff*"
  "Name to give to company-coq unification diff buffers.")

(defconst company-coq-script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst company-coq-refman-path
  (when company-coq-script-full-path
    (expand-file-name "refman/" (file-name-directory company-coq-script-full-path)))
  "Refman (and other assets)'s directory.")

(defface company-coq-doc-header-face-docs-and-sources
  '((t :height 1.5 :weight bold))
  "Face used to highlight the target line in source view."
  :group 'company-coq-faces)

(defface company-coq-doc-header-face-about
  '((t :inherit highlight :height 1.2))
  "Face used to highlight the target line in the docs."
  :group 'company-coq-faces)

(defface company-coq-doc-tt-face
  '((t :inherit font-lock-keyword-face :weight bold))
  "Face used to highlight keywords in the docs."
  :group 'company-coq-faces)

(defface company-coq-doc-i-face
  '((t :inherit font-lock-variable-name-face :weight bold :slant italic))
  "Face used to highlight symbol names in the docs."
  :group 'company-coq-faces)

(defface company-coq-comment-h1-face
  '((t :inherit font-lock-doc-face :height 2.5))
  "Face used to highlight *** comments."
  :group 'company-coq-faces)

(defface company-coq-comment-h2-face
  '((t :inherit font-lock-doc-face :height 1.8))
  "Face used to highlight *+ comments."
  :group 'company-coq-faces)

(defface company-coq-comment-h3-face
  '((t :inherit font-lock-doc-face :height 1.2))
  "Face used to highlight *! comments."
  :group 'company-coq-faces)

(defface company-coq-coqdoc-h1-face
  '((t :inherit font-lock-doc-face :inverse-video t :weight black))
  "Face used to highlight coqdoc's * comments."
  :group 'company-coq-faces)

(defface company-coq-coqdoc-h2-face
  '((t :inherit font-lock-doc-face :weight bold))
  "Face used to highlight coqdoc's ** comments."
  :group 'company-coq-faces)

(defface company-coq-coqdoc-h3-face
  '((t :inherit font-lock-doc-face :slant italic))
  "Face used to highlight coqdoc's *** comments."
  :group 'company-coq-faces)

(defface company-coq-coqdoc-h4-face
  '((t :inherit font-lock-doc-face))
  "Face used to highlight coqdoc's **** comments."
  :group 'company-coq-faces)

(defconst company-coq-goal-separator-spec
  `(("^   *\\(=====+ *\\)$"
     1 '(face (:strike-through t) display (space :align-to right)) append))
  "Font-lock spec for a sequence of '=' signs.")

(defconst company-coq-deprecated-spec
  `((,company-coq-deprecated-re 1 '(face (:underline (:color "#FF0000" :style wave))
                              help-echo "This form is deprecated (8.5)")
                     append))
  "Font-lock spec for deprecated forms.")

(defmacro company-coq-dbg (format &rest args)
  "Call `message' with FORMAT and ARGS if `company-coq-debug' is non-nil."
  `(when company-coq-debug
     (message (concat "company-coq: " ,format) ,@args)))

(defmacro company-coq-suppress-warnings (&rest body)
  "Run BODY, suppressing compilation warnings in Emacs <= 24.4."
  (declare (indent 0)
           (debug t))
  (if (and (= emacs-major-version 24) (< emacs-minor-version 4))
      `(with-no-warnings ,@body)
    `(progn ,@body)))

(defun company-coq--last-output-without-eager-annotation-markers ()
  "Return `proof-shell-last-output', without eager annotation markers.
Normally PG strips eager annotations, but
`company-coq-ask-prover' turns that mechanism off to not loose
output."
  (when proof-shell-last-output
    (if (or proof-shell-eager-annotation-start
            proof-shell-eager-annotation-end)
        (replace-regexp-in-string
         (concat "\\(?:" (or proof-shell-eager-annotation-start "") "\\)"
                 "\\(?1:[^0]+\\)"
                 "\\(?:" (or proof-shell-eager-annotation-end "") "\\)")
         "\\1" proof-shell-last-output t)
      proof-shell-last-output)))

(defun company-coq-trim (str)
  "Trim STR."
  (replace-regexp-in-string "\\`[ \r\n\t]+\\|[ \r\n\t]+\\'" "" str t t))

(defun company-coq-ask-prover (question)
  "Synchronously send QUESTION to the prover.
This function attemps to preserve the offsets of the
goals and response windows."
  (when question
    (if (company-coq-prover-available-p)
        (progn
          (setq company-coq-talking-to-prover t)
          (unwind-protect
              ;; `save-window-excursion' is still needed to restore any buffer
              ;; that might have been show instead of the goals or the response
              ;; (the fix to PG doesn't prevent it from restoring the window
              ;; configuration, and anyway the fix isn't deployed to everyone)
              (save-window-excursion
                ;; Coq-mode intercepts <infomsg>s using eager-annotation-start,
                ;; but it shouldn't.
                (let* ((proof-shell-eager-annotation-start nil)
                       (proof-shell-eager-annotation-end nil))
                  ;; proof-shell-invisible-cmd-get-result does not pass the
                  ;; 'no-goals-display flag, causing the goals buffer to jitter.
                  (proof-shell-invisible-command question 'wait nil
                                                 'no-response-display
                                                 'no-error-display
                                                 'no-goals-display))
                (company-coq-trim (company-coq--last-output-without-eager-annotation-markers)))
            (setq company-coq-talking-to-prover nil)))
      (company-coq-dbg "Prover not available; [%s] discarded" question)
      nil)))

(defun company-coq-error-message-p (msg)
  "Check if MSG is an error message."
  (and msg (string-match-p company-coq-error-regexp msg)))

(defun company-coq-unless-error (str)
  "Return STR, unless STR is an error message."
  (unless (company-coq-error-message-p str)
    str))

(defun company-coq-ask-prover-swallow-errors (question)
  "Call `company-coq-ask-prover' with QUESTION, swallowing errors.
Since the caller seems to be ok with this erroring out, we seize
the opportunity and wrap this in [Timeout 1] on Unixes."
  (unless (memq system-type '(cygwin windows-nt ms-dos))
    (setq question (format "Timeout 1 %s" question)))
  (company-coq-unless-error (company-coq-ask-prover question)))

(defun company-coq-split-lines (str &optional omit-nulls)
  "Split lines of STR.
If OMIT-NULLS is non-nil, remove empty strings from resulting list."
  (when str
    (split-string str "\n" omit-nulls)))

(defun company-coq-split-wrapped-lines (str &optional omit-nulls)
  "Unwrap STR and split it into lines.
If OMIT-NULLS is non-nil, remove empty strings from resulting list."
  (when str
    (let ((unwrapped (replace-regexp-in-string "\n +" " " str)))
      (company-coq-split-lines unwrapped omit-nulls))))

(defun company-coq-looking-back (regexp limit)
  "A greedy version of `looking-back'.
REGEXP and LIMIT are as in `looking-back'."
  (save-excursion
    (save-restriction
      (narrow-to-region limit (point))
      (goto-char limit)
      (re-search-forward (concat "\\(?:" regexp "\\)\\'") nil t))))

(defun company-coq-text-width (from to)
  "Measure the width of the text between FROM and TO.
Results are meaningful only if FROM and TO are on the same line."
  ;; (current-column) takes prettification into account
  (- (save-excursion (goto-char to)   (current-column))
     (save-excursion (goto-char from) (current-column))))

(defun company-coq-max-line-length ()
  "Return the width of the longest line in the current buffer."
  (save-excursion
    (goto-char (point-min))
    (cl-loop maximize (company-coq-text-width (point-at-bol) (point-at-eol))
             until (eobp) do (forward-line 1))))

(defun company-coq-truncate-buffer (start n-lines &optional ellipsis)
  "Truncate current buffer N-LINES after START.
Optionally adds an ELLIPSIS at the end."
  (cl-assert (and n-lines (> n-lines 0)))
  (save-excursion
    (goto-char start)
    (forward-line n-lines)
    (unless (eobp)
      (delete-region (point) (point-max))
      (forward-line -1)
      (goto-char (point-at-eol))
      (insert (or ellipsis " …")))))

(defun company-coq-prefix-all-lines (prefix)
  "Add a PREFIX to all lines of the current buffer."
  (save-excursion
    (goto-char (point-min))
    (while (not (eobp))
      (insert prefix)
      (forward-line 1))))

(defun company-coq-insert-spacer (pos)
  "Insert a thin horizontal line at POS."
  (save-excursion
    (goto-char pos)
    (let* ((from  (point))
           (to    (progn (insert "\n") (point)))
           (color (or (face-attribute 'highlight :background) "black")))
      (add-text-properties from to `(face (:height 1 :background ,color))))))

(defun company-coq-get-header (str)
  "Extract contents of STR, until the first blank line."
  (save-match-data
    (let ((header-end (and (string-match "\n\\s-*\\(\n\\|\\'\\)" str) (match-beginning 0))))
      (substring-no-properties str 0 header-end))))

(defun company-coq-boundp-string-match-p (regexp symbol)
  "Match REGEXP against SYMBOL.
If SYMBOL is undefined or nil, return nil."
  (and (boundp symbol)
       (symbol-value symbol)
       (string-match regexp (symbol-value symbol))))

(defun company-coq-boundp-equal (var symbol)
  "Check that VAR is defined, and compare its value to SYMBOL."
  (and (boundp var) (equal (symbol-value var) symbol)))

(defun company-coq-value-or-nil (symbol)
  "Get the value of SYMBOL.
Return nil if SYMBOL is undefined."
  (and (boundp symbol) (symbol-value symbol)))

(defun company-coq-insert-indented (lines)
  "Insert and indent LINES.
Ensures that the inserted text starts on a blank line."
  (save-excursion
    (unless (and (equal (point-at-bol) (skip-chars-backward " \t"))
                 (equal (point-at-eol) (skip-chars-forward " \t")))
      (newline)))
  (let ((beg (point-at-bol)))
    (mapc #'insert lines)
    (indent-region beg (point))
    (indent-according-to-mode)))

(defmacro company-coq-with-current-buffer-maybe (bufname &rest body)
  "If BUFNAME is a live buffer, run BODY in it."
  (declare (indent defun)
           (debug t))
  `(-when-let* ((bufname ,bufname)
                (buf (get-buffer bufname)))
     (with-current-buffer buf
       ,@body)))

(defun company-coq-extend-path (path components)
  "Extend PATH with each element of COMPONENTS."
  (if components
      (company-coq-extend-path (expand-file-name (car components) path) (cdr components))
    path))

(defun company-coq-chomp (l1 l2)
  "Remove the longest common prefix of L1 and L2.
Returns a cons of what remains"
  ;; (message "> [%s] [%s]" l1 l2)
  (while (and l1 l2 (string-prefix-p (car l1) (car l2)))
    (setq l1 (cdr l1))
    (setq l2 (cdr l2)))
  ;; (message "< [%s] [%s]" l1 l2)
  (cons l1 l2))

(defun company-coq-split-logical-path (path)
  "Split a logical PATH, such as a module path, into individual components."
  (unless (string-equal path "<>")
    (split-string path "\\.")))

(defun company-coq-prover-available-p ()
  "Return non-nil if the prover is available."
  (and (not company-coq-talking-to-prover)
       (proof-shell-available-p)))

(defun company-coq-prover-busy-p ()
  "Return non-nil if the prover is started and busy."
  (and (proof-shell-live-buffer)
       (not (company-coq-prover-available-p))))

(defun company-coq-reload-db (db init-fun track-symbol allow-nil needs-prover force)
  "Initialize DB using INIT-FUN if needed (or FORCE'd).
If NEEDS-PROVER is non-nil, ensure that the prover is available
before reloading.  If TRACK-SYMBOL is non-nil, use it to track
whether the database is up-to-date.  Reloading happens if the
reloading symbol has a non-nil value, or if the db has a nil
value.  A non-nil value for ALLOW-NIL strengthens the condition:
the second clause is ignored."
  (company-coq-dbg "company-coq-reload-db: Initializing %S (currently has %s elems)" db (length (symbol-value db)))
  (unless (and needs-prover (not (company-coq-prover-available-p)))
    (let ((non-nil (symbol-value db))
          (non-stale (or (null track-symbol) (not (symbol-value track-symbol)))))
      (unless (and (or non-nil allow-nil) non-stale (not force))
        (when track-symbol (set track-symbol nil))
        (set db (funcall init-fun)))))
  (symbol-value db))

(defun company-coq-prepare-redirection-command (cmd fname)
  "Prepare a command redirecting output of CMD to FNAME."
  (format company-coq-redirection-template fname cmd))

(defun company-coq-read-and-delete (fname)
  "Read FNAME, delete it, and return its contents."
  (ignore-errors
    (let ((contents (with-temp-buffer
                      (insert-file-contents fname nil nil nil t)
                      (buffer-string))))
      (delete-file fname)
      contents)))

(defun company-coq-ask-prover-redirect (cmd)
  "Synchronously send CMD to the prover, and return its output.
For performance, the output of the command is redirected to a
file and read back."
  (when cmd
    (let* ((prefix   (expand-file-name "coq" temporary-file-directory))
           (fname    (make-temp-name prefix))
           (question (company-coq-prepare-redirection-command cmd fname))
           (answer   (company-coq-ask-prover question)))
      (company-coq-dbg "Asking coq to redirect output of [%s] to [%s]" cmd prefix)
      (cons answer (company-coq-read-and-delete (concat fname ".out"))))))

(defun company-coq-get-symbols ()
  "Load symbols by querying the prover.
Do not call if the prover process is busy."
  (with-temp-message "company-coq: Loading symbols…"
    (let* ((start-time     (current-time))
           (_              (mapc #'company-coq-ask-prover company-coq-all-symbols-prelude))
           (output         (cdr (company-coq-ask-prover-redirect company-coq-all-symbols-cmd)))
           (extras         (cdr (company-coq-ask-prover-redirect company-coq-extra-symbols-cmd)))
           (_              (mapc #'company-coq-ask-prover company-coq-all-symbols-coda))
           (half-time      (current-time))
           (lines          (nconc (company-coq-split-lines output t) (company-coq-split-lines extras t)))
           (names          (company-coq-union-sort #'string-equal #'string-lessp lines)))
      (message "Loaded %d symbols (%d lines) in %.03f+%.03f seconds"
               (length names) (length lines) (float-time (time-subtract half-time start-time)) (float-time (time-since half-time)))
      names)))

(defun company-coq-get-ltacs ()
  "Load ltacs by querying the prover.
Do not call if the prover process is busy."
  (let* ((start-time     (current-time))
         (output         (cdr (company-coq-ask-prover-redirect company-coq-all-ltacs-cmd)))
         (lines          (company-coq-split-wrapped-lines output t))
         (tactics        (mapcar #'company-coq-parse-dynamic-ltacs-db-entry lines)))
    (company-coq-dbg "Loaded %d tactics in %.03f seconds"
          (length tactics) (float-time (time-since start-time)))
    tactics))

(defun company-coq-get-all-notations ()
  "Load tactic notations by querying the prover.
Do not call if the prover process is busy."
  (let ((output (company-coq-ask-prover-swallow-errors company-coq-all-notations-cmd)))
    (and output (company-coq-tg--extract-notations output))))

(defun company-coq-get-notations ()
  "Load tactic notations by querying the prover, ignoring some.
Tactics listed in `company-coq-tg--useless' are filtered out.
Do not call if the prover process is busy.
See also `company-coq-tactic-initialize-notations-filter'."
  (let ((tactics (company-coq-get-all-notations)))
    (unless company-coq-tg--useless ;; Fallback if initialization failed
      (setq company-coq-tg--useless (company-coq--list-to-table tactics)))
    (mapcar #'company-coq-parse-dynamic-notations-db-entry
            (company-coq--filter-using-table tactics company-coq-tg--useless))))

(defun company-coq-get-tactics ()
  "Load all tactics by querying the prover, including ltacs and definitions.
Do not call if the prover process is busy."
  (append (company-coq-get-ltacs) (company-coq-get-notations)))

(defun company-coq-tactic-initialize-notations-filter ()
  "Initialize the tactic notation exclusion list.
Tactics notations loaded when Coq starts are documented in the
manual, and should thus be ignored by the tactic grammar parser,
lest duplicates pop up."
  (setq company-coq-tg--useless (company-coq--list-to-table (company-coq-get-all-notations))))

(defun company-coq-init-symbols (&optional force)
  "Load symbols if needed or FORCE'd, by querying the prover."
  (interactive '(t))
  (when (company-coq-feature-active-p 'dynamic-symbols-backend)
    (company-coq-dbg "company-coq-init-symbols: Loading symbols (if never loaded)")
    (company-coq-reload-db 'company-coq-dynamic-symbols #'company-coq-get-symbols 'company-coq-symbols-reload-needed t t force)))

(defun company-coq-init-tactics (&optional force)
  "Load tactics if needed of FORCE'd, by querying the prover."
  (interactive '(t))
  (when (company-coq-feature-active-p 'dynamic-tactics-backend)
    (company-coq-reload-db 'company-coq-dynamic-tactics #'company-coq-get-tactics 'company-coq-tactics-reload-needed t t force)))

(defun company-coq-find-all (re beg end)
  "Find all occurences of RE between BEG and END.
Return results as ((MATCH-STRING 2) . POSITION)."
  (when (< beg end) ;; point-at-bol may be before unproc-beg
    (let ((case-fold-search nil)
          (matches          nil))
      (save-excursion
        (goto-char beg)
        (while (search-forward-regexp re end t)
          (push (cons (match-string-no-properties 2) (match-beginning 2)) matches)))
      matches)))

(defvar-local company-coq-local-definitions nil
  "Cache of local function definitions.")

(defvar-local company-coq-local-definitions-valid-from 1
  "Point up to which `company-coq-local-definitions' is accurate.")

(defvar-local company-coq-local-definitions-valid-up-to 1
  "Point up to which `company-coq-local-definitions' is accurate.")

(defun company-coq-collect-local-definitions ()
  "Find definitions of Coq symbols in the current buffer.
When completions are available directly from Coq, only look for
definitions in the unprocessed part of the buffer."
  (interactive) ;; NOTE this could timeout after a while
  (when (company-coq-feature-active-p 'local-definitions-backend)
    (let ((should-be-valid-from (if (company-coq-feature-active-p 'dynamic-symbols-backend)
                                    (proof-unprocessed-begin)
                                  (point-min)))
          (should-be-valid-up-to (point-at-bol)))
      (setq company-coq-local-definitions
            (append
             ;; New elements before cache
             (company-coq-find-all company-coq-definitions-regexp should-be-valid-from
                        (min should-be-valid-up-to company-coq-local-definitions-valid-from))
             ;; Old cache, minus stale elements
             (-filter (lambda (def)
                        (and (>= (cdr def) should-be-valid-from)
                             (<= (cdr def) should-be-valid-up-to)))
                      company-coq-local-definitions)
             ;; New elements after cache
             (company-coq-find-all company-coq-definitions-regexp (max should-be-valid-from company-coq-local-definitions-valid-up-to)
                        should-be-valid-up-to)))
      (setq company-coq-local-definitions-valid-from should-be-valid-from
            company-coq-local-definitions-valid-up-to should-be-valid-up-to))
    (mapcar (lambda (pair) (propertize (car pair)
                                  'location (current-buffer)
                                  'target (cdr pair)))
            company-coq-local-definitions)))

(defun company-coq--current-command-bounds ()
  "(Coarsely) find the limits of the current Coq phrase."
  (save-match-data
    (let ((bound-re "\\.[ \t\n]"))
      (list (or (save-excursion
                  (when (re-search-backward bound-re nil t)
                    (match-end 0)))
                (point-min))
            (or (save-excursion
                  (when (re-search-forward bound-re nil t)
                    (match-beginning 0)))
                (point-max))))))

(defun company-coq-line-is-import-p ()
  "Return non-nil if current line is part of an Import statement."
  (save-excursion
    (let* ((limit (point))
           (command-begin (or (re-search-backward "\\.[ \t\n]" nil t) (point-min)))
           (case-fold-search nil))
      (goto-char command-begin)
      (re-search-forward company-coq-import-regexp limit t))))

(defun company-coq-line-is-block-end-p ()
  "Return non-nil if point is at block end."
  (company-coq-looking-back company-coq-block-end-regexp (point-at-bol)))

(defun company-coq-parse-path-specs (loadpath-output)
  "Parse LOADPATH-OUTPUT as a sequence of module path specs.
Returns a list of pairs of (LOGICAL . PHYSICAL) paths."
  (when loadpath-output
    (save-match-data
      (cl-loop for     line
               in      (cdr (company-coq-split-wrapped-lines loadpath-output))
               if      (string-match company-coq-path-regexp line)
               collect (cons (match-string 1 line) (match-string 2 line))))))

(defun company-coq-get-path-specs ()
  "Load available modules by querying the prover.
Do not call if the prover process is busy."
  (interactive)
  (let* ((time       (current-time))
         (output     (company-coq-ask-prover-swallow-errors company-coq-modules-cmd))
         (path-specs (company-coq-parse-path-specs output)))
    (company-coq-dbg "Loaded %d modules paths (%.03f seconds)" (length path-specs) (float-time (time-since time)))
    path-specs))

(defun company-coq-init-modules (&optional force)
  "Load modules if needed or FORCE'd, by querying the prover."
  (interactive '(t))
  (when (company-coq-feature-active-p 'modules-backend)
    (company-coq-dbg "company-coq-init-modules: Loading modules (if never loaded)")
    (company-coq-reload-db 'company-coq-path-specs-cache #'company-coq-get-path-specs 'company-coq-modules-reload-needed t t force)))

(defun company-coq-collect-pg-abbrevs ()
  "Collect and parse abbrevs known by Proof General.
This used to load all tactics known by PG, but many of them did
not lend themselves well to autocompletion, and deduplication was
not fast."
  (let ((abbrevs (append '(("Module! (interactive)" nil "Module # : #.\n#\nEnd #." nil nil coq-insert-section-or-module)
                           ("match! (from type)" nil "" nil "match" company-coq-insert-match-construct)
                           ("intros! (guess names)" nil "intros #" nil nil coq-insert-intros)
                           ("as! (guess pattern)" nil "as #" nil nil company-coq-insert-as-clause)))))
    (-keep #'company-coq-parse-abbrevs-pg-entry abbrevs)))

(defvar company-coq--pg-abbrevs-cache nil
  "Cache of parsed PG abbrevs.")

(defun company-coq-init-pg-abbrevs (&optional force)
  "Load pg abbrevs if needed or FORCE'd."
  (interactive '(t))
  (company-coq-dbg "company-coq-init-pg-abbrevs: Loading abbrevs (if never loaded)")
  (company-coq-reload-db 'company-coq--pg-abbrevs-cache 'company-coq-collect-pg-abbrevs nil nil nil force))

(defface company-coq-snippet-hole-face
  '((t :slant italic :weight bold))
  "Face used to highlight holes in snippets."
  :group 'company-coq-faces)

(defun company-coq-cleanup-abbrev-2 (match)
  "Replace MATCH with a propertized replacement."
  (propertize (or (match-string 1 match) "#")
              'face '(company-coq-snippet-hole-face)))

(defconst company-coq--placeholder-regexps
  '("#" "$[0-9]" "@{\\(?1:[^}]+\\)}"
    "${\\(?:[0-9]+:\\)?\\(?1:[^}]+\\)}")
  "List of regular expressions matching holes in abbrevs.")

(defconst company-coq--all-placeholders-regexp
  (concat "\\(?:" (mapconcat #'identity company-coq--placeholder-regexps "\\|") "\\)")
  "Regular expression matching holes in abbrevs.
The content of the hole are bound to \\1.")

(defun company-coq-cleanup-abbrev-1 (abbrev)
  "Cleanup ABBREV for display, counting matches.
The return value is a cons of the cleaned-up string and the
number of matches."
  (let ((counter 0))
    (cons (replace-regexp-in-string company-coq--all-placeholders-regexp
                                    (lambda (match)
                                      (cl-incf counter)
                                      (company-coq-cleanup-abbrev-2 match))
                                    abbrev)
          counter)))

(defun company-coq-cleanup-abbrev (abbrev)
  "Cleanup ABBREV for display.
This doesn't move `match-beginning' and `match-end', so it's a
bit risky to call it after computing company's `match', at it
will change the length of the candidate."
  (pcase-let ((`(,abbrev . ,num-holes) (company-coq-cleanup-abbrev-1 abbrev)))
    (propertize abbrev 'num-holes num-holes)))

(defun company-coq-parse-abbrevs-pg-entry-1 (menuname _abbrev insert &optional _statech _kwreg insert-fun _hide)
  "Convert PG abbrev to internal company-coq format.
MENUNAME, INSERT, and INSERT-FUN are as in PG interal databases."
  (when (or (and insert (not (string-match-p (regexp-opt company-coq-excluded-pg-patterns) insert)))
            (and (not insert) insert-fun))
    (propertize (if insert-fun menuname (company-coq-cleanup-abbrev insert))
                'source 'pg
                'insert insert
                'insert-fun insert-fun)))

(defun company-coq-parse-abbrevs-pg-entry (abbrev)
  "Convert PG ABBREV to internal company-coq format."
  (apply #'company-coq-parse-abbrevs-pg-entry-1 abbrev))

(defun company-coq-parse-man-db-entry (abbrev-and-anchor)
  "Convert ABBREV-AND-ANCHOR imported from the manual to internal company-coq format."
  (let ((abbrev (car abbrev-and-anchor))
        (anchor (cdr abbrev-and-anchor)))
    (propertize (company-coq-cleanup-abbrev abbrev)
                'source 'man
                'anchor anchor
                'insert abbrev)))

(defun company-coq-parse-dynamic-ltacs-db-entry (line)
  "Convert one LINE of output of `company-coq-all-ltacs-cmd' to internal company-coq format."
  (let ((abbrev (replace-regexp-in-string " \\(\\S-+\\)" " @{\\1}" line)))
    (propertize (company-coq-cleanup-abbrev abbrev)
                'source 'ltac
                'insert abbrev)))

(defun company-coq-parse-dynamic-notations-db-entry (tactic)
  "Convert TACTIC notation to internal company-coq format."
  (propertize (company-coq-cleanup-abbrev tactic)
              'source 'tacn
              'insert tactic))

(defun company-coq-parse-custom-db-entry (abbrev)
  "Convert custom ABBREV to internal company-coq format."
  (propertize (company-coq-cleanup-abbrev abbrev)
              'source 'custom
              'insert abbrev))

(defun company-coq-get-prop (prop str)
  "Get text property PROP at index 0 of STR."
  (get-text-property 0 prop str))

(defun company-coq-append-copy (&rest sequences)
  "Append SEQUENCES, copying the last argument too."
  (apply #'append (append sequences '(nil))))

(defun company-coq-union-sort (test comp &rest lists)
  "Sort the concatenation of LISTS and remove duplicates.
Duplicates are detected using TEST, and sorting uses COMP as the
comparison function."
  (let ((merged  (cl-stable-sort (apply #'company-coq-append-copy lists) comp))
        (deduped nil)
        (prev    nil))
    (dolist (top merged)
      (unless (and prev (funcall test top prev))
        (push top deduped))
      (setq prev top))
    deduped))

(defun company-coq-sorted-intersection (l1 l2)
  "Compute the intersection of L1 and L2, assuming sortedness."
  (let ((inter nil))
    (while (and l1 l2)
      (cond
       ((string< (car l1) (car l2)) (pop l1))
       ((string< (car l2) (car l1)) (pop l2))
       ((string= (car l1) (car l2))
        (push (car l1) inter)
        (pop l1) (pop l2))))
    inter))

(defun company-coq-number (ls)
  "Add an increasing num text property to each element of LS."
  (let ((num 0))
    (mapc (lambda (x)
            (put-text-property 0 (length x) 'num num x)
            (setq num (+ 1 num)))
          ls)))

(defun company-coq--merge-sorted (seq1 seq2 lessp)
  "Merge sorted sequences SEQ1 and SEQ2 using comparison LESSP."
  (let ((merged nil))
    (while (and seq1 seq2)
      (if (funcall lessp (car seq1) (car seq2))
          (progn (push (car seq1) merged)
                 (setq seq1 (cdr seq1)))
        (push (car seq2) merged)
        (setq seq2 (cdr seq2))))
    (nconc seq1 seq2 (nreverse merged))))

(defun company-coq-is-lower (str)
  "Check if STR is lowercase."
  (let ((case-fold-search nil))
    (not (string-match-p "[[:upper:]]" str))))

(defun company-coq-string-lessp-foldcase (str1 str2)
  "Compare STR1 and STR2, case-independently."
  (string-lessp (upcase str1) (upcase str2)))

(defmacro company-coq-bool-lessp (bindings both-t &optional both-nil)
  "Boolean-compare BINDINGS, falling back to BOTH-T or BOTH-NIL."
  (declare (indent 1)
           (debug ((&rest (sexp form)) body body)))
  (let ((var1 (caar bindings))
        (var2 (cl-caadr bindings)))
    `(let ,bindings
       (cond
        ((and ,var1 (not ,var2)) t)
        ((and ,var1 ,var2) ,both-t)
        ((and (not, var1) (not ,var2) ,(or both-nil both-t)))))))

(defun company-coq-string-lessp-match-beginning (str1 str2)
  "Order STR1 and STR2 by match-begining being 0.
Falls back to `company-coq-string-lessp-foldcase'."
  (company-coq-bool-lessp ((m1 (eq 0 (company-coq-get-prop 'match-beginning str1)))
                (m2 (eq 0 (company-coq-get-prop 'match-beginning str2))))
    (company-coq-string-lessp-foldcase str1 str2)))

(defun company-coq-collect-user-snippets ()
  "Collect and propertize user snippets."
  (mapcar #'company-coq-parse-custom-db-entry company-coq-custom-snippets))

(defun company-coq-propertize-match (match beginning end)
  "Annotate completion candidate MATCH with BEGINNING and END."
  (company-coq-dbg "company-coq-propertize-match: %s %s %s" match beginning end)
  (put-text-property 0 (length match) 'match-beginning beginning match)
  (put-text-property 0 (length match) 'match-end end match)
  match)

(defun company-coq-complete-prefix-substring (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS starting with PREFIX.
With IGNORE-CASE, search case-insensitive."
  (let ((completion-ignore-case ignore-case)
        (case-fold-search       ignore-case)
        (prefix-re              (regexp-quote prefix)))
    (cl-loop for completion in completions
             if (string-match prefix-re completion)
             collect (company-coq-propertize-match completion (match-beginning 0) (match-end 0)))))

(defun company-coq--make-fuzzy-regexp (prefix)
  "Create a REGEXP for fuzzy matching of PREFIX."
  ;; The regexp says: skip stuff before beginning a new word, or skip nothing
  (concat "\\`\\W*" ;; Skip leading symbols (e.g. @)
          (mapconcat (lambda (c) (regexp-quote (char-to-string c)))
                     (string-to-list prefix) "\\(?:\\|[^\0]+?\\_<\\)")))

(defun company-coq-complete-sub-re (prefix candidates)
  "Find fuzzy candidates for PREFIX in CANDIDATES."
  (let* ((re (company-coq--make-fuzzy-regexp prefix))
         (case-fold-search nil))
    (save-match-data
      (cl-loop for     candidate
               in      candidates
               when    (string-match re candidate)
               collect (company-coq-propertize-match candidate 0 (match-end 0))))))

(defun company-coq-match-logical-paths (module-atoms path-atoms)
  "Match module path MODULE-ATOMS against logical path PATH-ATOMS.
Result is a cons (QUALID-ATOMS SEARCH-ATOMS LEFT-PTH).  This
function distinguishes three cases:

1. The logical path is longer; in this case, the qualifier is the
   full logical path, and the search term is empty.

2. The module path is longer; in this case, the qualifier is the
   full logical path, plus what remains of the module path (minus
   the last item of the module path), and the search term is the
   last item of the module path.

3. The two paths don't match; in this case, there is no qualifier
   nor search term."
  (pcase (company-coq-chomp module-atoms path-atoms)
    (`(,mod .  nil) (let ((subdirectory-atoms (butlast mod)))
                      (unless (member "" subdirectory-atoms) ;; We don't support skipping over subdirectories
                        (cons (append path-atoms subdirectory-atoms) (cons mod nil)))))
    (`(nil  . ,pth) (cons path-atoms (cons nil pth)))
    (_              nil)))

(defun company-coq-complete-module-unqualified (search-path search-regexp)
  "Find module names matching SEARCH-REGEXP in SEARCH-PATH.
Results are file names only, and do not include the .v[i]o
extension."
  (when (file-exists-p search-path)
    (cl-loop for file in (directory-files search-path nil nil t)
             if      (or (not search-regexp) (string-match-p search-regexp file))
             if      (string-match-p company-coq-compiled-regexp file)
             collect (replace-regexp-in-string company-coq-compiled-regexp "" file)
             else if (and (not (string-match-p "\\." file)) (file-directory-p (expand-file-name file search-path)))
             collect (concat file "."))))

(defun company-coq-take-summed-lengths (ls count)
  "Sum the lengths of the first COUNT lists in LS."
  (cl-loop for i = 0 then (+ 1 i)
           for l = ls then (cdr l)
           while (< i count)
           sum (length (car l))))

(defun company-coq-qualify-module-names (mod-names qualid-atoms fully-matched-count part-matched-len physical-path)
  "Qualify each name in MOD-NAMES using QUALID-ATOMS.
PHYSICAL-PATH is the path corresponding to QUALID-ATOMS.
See `company-coq-complete-module-from-atoms' for documentation of
FULLY-MATCHED-COUNT and PART-MATCHED-LEN."
  (when mod-names
    (let* ((qualid     (mapconcat 'identity qualid-atoms "."))
           (prefix     (if qualid-atoms (concat qualid ".") ""))
           (m-pref-len (company-coq-take-summed-lengths qualid-atoms fully-matched-count))
           (match-end  (+ m-pref-len ;; fully matched prefix
                          part-matched-len ;; partially matched element (end of search term)
                          fully-matched-count))) ;; dots
      (mapcar (lambda (mod-name)
                (propertize (concat prefix mod-name)
                            'meta      (concat physical-path " → " mod-name)
                            'location  (expand-file-name (concat mod-name ".v") physical-path)
                            'match-end match-end))
              mod-names))))

(defun company-coq-complete-module-qualified
    (qualid-atoms search-atoms physical-path fully-matched-count part-matched-len)
  "Find qualified module names in PHYSICAL-PATH that match SEARCH-ATOMS.
QUALID-ATOMS are the atoms corresponding to PHYSICAL-PATH.
See `company-coq-complete-module-from-atoms' for documentation of
FULLY-MATCHED-COUNT and PART-MATCHED-LEN."
  ;; (message "> [%s] [%s] [%s]" (prin1-to-string qualid-atoms) (prin1-to-string search-atoms) physical-path)
  (let* ((kwd           (car (last search-atoms)))
         (nil-kwd       (or (not kwd) (equal kwd "")))
         (ext-path      (company-coq-extend-path physical-path search-atoms))
         (search-path   (if nil-kwd (file-name-as-directory ext-path)
                          (file-name-directory ext-path)))
         (search-regexp (if nil-kwd nil (concat "\\`" (regexp-quote kwd))))
         (mod-names     (company-coq-complete-module-unqualified
                         search-path search-regexp)))
    ;; (message "Searching in [%s] with regexp [%s]: [%s]" search-path search-regexp mod-names)
    (company-coq-qualify-module-names mod-names qualid-atoms fully-matched-count part-matched-len search-path)))

(defun company-coq-complete-module-from-atoms (module-atoms path-atoms physical-path)
  "Wrapper around `company-coq-complete-module-qualified'.
MODULE-ATOMS, PATH-ATOMS, PHYSICAL-PATH are as in that function."
  (pcase (company-coq-match-logical-paths module-atoms path-atoms)
    (`(,qualid . (,search . ,pth))
     (let* (;; Fully matched count is the full qualid if the search term
            ;; (module-atoms) was strictly longer than the path, and otherwise
            ;; one less than the number of elements in common
            (fully-matched-count (if (eq search nil)
                                     (- (length path-atoms) (length pth) 1)
                                   (length qualid)))
            ;; Part matched len is always the length of the last search term
            (part-matched-len    (length (car (last module-atoms)))))
       (company-coq-complete-module-qualified qualid search physical-path fully-matched-count part-matched-len)))))

(defun company-coq-complete-module-from-path-spec (module-atoms path-spec)
  "Find modules matching MODULE-ATOMS in PATH-SPEC.
This essentially attempts to match MODULE-ATOMS to the logical
path in PATH-SPEC, and for each matching position computes a
search term and a qualifier."
  (pcase-let ((`(,logical-path . ,physical-path) path-spec))
    (let* ((path-atoms   (company-coq-split-logical-path logical-path))
           (completions  (list (company-coq-complete-module-from-atoms module-atoms nil physical-path))))
      (while path-atoms
        (push (company-coq-complete-module-from-atoms
               module-atoms path-atoms physical-path)
              completions)
        (setq path-atoms (cdr path-atoms)))
      (apply #'append completions))))

(defun company-coq-complete-modules (module)
  "Find completion candidates for MODULE."
  (when module
    (let* ((module-atoms (company-coq-split-logical-path module)))
      (apply #'company-coq-union-sort #'string-equal #'string-lessp
             (-keep (apply-partially #'company-coq-complete-module-from-path-spec
                                     module-atoms)
                    company-coq-path-specs-cache)))))

(defun company-coq-test-output-or-response (regexp cache-var)
  "Check last prover output against REGEXP.
Uses CACHE-VAR because some of the output may have been
redirected to response buffer, so we want to process that, but we
don't want to process the same thing repeatedly."
  (let ((response (company-coq-with-current-buffer-maybe proof-response-buffer
                    (buffer-string))))
    (or (unless (string= response (symbol-value cache-var))
          (set cache-var response)
          (string-match-p regexp response))
        (company-coq-boundp-string-match-p regexp 'proof-shell-last-output))))

(defvar company-coq-shell-output-is-end-of-def-response-cache nil
  "Contents of response buffer.
Updated when `company-coq-shell-output-is-end-of-def' is called.")

(defun company-coq-shell-output-is-end-of-def ()
  "Check output of the last command against `company-coq-end-of-def-regexp'."
  (company-coq-test-output-or-response company-coq-end-of-def-regexp 'company-coq-shell-output-is-end-of-def-response-cache))

(defvar company-coq-shell-output-is-error-response-cache nil
  "Last contents of response buffer.
Updated when `company-coq-shell-output-is-error' is called.")

(defun company-coq-shell-output-is-error ()
  "Check whether proof-general signaled an error."
  (company-coq-test-output-or-response company-coq-error-regexp 'company-coq-shell-output-is-error-response-cache))

(defun company-coq-shell-output-is-end-of-proof ()
  "Check whether proof-general signaled a finished proof."
  proof-shell-proof-completed)

(defun company-coq-warn (message &rest args)
  "Show a warning MESSAGE, formatted with ARGS."
  (display-warning 'company-coq (apply #'format message args) :warning))

(defun company-coq--coqtop-patched-p ()
  "Check whether coqtop has company-coq patches."
  (eq company-coq--coqtop-patched-result 'yes))

(defun company-coq-detect-capabilities ()
  "Update `company-coq--coqtop-patched-result' if needed."
  (when (eq company-coq--coqtop-patched-result 'unknown)
    (let* ((output (car (company-coq-ask-prover-redirect company-coq--capability-detection-cmd)))
           (risky-features '(dynamic-symbols-backend)))
      (when output
        (setq company-coq--coqtop-patched-result (if (company-coq-unless-error output) 'yes 'no))
        (message "Capability detection complete: dynamic completion is %savailable."
                 (if (company-coq--coqtop-patched-p) "" "not "))
        (when (and (cl-some #'company-coq-feature-active-p risky-features)
                   (not (company-coq--coqtop-patched-p)))
          (company-coq-warn (concat "Dynamic completion is enabled, but "
                         "your version of coqtop does not seem to support it.")))))))

(defun company-coq-maybe-reload-each ()
  "Reload dynamic completion databases if needed."
  (company-coq-dbg "company-coq-maybe-reload-each: [%s] [%s]"
        company-coq-symbols-reload-needed
        company-coq-modules-reload-needed)
  (when (company-coq-prover-available-p)
    (company-coq-detect-capabilities)
    (company-coq-init-tactics)
    (company-coq-init-symbols)
    (company-coq-init-modules)))

(defun company-coq--narrow-to-matches (opener closer)
  "Narrow current buffer to first matches of OPENER and CLOSER.
Returns non-nil iff narrowing was successful."
  (goto-char (point-min))
  (-when-let* ((beg (when (re-search-forward opener nil t)
                      (match-end 0)))
               (end (when (re-search-forward closer nil t)
                      (match-beginning 0))))
    (narrow-to-region beg end)
    (goto-char (point-min))))

(defun company-coq--bounded-re-search-forward (bound-re)
  "Search forward for text enclosed in instances of BOUND-RE.
Matches will look like BOUND-RE ... BOUND-RE, though the second
BOUND-RE is optional at the end of the buffer.  Spaces around the
body of the match are ommitted.  The body is returned as a
cons (BODY-TEXT . START).  Point is left at beginning of second
match for BOUND-RE (or at end of buffer)."
  (when (re-search-forward bound-re nil t)
    (skip-chars-forward " \r\n\t")
    (let ((body-start (point)))
      (save-match-data
        (if (re-search-forward bound-re nil t)
            (goto-char (match-beginning 0))
          (goto-char (point-max)))
        (save-excursion
          (skip-chars-backward " \r\n\t" body-start)
          (cons (buffer-substring-no-properties body-start (point)) body-start))))))

(cl-defstruct company-coq-hypothesis
  names separator type names-position type-position)

(defun company-coq--parse-hypothesis-match (pair)
  "Construct an hypothesis entry out of PAIR and match data."
  (make-company-coq-hypothesis
   :names (match-string-no-properties 1)
   :separator (match-string-no-properties 2)
   :type (car pair)
   :names-position (match-beginning 1)
   :type-position (cdr pair)))

(defun company-coq--collect-hypotheses ()
  "Find hypotheses in current buffer.
Return a `company-coq-hypothesis'.  SEP is ‘:’ or ‘:=’.  NAMES
may contain multiple names."
  (save-restriction
    (when (company-coq--narrow-to-matches company-coq--hypotheses-block-opener
                               company-coq--hypotheses-block-closer)
      (cl-loop for match = (company-coq--bounded-re-search-forward company-coq--hypothesis-header-regexp)
               while match collect (company-coq--parse-hypothesis-match match)))))

(defun company-coq--collect-hypothesis-names ()
  "Return names of all hypotheses in the current buffer."
  (cl-loop for entry in (company-coq--collect-hypotheses)
           append (split-string (company-coq-hypothesis-names entry) "\\s-*,\\s-*")))

(defun company-coq--split-string-with-positions-1 (prev-end end)
  "Construct a value for `company-coq--split-string-with-positions'.
See that function for from PREV-END and END."
  (cons (buffer-substring-no-properties prev-end end)
        (1- prev-end)))

(defun company-coq--split-string-with-positions (str regexp)
  "Split STR at instances of REGEXP.
Return values are in the form (STR FROM TO)."
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (let ((matches nil)
          (prev-end 1))
      (while (re-search-forward regexp nil t)
        (push (company-coq--split-string-with-positions-1
               prev-end (match-beginning 0))
              matches)
        (setq prev-end (match-end 0)))
      (push (company-coq--split-string-with-positions-1
             prev-end (1+ (length str)))
            matches)
      (nreverse matches))))

(defun company-coq--split-merged-hypothesis (hyp)
  "Split HYP into multiple hypotheses with one name per entry."
  (save-match-data
    (cl-loop for (name . offset) in (company-coq--split-string-with-positions
                                     (company-coq-hypothesis-names hyp) "\\s-*,\\s-*")
             collect (let ((copy (copy-company-coq-hypothesis hyp)))
                       (setf (company-coq-hypothesis-names copy) name)
                       (cl-incf (company-coq-hypothesis-names-position copy) offset)
                       copy))))

(defun company-coq--split-merged-hypotheses (hypotheses)
  "Compute a copy of HYPOTHESES with a single name per entry."
  (-mapcat #'company-coq--split-merged-hypothesis hypotheses))

(defun company-coq--collect-subgoals ()
  "Find subgoals in current buffer.
Returns a list of lists of the following form:
  (TYPE TYPE-FROM TYPE-TO)
where FROM and TO indicate buffer positions bounding TYPE."
  (goto-char (point-min))
  (cl-loop for match = (company-coq--bounded-re-search-forward company-coq--subgoal-header-regexp)
           ;; match is already in the form body . body-pos
           while match collect match))

(defun company-coq--parse-context-and-goals (response)
  "Extract a full parse of the context and the goal from RESPONSE."
  (with-temp-buffer
    (insert response)
    (list (company-coq--collect-hypotheses)
          (company-coq--collect-subgoals))))

(defun company-coq--collect-hypotheses-and-goal (response)
  "Extract a list of hypothesis names and a goal from RESPONSE."
  (with-temp-buffer
    (insert response)
    (list (company-coq--collect-hypothesis-names)
          (caar (company-coq--collect-subgoals)))))

(defun company-coq-run-then-collect-hypotheses-and-goal (command)
  "Send COMMAND to the prover, and return the new context and goal."
  (-if-let* ((output (company-coq-ask-prover-swallow-errors command)))
      (company-coq--collect-hypotheses-and-goal (replace-regexp-in-string "\n\n[^\0]*\\'" "" output))
    (error (format "company-coq-parse-context: No context to parse."))))

(defvar company-coq--previous-context nil
  "Last context displayed to the user.")

(defvar company-coq--current-context nil
  "Last context displayed to the user.")

(defvar company-coq--previous-context-parse nil
  "Parsed version of `company-coq--previous-context'.")

(defvar company-coq--current-context-parse nil
  "Parsed version of `company-coq--current-context'.")

(defvar company-coq--hyp-names nil
  "Names of hypotheses currently in context.")

(defun company-coq--update-context (&optional clear)
  "Update caches tracking the current goal.
If CLEAR is non-nil, clear all caches."
  (company-coq-dbg "company-coq--update-context: Called")
  (when (or (company-coq-feature-active-p 'goals-diff)
            (company-coq-feature-active-p 'context-backend))
    (let* ((new-context (or proof-shell-last-goals-output ""))
           (is-empty (string= new-context ""))
           (is-old (string= company-coq--current-context new-context)))
      (if (or clear is-empty)
          (setq company-coq--previous-context nil
                company-coq--current-context nil
                company-coq--previous-context-parse nil
                company-coq--current-context-parse nil
                company-coq--hyp-names nil)
        (unless is-old
          (setq company-coq--previous-context company-coq--current-context
                company-coq--current-context new-context
                company-coq--previous-context-parse company-coq--current-context-parse
                company-coq--current-context-parse (company-coq--parse-context-and-goals new-context)
                company-coq--hyp-names (mapcar #'company-coq-hypothesis-names
                                    (company-coq--split-merged-hypotheses
                                     (car company-coq--current-context-parse)))))))))

(defun company-coq-maybe-proof-output-reload-things ()
  "Parse output of prover, looking for signals that things need to be reloaded, and reload them."
  (interactive)
  (unless company-coq-talking-to-prover
    (company-coq-dbg "company-coq-maybe-proof-output-reload-things: last output is [%S]." proof-shell-last-output)
    (let ((is-error         (company-coq-shell-output-is-error))
          (is-end-of-def    (company-coq-shell-output-is-end-of-def))
          (is-end-of-proof  (company-coq-shell-output-is-end-of-proof)))
      (when is-end-of-proof (company-coq-dbg "company-coq-maybe-proof-output-reload-things: At end of proof"))
      (when is-end-of-def   (company-coq-dbg "company-coq-maybe-proof-output-reload-things: At end of definition"))
      (setq company-coq-symbols-reload-needed (or company-coq-symbols-reload-needed is-end-of-def is-end-of-proof))
      (setq company-coq-tactics-reload-needed (or company-coq-tactics-reload-needed is-end-of-def))
      (company-coq--update-context (or is-end-of-def is-end-of-proof))
      (if is-error (company-coq-dbg "Last output was an error; not reloading")
        (company-coq-dbg "This could be a good time to reload things?")
        ;; Delay call until after we have returned to the command loop.  The
        ;; “0.02” part is a fix for #121.  This timer may run while PG
        ;; busy-waits for a command to return, e.g. when user calls a command
        ;; that runs “Show Intros”.  Unfortunately, there doesn't seem to be a
        ;; way to detect this condition (the `proof-shell-busy' flag can be
        ;; unset just before our timer runs).
        (run-with-timer 0.02 nil #'company-coq-maybe-reload-each)))))

(defun company-coq-maybe-proof-input-reload-things ()
  "Parse output of prover, looking for signals that things need to be reloaded.
Nothing is reloaded immediately; instead the relevant flags are set."
  (interactive)
  (unless company-coq-talking-to-prover
    (company-coq-dbg "company-coq-maybe-proof-input-reload-things: Called")
    (let* ((is-advancing  (company-coq-boundp-equal 'action 'proof-done-advancing))
           (is-retracting (company-coq-boundp-equal 'action 'proof-done-retracting))
           (is-tac-not    (and is-advancing (company-coq-boundp-string-match-p company-coq-tac-notation-regexp 'string)))
           (is-import     (and is-advancing (company-coq-boundp-string-match-p company-coq-import-regexp 'string)))
           (is-load       (and is-advancing (company-coq-boundp-string-match-p company-coq-load-regexp   'string))))
      (when is-retracting (company-coq-dbg "company-coq-maybe-proof-input-reload-things: Rewinding"))
      (when is-import     (company-coq-dbg "company-coq-maybe-proof-input-reload-things: New import"))
      (when is-load       (company-coq-dbg "company-coq-maybe-proof-input-reload-things: Touching load path"))
      (setq company-coq-symbols-reload-needed (or company-coq-symbols-reload-needed is-import)) ;; is-retracting
      (setq company-coq-tactics-reload-needed (or company-coq-tactics-reload-needed is-import is-tac-not))
      (setq company-coq-modules-reload-needed (or company-coq-modules-reload-needed is-import is-load))
      (when is-retracting (company-coq--update-context t)))))

(defvar company-coq-goals-window nil
  "Window originally dedicated to Coq goals.")

(defun company-coq-get-goals-window ()
  "Return a window to redisplay the goals in."
  (let ((pg-buffer proof-goals-buffer))
    (or (and pg-buffer (get-buffer-window pg-buffer))
        (and (window-live-p company-coq-goals-window) company-coq-goals-window))))

(defun company-coq-get-response-window ()
  "Return the goals window."
  (and proof-response-buffer (get-buffer-window proof-response-buffer)))

(defun company-coq--quit-window (buf-name)
  "Quit window of BUF-NAME, if any.
Return non-nil iff such a window was found."
  (-when-let* ((win (get-buffer-window buf-name)))
    (save-selected-window
      (quit-window nil win)
      t)))

(defun company-coq-state-change (&rest _args)
  "Handle changes of prover state."
  (unless (window-live-p company-coq-goals-window)
    (setq company-coq-goals-window (company-coq-get-goals-window)))
  ;; Hide the docs and redisplay the goals buffer
  (dolist (buf `(,company-coq--doc-buffer
                 ,company-coq--goal-diff-buffer
                 ,company-coq--unification-diff-buffer))
    (when (setq buf (get-buffer buf))
      (company-coq--quit-window buf)))
  (-when-let* ((goals-buf proof-goals-buffer)
               (goals-win (company-coq-get-goals-window)))
    ;; Removing this test makes everything orders of magnitude slower on Jonathan's machine
    (unless (eq (window-buffer goals-win) goals-buf)
      (set-window-dedicated-p goals-win nil)
      (set-window-buffer goals-win goals-buf))))

(defun company-coq-coq-mode-p ()
  "Check if current buffer is in Coq mode."
  (derived-mode-p 'coq-mode))

(defun company-coq--proof-buffer-p ()
  "Check if current buffer is a Coq proof buffer."
  (or (company-coq-coq-mode-p)
      (memq major-mode '(coq-response-mode coq-goals-mode))))

(defvar company-coq--use-special-set-unset-test-regexp nil
  "If non-nil, consider ‘Set ’ (etc.) as valid prefixes.")

(defun company-coq-prefix-at-point ()
  "Compute prefix at point, for completion.
All candidates for a given company completion session must share
the same prefix: thus there can only be one prefix function for
all company-coq backends."
  (company-coq-dbg "company-coq-prefix-at-point: Called")
  (when (company-coq-coq-mode-p)
    ;; Don't complete in the middle of a word
    (unless (and (char-after) (memq (char-syntax (char-after)) '(?w ?_)))
      ;; Only complete if company-coq-completion-predicate allows it
      (when (or (null company-coq-completion-predicate) (funcall company-coq-completion-predicate))
        (save-excursion
          (when (or (and company-coq--use-special-set-unset-test-regexp
                         (company-coq-looking-back (concat company-coq-options-header-re company-coq-prefix-regexp) (point-at-bol)))
                    (company-coq-looking-back company-coq-prefix-regexp (point-at-bol)))
            (match-string-no-properties 0)))))))

(defun company-coq-symbol-at-point-with-pos ()
  "Return symbol at point and its left bound.
Does not use `coq-id-or-notation-at-point', because we want to
return the starting point as well."
  (let* ((start  (and (company-coq-looking-back company-coq-prefix-regexp (point-at-bol))
                      (save-excursion
                        (goto-char (match-beginning 0))
                        (skip-chars-forward ".")
                        (point))))
         (end (and start (save-excursion
                           (goto-char start)
                           (when (looking-at company-coq-symbol-regexp)
                             ;; No dots at end of symbol
                             (match-end 0))))))
    (when (and start end (< start end))
      (cons (buffer-substring-no-properties start end) start))))

(defun company-coq-symbol-at-point ()
  "Return symbol at point."
  (car (company-coq-symbol-at-point-with-pos)))

(defun company-coq-symbol-at-point-with-error ()
  "Return symbol at point, throwing an error if none is found."
  (-if-let* ((symbol (company-coq-symbol-at-point)))
      symbol
    (user-error "No identifier found at point")))

(defun company-coq-truncate-to-minibuf (str)
  "Truncate STR for display in minibuffer."
  (when str
    ;; (- … 10) adds some padding to compensate for wide characters
    (truncate-string-to-width str (max 5 (- (window-body-width (minibuffer-window)) 10)) 0 nil "…")))

(defun company-coq-meta-symbol (name)
  "Compute company's meta for symbol NAME."
  (company-coq-dbg "company-coq-meta-symbol: Called for name %s" name)
  (-when-let* ((output (company-coq-ask-prover-swallow-errors
                        (format company-coq-symbols-meta-cmd name))))
    (company-coq-truncate-to-minibuf
     (company-coq--fontify-string
      (replace-regexp-in-string "\\s-+" " " (company-coq-trim output))))))

(defun company-coq-meta-refman (name)
  "Compute company's meta for value NAME.
If NAME has an 'anchor text property, returns a help message."
  (company-coq-dbg "company-coq-meta-refman: Called for name %s" name)
  (and (company-coq-get-prop 'anchor name)
       (substitute-command-keys "\\<company-active-map>\\[company-show-doc-buffer]: Show the documentation of this Coq command.")))

(defun company-coq-meta-simple (name)
  "Read precomputed company's meta for NAME."
  (company-coq-dbg "company-coq-meta-simple: Called for name %s" name)
  (company-coq-truncate-to-minibuf
   (company-coq-get-prop 'meta name)))

(defun company-coq-display-in-pg-window (buffer)
  "Display BUFFER in PG window."
  ;; This always displays the buffer, unless no window is available.  This was
  ;; important (but it doesn't matter too much anymore), because if the window
  ;; is not displayed and shr-width is not set upon calling
  ;; `shr-insert-document', then shr will get the window width incorrectly, and
  ;; thus fail to wrap text properly.
  ;; Setting the wrap limit to a large value, as done by `company-coq-doc-refman-put-html'
  ;; fixes this, but it requires that we remove <table>s and <hr>s from the
  ;; manual, lest they cause an out of memory exception when rendering (eg. for
  ;; the "mutually co-inductive records error" documentation)
  (company-coq-dbg "Called company-coq-display-in-pg-buffer with %s" buffer)
  (-if-let* ((pg-window (company-coq-get-goals-window)))
      (progn (set-window-dedicated-p pg-window nil)
             (set-window-buffer pg-window buffer)
             pg-window)
    (display-buffer buffer)))

(defun company-coq-quit-window (kill)
  "Call `quit-window' and jump to the proof script buffer.
KILL: See `quit-window'."
  (interactive "P")
  (quit-window kill)
  (-when-let* ((win (and proof-script-buffer (get-buffer-window proof-script-buffer))))
    (select-window win)))

(defvar company-coq--temp-buffer-minor-mode-map
  (let ((cc-map (make-sparse-keymap)))
    (define-key cc-map (kbd "q") #'company-coq-quit-window)
    cc-map)
  "Keymap for company-coq's temp buffers.")

(define-minor-mode company-coq--temp-buffer-minor-mode
  "Makes it easy to close a temp Coq buffer."
  :lighter nil
  :keymap company-coq--temp-buffer-minor-mode-map)

(defun company-coq--setup-secondary-buffer ()
  "Ensure that Emacs doesn't offer to save the current buffer."
  (set-buffer-modified-p nil)
  (setq-local buffer-offer-save nil)
  (kill-local-variable 'kill-buffer-hook))

(defun company-coq--setup-doc-buffer ()
  "Prepare current buffer for documentation display."
  (visual-line-mode)
  (buffer-disable-undo)
  (company-coq--keybindings-minor-mode)
  (company-coq--temp-buffer-minor-mode)
  (company-coq--setup-secondary-buffer)
  (setq-local show-trailing-whitespace nil)
  (setq-local cursor-in-non-selected-windows nil))

(defmacro company-coq-with-clean-doc-buffer (&rest body)
  "Run BODY in a clean documentation buffer."
  (declare (indent defun)
           (debug body))
  `(progn
     (company-coq-dbg "company-prepare-doc-buffer: Called")
     (prog1
         (let ((doc-buffer (get-buffer-create company-coq--doc-buffer)))
           (with-selected-window (company-coq-display-in-pg-window doc-buffer)
             (with-current-buffer doc-buffer
               (let ((inhibit-read-only t))
                 (erase-buffer)
                 (remove-overlays)
                 (fundamental-mode)
                 (prog1 (progn ,@body)
                   (company-coq--setup-doc-buffer))))))
       (company-coq--record-selected-window))))

(defun company-coq-scroll-above-definition-at-pt ()
  "Highlight the current line and scroll up to for context."
  (forward-line -2)
  (or (and (coq-looking-at-comment)
           (car (company-coq--get-comment-region)))
      (point)))

(defun company-coq-search-then-scroll-up-1 (target fallback) ;; FIXME remove fallback?
  "Compute target point and window pos from TARGET and FALLBACK."
  (when (stringp fallback)
    (setq fallback (concat "\\_<\\(?2:" (regexp-quote fallback) "\\)\\_>\\s-*:[^=]")))
  (save-excursion
    (if (or (and (number-or-marker-p target)
                 (goto-char target))
            (and (stringp target)
                 (goto-char (point-min))
                 (or (re-search-forward target nil t)
                     (and (stringp fallback)
                          (re-search-forward fallback nil t)))))
        (progn (when (and (stringp target) (match-beginning 2))
                 (goto-char (match-beginning 2)))
               (list (point) (company-coq-scroll-above-definition-at-pt)))
      nil)))

(defun company-coq-search-then-scroll-up (target fallback callback)
  "Find a match for TARGET, then return a good point to scroll to.
Returns a point before that definition; it be a few lines higher
or, if that's inside a comment, at the beginning of the comment.
If target is nil, go to the top.  If target can't be found, look
for FALLBACK (followed by \\s-*:[^=]) instead.  If the target can
be found, call CALLBACK with the point where TARGET or FALLBACK
was found, and the value to be returned."
  (let ((point-pos (company-coq-search-then-scroll-up-1 target fallback)))
    (if point-pos
        (when (functionp callback)
          (apply callback point-pos))
      (when target ;; Not found ;; FIXME this happens when using ‘M-.’ in goals buffer for local def
        (message "Definition came from this buffer, but precise location is unknown.")))
    (or (cadr point-pos) (point-min))))

(defun company-coq-align-to (point window-top)
  "Go to POINT and scroll to WINDOW-TOP."
  (goto-char point)
  (set-window-start (selected-window)
                    (save-excursion
                      ;; set-window-start needs pt at bol
                      (goto-char window-top)
                      (point-at-bol))))

(defun company-coq-recenter-on (point)
  "Go to POINT and scroll to it."
  (goto-char point)
  (recenter))

(defun company-coq--highlight-and-align (point window-top)
  "Go to POINT, highlight, and scroll to WINDOW-TOP."
  (company-coq-align-to point window-top)
  (company-coq-make-title-line 'company-coq-doc-header-face-docs-and-sources t))

(defun company-coq--pulse-and-recenter (point _window-top)
  "Go to POINT, then pulse."
  (company-coq-recenter-on point)
  (unless (eq system-type 'darwin) ;; Pulsing is slow on MacOS
    (pulse-momentary-highlight-one-line (point))))

(defun company-coq-location-simple (name &optional target)
  "Show context of NAME based on its location property.
Once location of NAME is found look for TARGET in it.  Returns a
cons suitable for passing to company's `location'."
  (company-coq-dbg "company-coq-location-simple: Called for name %s" name)
  (let* ((fname-or-buffer (company-coq-get-prop 'location name))
         (is-buffer       (and fname-or-buffer (bufferp fname-or-buffer)))
         (is-fname        (and fname-or-buffer (stringp fname-or-buffer) (file-exists-p fname-or-buffer))))
    (if (or is-buffer is-fname)
        (company-coq-with-clean-doc-buffer
          (cond (is-buffer (insert-buffer-substring fname-or-buffer))
                (is-fname  (insert-file-contents fname-or-buffer nil nil nil t)))
          (coq-mode)
          (company-coq-mode)
          (cons (current-buffer)
                (company-coq-search-then-scroll-up
                 ;; When there's a TARGET, use NAME as the fallback
                 target (when target name) #'company-coq--highlight-and-align))))))

(defun company-coq-longest-matching-path-spec (qname)
  "Find the longest logical name matching QNAME.
Returns the corresponding (logical name . real name) pair."
  (cl-loop for     (logical . real)
           in      company-coq-path-specs-cache
           with    longest = nil
           when    (string-match-p (concat "\\`" (regexp-quote logical) "\\.") qname)
           do      (when (> (length logical) (length (car longest)))
                     (setq longest (cons logical real)))
           finally return longest))

(defun company-coq-library-path (lib-path mod-name fallback-spec)
  "Find a .v file likely to hold the definition of (LIB-PATH MOD-NAME).
May also return a buffer visiting that file.  FALLBACK-SPEC is a
module path specification to be used if [Locate Library] points
to a non-existent file (for an example of such a case, try
\[Locate Library Peano] in 8.4pl3)."
  (if (and (equal lib-path "") (equal mod-name "Top"))
      (current-buffer)
    (let* ((lib-name (concat lib-path mod-name))
           (output   (company-coq-ask-prover-swallow-errors (format company-coq-locate-lib-cmd lib-name))))
      (or (and output (save-match-data
                        (when (and (string-match company-coq-locate-lib-output-format output)
                                   (string-match-p company-coq-compiled-regexp (match-string-no-properties 3 output)))
                          (concat (match-string-no-properties 2 output) ".v"))))
          (and fallback-spec (expand-file-name (concat mod-name ".v") (cdr fallback-spec)))))))

(defun company-coq--locate-name (name functions)
  "Find location of NAME using FUNCTIONS.
FUNCTIONS are called successively with NAME until one of them
returns proper output, which must be a cons of a file name or
buffer, followed by a (possibly empty) regexp used to find NAME
in that file."
  (cl-loop for function in functions
           thereis (funcall function name)))

(defun company-coq--loc-output-regexp (headers)
  "Create a regexp matching HEADERS followed by a name."
  (concat "\\`" (regexp-opt headers) "\\_>[\n[:space:]]+" "\\(" company-coq-symbol-regexp "\\)"))

(defun company-coq--loc-fully-qualified-name (fqn)
  "Find source file for fully qualified name FQN."
  (let* ((spec (company-coq-longest-matching-path-spec fqn))
         (logical (if spec (concat (car spec) ".") ""))
         (mod-name (replace-regexp-in-string "\\..*\\'" "" fqn nil nil nil (length logical))))
    (company-coq-library-path logical mod-name spec)))

(defun company-coq--fqn-with-regexp-1 (name cmd-format response-format)
  "Find qualified name of NAME using CMD-FORMAT and RESPONSE-FORMAT."
  (-when-let* ((output (company-coq-ask-prover-swallow-errors (format cmd-format name))))
    (save-match-data
      (when (string-match response-format output)
        (match-string-no-properties 1 output)))))

(defun company-coq--fqn-with-regexp (name cmd-format response-headers)
  "Find qualified name of NAME using CMD-FORMAT and RESPONSE-HEADERS."
  (company-coq--fqn-with-regexp-1 name cmd-format (company-coq--loc-output-regexp response-headers)))

(defun company-coq--loc-with-regexp (name cmd-format response-headers)
  "Find location of NAME using CMD-FORMAT and RESPONSE-HEADERS.
Returns a cons as specified by `company-coq--locate-name'."
  (-when-let* ((fqn (company-coq--fqn-with-regexp name cmd-format response-headers))
               (loc (company-coq--loc-fully-qualified-name fqn))
               (short-name (replace-regexp-in-string "\\`.*\\." "" fqn)))
    (cons loc (concat (company-coq-make-headers-regexp response-headers)
                      "\\s-*\\(" (regexp-quote short-name) "\\)\\_>"))))

(defun company-coq--loc-symbol (symbol)
  "Find the location of SYMBOL."
  (company-coq--loc-with-regexp symbol "Locate %s." `("Notation" "Constant" ,@company-coq-definitions-kwds)))

(defun company-coq--loc-tactic (tactic)
  "Find the location of TACTIC."
  (company-coq--loc-with-regexp tactic "Locate Ltac %s." '("Ltac")))

(defun company-coq--loc-constructor (constructor)
  "Find the location of CONSTRUCTOR."
  ;; First check if CONSTRUCTOR is indeed a constructor
  (when (company-coq--fqn-with-regexp constructor "Locate %s." '("Constructor"))
    ;; Then obtain it's parent type using Print
    (-when-let* ((parent (company-coq--fqn-with-regexp constructor "Print %s." '("Inductive"))))
      (company-coq--loc-with-regexp parent "Locate %s." '("Inductive")))))

(defun company-coq--loc-field (field)
  "Find the location of FIELD (from a record)."
  ;; First check if RECORD is indeed a constructor
  (-when-let* ((record (company-coq--fqn-with-regexp-1
                        field
                        "Check {| %s := _ |}"
                        (concat "{|.*|}[ \n]+:[ \n]+\\(" company-coq-symbol-regexp "\\)"))))
    (company-coq--loc-with-regexp record "Locate %s." '("Inductive" "Record" "Class"))))

(defun company-coq--loc-module (module)
  "Find the location of MODULE."
  ;; FIXME more docs.
  ;; FIXME this doesn't find modules other than file-level ones.
  ;; Try using Locate Module.
  (let ((candidates (company-coq-candidates-modules module)))
    (cl-loop for candidate in candidates
             when (string= module candidate)
             thereis (cons (company-coq-get-prop 'location candidate) nil))))

(defun company-coq--maybe-complain-docs-not-found (interactive-p doc-type name)
  "If INTERACTIVE-P, complain that do DOC-TYPE was found for NAME."
  (when interactive-p
    (user-error "No %s found for ‘%s’.%s" doc-type name
                (if (company-coq-prover-available-p) ""
                  " Try starting Coq, or waiting for processing to complete."))))

(defun company-coq-locate-internal (name fqn-functions display-fun &optional interactive)
  "Show the definition of NAME in source context.
Use FQN-FUNCTIONS to guess the fully qualified name of NAME
and its location, then use DISPLAY-FUN to show that name.  If
INTERACTIVE, complain loudly if the location of NAME cannot be
determined."
  (company-coq-dbg "company-coq-location-source: Called for [%s]" name)
  (pcase (company-coq--locate-name name fqn-functions)
    (`(,fname . ,target) (funcall display-fun target fname name))
    (_ (company-coq--maybe-complain-docs-not-found interactive "location" name))))

(defun company-coq-location-source-1 (target location fallback)
  "Show TARGET in LOCATION; if not found, look for FALLBACK."
  (company-coq-location-simple (propertize fallback 'location location) target))

(defun company-coq-location-source (name fqn-functions)
  "Show the definition of NAME in source context.
FQN-FUNCTIONS: see `company-coq-locate-internal'."
  (company-coq-locate-internal name fqn-functions #'company-coq-location-source-1 nil))

(defvar company-coq-location-history nil
  "Keeps track of manual location queries.")

(defun company-coq-location-symbol (name)
  "Prompt for a symbol NAME, and display its definition in context."
  ;; (interactive (company-coq-location-interact (list company-coq-dynamic-symbols)))
  (company-coq-location-source name (list #'company-coq--loc-symbol)))

(defun company-coq-location-tactic (name)
  "Prompt for a tactic NAME, and display its definition in context."
  ;; (interactive (company-coq-location-interact (list company-coq-dynamic-tactics)))
  (company-coq-location-source (replace-regexp-in-string " .*" "" name) (list #'company-coq--loc-tactic)))

(defun company-coq-location-local-definition (name)
  "Display the definition of a local definition NAME in context."
  (company-coq-location-simple name (company-coq-get-prop 'target name)))

(defun company-coq-location-definition (name)
  "Prompt for a tactic or symbol NAME, and display its definition in context."
  ;; (interactive (company-coq-location-interact (list company-coq-dynamic-symbols company-coq-dynamic-tactics)))
  (company-coq-location-source name (list #'company-coq--loc-symbol #'company-coq--loc-tactic)))

;; (defun company-coq-jump-interact (dynamic-pool)
;;   "Prompt for, and read, a name to find sources for.
;; Completion candidates are taken from DYNAMIC-POOL."
;;   (let ((completions (apply #'append
;;                             (company-coq-collect-local-definitions)
;;                             dynamic-pool)))
;;     (list (completing-read "Name to find sources for? " completions
;;                            (lambda (choice) (not (eq (company-coq-get-prop 'source choice) 'tacn)))
;;                            nil nil 'company-coq-location-history (company-coq-symbol-at-point) t)
;;           t)))

(defun company-coq--save-location ()
  "Push point to xref marker stack and to global mark ring."
  (push-mark nil t)
  (when (fboundp 'xref-push-marker-stack)
    (xref-push-marker-stack)))

(defun company-coq-jump-to-definition-1 (target location fallback)
  "Jump to TARGET in LOCATION.  If not found, jump to FALLBACK."
  (cond
   ((bufferp location)
    (company-coq--save-location)
    (switch-to-buffer location))
   ((and (stringp location) (file-exists-p location))
    (company-coq--save-location)
    (find-file location))
   (t (user-error "Not found: %S" location)))
  (company-coq-search-then-scroll-up target fallback #'company-coq--pulse-and-recenter))

(defun company-coq-jump-to-definition (name &optional fqn-functions)
  "Jump to the definition of NAME, using FQN-FUNCTIONS to find it.
Interactively, use the identifier at point."
  (interactive (list (company-coq-symbol-at-point-with-error) nil))
  (company-coq-error-unless-feature-active 'cross-ref)
  (unless fqn-functions
    (setq fqn-functions (list #'company-coq--loc-module #'company-coq--loc-tactic
                              #'company-coq--loc-field #'company-coq--loc-symbol
                              #'company-coq--loc-constructor)))
  (company-coq-locate-internal name fqn-functions #'company-coq-jump-to-definition-1 t))

(defun company-coq-make-title-line (face &optional skip-space)
  "Format the current line as a title, applying FACE.
With SKIP-SPACE, do not format leading spaces."
  (let* ((start   (save-excursion (goto-char (point-at-bol))
                                  (if skip-space (skip-chars-forward " \t"))
                                  (point)))
         (end     (1+ (point-at-eol))) ;; +1 to cover the full line
         (overlay (make-overlay start end)))
    (overlay-put overlay 'face face)))

(defun company-coq-annotation-snippet (source candidate)
  "Compute company's annotation for snippet CANDIDATE.
SOURCE identifies the backend that produced CANDIDATE."
  (let* ((anchored  (company-coq-get-prop 'anchor candidate)))
    (propertize source 'face `(:underline ,(if anchored t nil)))))

(defun company-coq-annotation-tactic (candidate)
  "Compute company's annotation for tactic CANDIDATE."
  (symbol-name (company-coq-get-prop 'source candidate)))

(defun company-coq-doc-buffer-collect-outputs (name templates &optional fallbacks)
  "Insert NAME into each TEMPLATES, run these commands, and collect the outputs.
If no command succeed, do the same with FALLBACKS as TEMPLATES."
  (or (cl-loop for template in templates
               for cmd = (format template name)
               for output = (company-coq-ask-prover-swallow-errors cmd)
               when output collect output)
      (and fallbacks (company-coq-doc-buffer-collect-outputs name fallbacks))))

(defun company-coq-doc-buffer-generic (name cmds &optional interactive)
  "Prepare a doc buffer for NAME, using CMDS to collect information.
If INTERACTIVE is non-nil and no help is found, complain loudly."
  (company-coq-dbg "company-coq-doc-buffer-generic: Called for name %s" name)
  (-if-let* ((chapters (company-coq-doc-buffer-collect-outputs name cmds)))
      (let* ((fontized-name (propertize name 'font-lock-face 'company-coq-doc-i-face))
             (doc-tagline   (format company-coq-doc-tagline fontized-name))
             (doc-body      (mapconcat #'identity chapters company-coq-doc-def-sep))
             (doc-full      (concat doc-tagline "\n\n" doc-body)))
        (company-coq-with-clean-doc-buffer
          (insert doc-full)
          (coq-response-mode)
          (goto-char (point-min))
          (company-coq-make-title-line 'company-coq-doc-header-face-about)
          (current-buffer)))
    (company-coq--maybe-complain-docs-not-found interactive "documentation" name)))

(defun company-coq-doc-buffer-symbol (name)
  "Prepare a company doc buffer for symbol NAME."
  (company-coq-doc-buffer-generic name (list company-coq-doc-cmd
                                  company-coq-def-cmd)))

(defun company-coq-doc-buffer-definition (name)
  "Prepare a company doc buffer for definition NAME."
  (company-coq-doc-buffer-generic name (list company-coq-doc-cmd
                                  company-coq-def-cmd
                                  company-coq-tactic-def-cmd)))

(defun company-coq-doc-buffer-tactic (name)
  "Prepare a company doc buffer for tactic NAME."
  (setq name (replace-regexp-in-string " .*" "" name))
  (company-coq-doc-buffer-generic name (list company-coq-tactic-def-cmd)))

(defun company-coq-doc (name cmds)
  "Show documentation for NAME, using CMDS to build docs.
Interactively, use the identifier at point."
  (interactive (list (company-coq-symbol-at-point-with-error)
                     (list company-coq-doc-cmd company-coq-def-cmd company-coq-tactic-def-cmd)))
  (when (company-coq-doc-buffer-generic name cmds t)
    (company-coq--help-hide-docs)))

(defun company-coq-call-compat (func fallback &rest args)
  "Call FUNC, or FALLBACK if FUNC is undefined, on ARGS.
Acts as a compatibility layer for obsolete function in 24.3."
  (apply #'funcall (if (functionp func) func fallback) args))

(defun company-coq-shr-fontize (dom font)
  "Wrapper around `shr-fontize-cont' and `shr-fontize-dom'.
DOM and FONT are as in these functions."
  (company-coq-call-compat 'shr-fontize-cont 'shr-fontize-dom dom font))

(defun company-coq-shr-tag-tt (cont)
  "Format a tt tag CONT."
  (company-coq-shr-fontize cont 'company-coq-doc-tt-face))

(defun company-coq-shr-tag-i (cont)
  "Format an i tag CONT."
  (company-coq-shr-fontize cont 'company-coq-doc-i-face))

(defun company-coq--reasonable-shr-width ()
  "Return a good `shr-width' for rendering <table>s and <hr>s.
In Emacs 24 we set `shr-width' to `most-positive-fixnum' before
rendering to disable wrapping.  This works well for everything
except tables and horizontal rules, which we special-case in
`company-coq-shr-tag-table' and `company-coq-shr-tag-hr' lest shr
cause an OOM exception."
  (* (- (window-body-width) 2)
     (if (bound-and-true-p shr-use-fonts)
         (frame-char-width) 1)))

(defun company-coq-shr-tag-hr (_cont)
  "Format an hr tag CONT.
Don't even try to call shr; draw the line ourselves."
  (shr-ensure-newline)
  (insert (make-string (window-body-width) shr-hr-line) "\n"))

(defun company-coq-shr-tag-table (cont)
  "Format a table tag CONT."
  (let ((shr-internal-width (company-coq--reasonable-shr-width)))
    (shr-tag-table cont)))

(defun company-coq-doc-refman-prettify-title (target-point)
  "Make a pretty title at TARGET-POINT."
  (goto-char (or target-point (point-min)))
  (when target-point
    (company-coq-make-title-line 'company-coq-doc-header-face-docs-and-sources nil)
    (when (= (char-after (point)) ?*)
      (delete-char 1)))) ;; Remove the star (*) added by shr

(defconst company-coq-emacs-below-25-p
  (< emacs-major-version 25)
  "Whether Emacs version is below 25.")

(defconst company-coq-emacs-below-24.4-p
  (version< emacs-version "24.4")
  "Non-nil when SHR lacks target ids and external rendering.")

(defconst company-coq--shr-target-marker "!!COMPANY-COQ!!"
  "Used to mark the target html tag when shr can't do it.")

(defun company-coq--shr-maybe-find-target ()
  "Find an ‘id’ matching ‘shr-target-id’ and mark it."
  (when (and shr-target-id company-coq-emacs-below-24.4-p)
    (goto-char (point-min))
    (when (and (search-forward (format "id=\"%s\"" shr-target-id) nil t)
               (search-forward ">" nil t))
      (goto-char (match-end 0))
      (insert company-coq--shr-target-marker))))

(defun company-coq--shr-maybe-mark-target ()
  "Annotate text matching ‘company-coq--shr-target-marker’."
  (when (and shr-target-id company-coq-emacs-below-24.4-p)
    (goto-char (point-min))
    (when (search-forward company-coq--shr-target-marker nil t)
      (replace-match "" t t)
      (insert (propertize "*" 'shr-target-id t)))))

(defun company-coq-doc-refman-put-html (html-full-path)
  "Print formatted html from HTML-FULL-PATH in current buffer.
Highlights the surroundings of the first tag whose id is
‘shr-target-id’ (or at least try to on old Emacsen)."
  (let ((doc (with-temp-buffer
               (insert-file-contents html-full-path)
               (company-coq--shr-maybe-find-target)
               (libxml-parse-html-region (point-min) (point-max))))
        (shr-width (cond
                    ;; Below 24.4: Let shr do its wrapping and abandon hopes of
                    ;; proper wrapping of enlarged titles
                    (company-coq-emacs-below-24.4-p (company-coq--reasonable-shr-width))
                    ;; Below 25: Use infinite line width; external rendering
                    ;; functions ensure that this doesn't cause problems
                    (company-coq-emacs-below-25-p most-positive-fixnum)
                    ;; Emacs 25: using 0 disables wrapping; the special case for
                    ;; tables is still useful
                    (t 0)))
        (after-change-functions nil)
        (shr-external-rendering-functions '((tt . company-coq-shr-tag-tt)
                                            (i . company-coq-shr-tag-i)
                                            (hr . company-coq-shr-tag-hr)
                                            (table . company-coq-shr-tag-table))))
    (shr-insert-document doc) ;; This sets the 'shr-target-id property upon finding the shr-target-id anchor
    (company-coq--shr-maybe-mark-target)
    (company-coq-doc-refman-prettify-title (next-single-property-change (point-min) 'shr-target-id))))

(defun company-coq--help-hide-docs ()
  "Help the user hide the documentation window."
  (message (substitute-command-keys "Type \"\\<company-coq--temp-buffer-minor-mode-map>\\[company-coq-quit-window]\" in help window to restore previous buffer.")))

(defun company-coq-doc-buffer-refman (name-or-anchor &optional center)
  "Prepare a doc buffer for element NAME-OR-ANCHOR.
If NAME, read \\='anchor from it.  Otherwise use as anchor
directly.  With CENTER, center relevant point in window instead
of aligning at top."
  (interactive)
  (company-coq-dbg "company-coq-doc-buffer-refman: Called for %s" name-or-anchor)
  (when (fboundp 'libxml-parse-html-region)
    (let* ((anchor         (if (stringp name-or-anchor) (company-coq-get-prop 'anchor name-or-anchor) name-or-anchor))
           (shr-target-id  (and anchor (concat "qh" (int-to-string (cdr anchor)))))
           (doc-short-path (and anchor (concat (car anchor) ".html.gz")))
           (doc-full-path  (and doc-short-path (expand-file-name doc-short-path company-coq-refman-path))))
      (when doc-full-path
        (company-coq-with-clean-doc-buffer
          (company-coq-doc-refman-put-html doc-full-path)
          (beginning-of-line) ;; set-window-start needs point at bol
          (if center (recenter)
            (set-window-start (selected-window) (point)))
          (cons (current-buffer) (point)))))))

(defun company-coq-candidates-symbols (prefix)
  "Find symbols matching PREFIX."
  (when (company-coq-init-symbols)
    (company-coq-complete-prefix-substring prefix company-coq-dynamic-symbols)))

(defun company-coq-candidates-tactics (prefix)
  "Find tactics matching PREFIX."
  (when (company-coq-init-tactics)
    (company-coq-complete-sub-re prefix company-coq-dynamic-tactics)))

(defun company-coq-candidates-local-definitions (prefix)
  "Find local definitions matching PREFIX."
  (company-coq-complete-prefix-substring prefix (company-coq-collect-local-definitions)))

(defun company-coq-candidates-snippets (init-function prefix)
  "Find snippets matching PREFIX.
Database is generated by calling INIT-FUNCTION."
  (company-coq-dbg "company-coq-candidates-snippets: Called")
  (company-coq-complete-sub-re prefix (funcall init-function)))

(defun company-coq-candidates-context (prefix)
  "Find hypotheses matching PREFIX."
  (company-coq-complete-prefix-substring prefix company-coq--hyp-names))

(defun company-coq-candidates-modules (prefix)
  "Find modules matching PREFIX."
  (when (and (company-coq-line-is-import-p) (company-coq-init-modules))
    (company-coq-complete-modules prefix)))

(defun company-coq-candidates-block-end (prefix)
  "Find an open section to close matching PREFIX.
Works by finding the closest section/chapter/… opening, and
returning it if it matches PREFIX."
  (when (and prefix (company-coq-line-is-block-end-p))
    (save-excursion
      ;; Find matching delimiter
      (condition-case-unless-debug _
          (when (re-search-backward company-coq-block-end-regexp)
            (goto-char (match-beginning 1))
            (backward-up-list)
            (when (re-search-backward company-coq-section-regexp nil t)
              (let ((nearest-section-name (match-string-no-properties 2)))
                (when (and nearest-section-name
                           (string-match-p (concat "\\`" (regexp-quote prefix)) nearest-section-name))
                  (list (company-coq-propertize-match nearest-section-name 0 (length prefix)))))))
        (scan-error)))))

(defun company-coq-candidates-reserved (prefix)
  "Find reserved keywords matching PREFIX."
  (interactive)
  (let ((case-fold-search nil))
    (when (string-match-p (company-coq--reserved-keywords-regexp) prefix)
      (list prefix))))

(defun company-coq-parse-search-results ()
  "Extract and store symbols from the prover's output.
Only works after running a search command.  Results are stored in
`company-coq-last-search-results'.  Prover output size is cached
in `company-coq-last-search-scan-size'."
  (let* ((response-buffer proof-response-buffer)
         (response-size   (and response-buffer
                               (buffer-size response-buffer)))
         (needs-update    (and response-buffer
                               (not (equal response-size
                                           company-coq-last-search-scan-size)))))
    (unless (and response-buffer (not needs-update))
      (setq company-coq-last-search-results nil
            company-coq-last-search-scan-size nil))
    (when needs-update
      (setq company-coq-last-search-scan-size response-size)
      (with-current-buffer response-buffer
        (save-match-data
          (save-excursion
            (goto-char (point-min))
            (while (re-search-forward company-coq-all-symbols-slow-regexp nil t)
              (push (match-string-no-properties 1) company-coq-last-search-results))))))))

(defun company-coq-candidates-search-results (prefix)
  "Find search results matching PREFIX."
  (company-coq-parse-search-results)
  (company-coq-complete-prefix-substring prefix company-coq-last-search-results))

(defun company-coq-dabbrev-to-yas-format-one (match)
  "Convert dabbrev placeholder in MATCH to yasnippet format."
  (concat  "${" (or (match-string 1 match) company-coq-snippet-default-hole-contents) "}"))

(defun company-coq-yasnippet-choicify-one (match)
  "Convert dabbrev choice in MATCH to yasnippet format."
  (let ((choices (save-match-data (split-string (match-string 1 match) " | "))))
    (concat "${$$" (prin1-to-string `(company-coq-choose-value (list ,@choices))) "}")))

(defun company-coq-dabbrev-to-yas (abbrev)
  "Convert dabbrev without choices ABBREV to yasnippet format."
  (replace-regexp-in-string company-coq-dabbrev-to-yas-regexp
                            #'company-coq-dabbrev-to-yas-format-one abbrev))

(defun company-coq-dabbrev-to-yas-with-choices (abbrev)
  "Convert dabbrev ABBREV to yasnippet format."
  (let ((snippet (company-coq-dabbrev-to-yas abbrev))
        (case-fold-search t))
    (replace-regexp-in-string company-coq-yasnippet-choice-regexp
                              #'company-coq-yasnippet-choicify-one snippet)))

(defconst company-coq-abbrevs-transforms-alist '((man  . company-coq-dabbrev-to-yas-with-choices)
                                      (ltac . company-coq-dabbrev-to-yas)
                                      (tacn . company-coq-dabbrev-to-yas)
                                      (pg   . company-coq-dabbrev-to-yas))
  "Map of conversion functions to use on different abbrev sources.")

(defun company-coq-abbrev-to-yas (abbrev source)
  "Convert an abbrev ABBREV to yasnippet.
Which conversion function to use is determined from SOURCE."
  (company-coq-dbg "company-coq-abbrev-to-yas: Transforming %s" abbrev)
  (-if-let* ((transform (cdr-safe (assq source company-coq-abbrevs-transforms-alist))))
      (funcall transform abbrev)
    abbrev))

(defun company-coq-get-snippet (candidate)
  "Read yas-formatted snippet from CANDIDATE."
  (let* ((abbrev  (company-coq-get-prop 'insert candidate))
         (source  (company-coq-get-prop 'source candidate))
         (snippet (and abbrev (company-coq-abbrev-to-yas abbrev source))))
    snippet))

(defun company-coq-complain-unless-prover-available (msg)
  "Show an error message using MSG if the prover isn't available."
  (unless (company-coq-prover-available-p)
    (user-error "Please ensure that the prover is started and idle before %s" msg)))

(defun company-coq-call-insert-fun (insert-fun beg end)
  "Check if prover is available and call INSERT-FUN.
Before calling INSERT-FUN, delete BEG .. END."
  (delete-region beg end)
  (company-coq-complain-unless-prover-available "using smart completions")
  (call-interactively insert-fun))

(defun company-coq-post-completion-snippet (candidate)
  "Run post-action for CANDIDATE (most often, insert YAS snippet)."
  (when (search-backward candidate)
    (let* ((beg (match-beginning 0))
           (end (match-end 0))
           (snippet (company-coq-get-snippet candidate))
           (num-holes (company-coq-get-prop 'num-holes candidate))
           (insert-fun (company-coq-get-prop 'insert-fun candidate))
           (needs-newline (or insert-fun (> num-holes 0))))
      (cond
       (insert-fun
        (company-coq-call-insert-fun insert-fun beg end)
        (indent-according-to-mode))
       (snippet
        (yas-expand-snippet snippet beg end)))
      needs-newline)))

(defun company-coq-goto-occurence (&optional _event)
  "Close occur buffer and go to position at point."
  (interactive)
  (let ((pos (occur-mode-find-occurrence)))
    (let ((occur-buf (current-buffer)))
      (switch-to-buffer (marker-buffer pos))
      (goto-char pos)
      (kill-buffer occur-buf))))

(defun company-coq-occur ()
  "Show an outline of the current proof script."
  (interactive)
  (company-coq-error-unless-feature-active 'outline)
  (let* ((same-window-buffer-names '("*Occur*"))
         (source-name (buffer-name))
         (occur-title (format "Outline of [%s]" source-name)))
    (-when-let* ((buf (get-buffer occur-title)))
      (when (buffer-live-p buf)
        (kill-buffer buf)))
    (occur company-coq-outline-regexp-base)
    (company-coq-with-current-buffer-maybe "*Occur*"
      (rename-buffer occur-title t)
      (toggle-truncate-lines t)
      (let ((local-map (copy-keymap (current-local-map))))
        (substitute-key-definition #'occur-mode-goto-occurrence
                                   #'company-coq-goto-occurence local-map)
        (substitute-key-definition #'occur-mode-mouse-goto
                                   #'company-coq-goto-occurence local-map)
        (use-local-map local-map))
      (let ((inhibit-read-only t))
        (save-excursion ;; Prettify buffer title
          (goto-char (point-min))
          (when (re-search-forward "\\`[0-9]+\\s-*match.*\n*" (point-max) t)
            (replace-match (replace-quote (concat occur-title "\n")))
            (goto-char (point-min))
            (company-coq-make-title-line 'company-coq-doc-header-face-about)))))))

(defun company-coq-grep-symbol (regexp)
  "Recursively find REGEXP in .v files, starting from current directory."
  (interactive
   (list (cond
          ((use-region-p)
           (buffer-substring-no-properties (region-beginning) (region-end)))
          (t
           (let ((symbol (company-coq-symbol-at-point)))
             (if (> (length symbol) 1) (regexp-quote symbol)
               (read-from-minibuffer "Regexp to look for: ")))))))
  (company-coq-dbg "company-coq-grep-symbol: Looking for [%s]" regexp)
  (grep-compute-defaults)
  (message "Using regexp [%s]" regexp)
  (rgrep regexp "*.v" default-directory)
  (with-current-buffer next-error-last-buffer
    (let ((inhibit-read-only t))
      (save-excursion ;; Prettify buffer title
        (goto-char (point-min))
        (when (search-forward "find" nil t)
          (delete-region (point-min) (point-at-eol))
          (insert (format "Searching for [%s] in [%s]\n" regexp default-directory))
          (goto-char (point-min))
          (company-coq-make-title-line 'company-coq-doc-header-face-about))))))

(defun company-coq--make-diff-temp-buffer (bufname string prefix)
  "Insert STRING into BUFNAME, with optional PREFIX."
  (with-current-buffer (get-buffer-create bufname)
    (let ((inhibit-read-only t))
      (erase-buffer)
      (when prefix (insert prefix))
      (insert string)
      (newline))
    (current-buffer)))

(defun company-coq-diff-strings (s1 s2 prefix diff-buffer-name context)
  "Compare S1 and S2, with PREFIX.
Use DIFF-BUFFER-NAME to name newly created buffers.  Display CONTEXT lines
of context around differences."
  (let ((same-window-buffer-names '("*Diff*"))
        (b1 (company-coq--make-diff-temp-buffer (format "*company-coq-%s-A*" diff-buffer-name) s1 prefix))
        (b2 (company-coq--make-diff-temp-buffer (format "*company-coq-%s-B*" diff-buffer-name) s2 prefix)))
    (set-window-dedicated-p (selected-window) nil)
    (company-coq-with-current-buffer-maybe diff-buffer-name
      (kill-buffer))
    (unwind-protect
        (diff b1 b2 `(,(format "--unified=%d" context) "--minimal" "--ignore-all-space") 'noasync)
      (kill-buffer b1)
      (kill-buffer b2))
    (company-coq-with-current-buffer-maybe "*Diff*"
      (diff-refine-hunk)
      (rename-buffer diff-buffer-name)
      (save-excursion
        (goto-char (point-min))
        (let ((inhibit-read-only t))
          (when (re-search-forward "^@@" nil t)
            (delete-region (point-min) (match-beginning 0)))
          (while (re-search-forward " *\n *\n\\( *\n\\)+" nil t)
            ;; Remove spurious spacing added to prevent diff from mixing terms
            (replace-match "\n" t t)))))))

(defconst company-coq--diff-separator
  (concat (make-string 5 ?\n) (make-string 60 ?-) (make-string 5 ?\n)))

(defun company-coq--prepare-diff-chunks (&rest chunks)
  "Concat non-nil CHUNKS, adding lots of space in-between."
  (mapconcat #'identity (delq nil chunks) company-coq--diff-separator))

(defun company-coq-diff-unification-error (&optional context)
  "Compare two terms of a unification error, highlighting differences.
With prefix CONTEXT, display that many lines of context around
differences."
  (interactive "P")
  (with-current-buffer proof-response-buffer
    (save-match-data
      (save-excursion
        (goto-char (point-min))
        (if (re-search-forward company-coq-unification-error-message nil t)
            (let ((pre (company-coq--prepare-diff-chunks (match-string-no-properties 1)
                                              (match-string-no-properties 3)))
                  (post (company-coq--prepare-diff-chunks (match-string-no-properties 2)
                                               (match-string-no-properties 4))))
              (with-selected-window (or (company-coq-get-response-window) (selected-window))
                (company-coq-diff-strings pre post " " company-coq--unification-diff-buffer (or context 10))))
          (user-error "No unification error message found"))))))

(defun company-coq-diff-goals (&optional context)
  "Compare two terms of a unification error, highlighting differences.
With prefix CONTEXT, display that many lines of context around
differences."
  (interactive "P")
  (unless company-coq--current-context (user-error "Current goal unknown"))
  (unless company-coq--previous-context (user-error "Previous goal unknown"))
  (with-selected-window (or (company-coq-get-goals-window) (selected-window))
    (company-coq-diff-strings company-coq--previous-context company-coq--current-context
                   " " company-coq--goal-diff-buffer (or context 5))))

(defun company-coq-diff-dwim ()
  "Compare unification error messages (if any) or goals."
  (interactive)
  (unless (or (company-coq--quit-window company-coq--goal-diff-buffer)
              (company-coq--quit-window company-coq--unification-diff-buffer))
    (condition-case nil
        (company-coq-diff-unification-error)
      (user-error (company-coq-diff-goals)))
    (message "%s" (substitute-command-keys "Use \\[company-coq-diff-dwim] to hide the diff."))))

(defun company-coq-cant-fold-unfold ()
  "Return nil iff folding is possible at current point."
  ;; NOTE: This could work better by using information from show-paren-data-function
  (save-excursion
    (condition-case nil
        (progn (outline-back-to-heading) nil)
      (error t))))

(defun company-coq-fold ()
  "Hide the body of the current proof or definition.
When outside a proof, or when repeated, hide the body of all
proofs and definitions."
  (interactive)
  (company-coq-error-unless-feature-active 'outline)
  (when outline-minor-mode
    (if (or (eq last-command #'company-coq-fold) (company-coq-cant-fold-unfold))
        (company-coq-call-compat 'outline-hide-body 'hide-body)
      (company-coq-call-compat 'outline-hide-subtree 'hide-subtree))))

;; Disable company-coq-fold
(unless (plist-member (symbol-plist 'company-coq-fold) 'disabled)
  (put #'company-coq-fold 'disabled t))

(defun company-coq-unfold ()
  "Reveal the body of the current proof.
When outside a proof, or when repeated, reveal the body of all
proofs and definitions."
  (interactive)
  (company-coq-error-unless-feature-active 'outline)
  (when outline-minor-mode
    (if (or (eq last-command #'company-coq-unfold) (company-coq-cant-fold-unfold))
        (company-coq-call-compat 'outline-show-all 'show-all)
      (company-coq-call-compat 'outline-show-subtree 'show-subtree))))

(defun company-coq-dynamic-symbols-backend (command &optional arg &rest ignored)
  "`company-mode' backend for dynamically known Coq symbols.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "dynamic symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-dynamic-symbols-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-symbols arg))
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`match (company-coq-get-prop 'match-end arg))
    (`annotation "def")
    (`location (company-coq-location-symbol arg))
    (`doc-buffer (company-coq-doc-buffer-symbol arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-dynamic-tactics-backend (command &optional arg &rest ignored)
  "`company-mode' backend for dynamically known Coq tactics.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (pcase command
    (`interactive (company-begin-backend 'company-coq-dynamic-tactics-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-tactics arg))
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`no-cache t)
    (`match (company-coq-get-prop 'match-end arg))
    (`annotation (company-coq-annotation-tactic arg))
    (`location (company-coq-location-tactic arg))
    (`post-completion (company-coq-post-completion-snippet arg))
    (`doc-buffer (company-coq-doc-buffer-tactic arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-local-definitions-backend (command &optional arg &rest ignored)
  "`company-mode' backend for statically known Coq symbols.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "static symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-local-definitions-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-local-definitions arg))
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`match (company-coq-get-prop 'match-end arg))
    (`annotation "ldef")
    (`location (company-coq-location-local-definition arg))
    (`doc-buffer (company-coq-doc-buffer-definition arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-generic-snippets-backend (db-init-function backend command &optional arg &rest ignored)
  "Generic `company-mode' backend for annotated snippets.
DB-INIT-FUNCTION is a function initializing and returning a
database of snippets.  BACKEND is the name of the calling
backend.  COMMAND, ARG and IGNORED: see `company-backends'."
  (pcase command
    (`interactive (company-begin-backend backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-snippets db-init-function arg))
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`no-cache t)
    (`match (company-coq-get-prop 'match-end arg))
    (`post-completion (company-coq-post-completion-snippet arg))
    (`require-match 'never)))

(defun company-coq-user-snippets-backend (command &optional arg &rest ignored)
  "`company-mode' backend for user snippets.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "user snippets backend: called with command %s" command)
  (pcase command
    (`annotation (company-coq-annotation-snippet "usr" arg))
    (`sorted t) ;; User ordering is preserved
    (_ (apply #'company-coq-generic-snippets-backend #'company-coq-collect-user-snippets
              #'company-coq-user-snippets-backend command arg ignored))))

(defun company-coq-pg-backend (command &optional arg &rest ignored)
  "`company-mode' backend for user snippets.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "pg backend: called with command %s" command)
  (pcase command
    (`annotation (company-coq-annotation-snippet "pg" arg))
    (`sorted t) ;; Ordering of PG forms is preserved
    (_ (apply #'company-coq-generic-snippets-backend #'company-coq-init-pg-abbrevs
              #'company-coq-pg-backend command arg ignored))))

(defun company-coq-generic-refman-backend (db-init-fun backend command &optional arg &rest ignored)
  "Generic `company-mode' backend for documented abbrevs.
DB-INIT-FUN is a function initializing and returning a
database of snippets.  BACKEND is the name of the calling
backend.  COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (pcase command
    (`meta (company-coq-meta-refman arg))
    (`doc-buffer (company-coq-doc-buffer-refman arg))
    (`location (company-coq-doc-buffer-refman arg))
    (`annotation (company-coq-annotation-snippet "ref" arg))
    (`sorted t) ;; The static abbrevs cache is kept sorted
    (_ (apply #'company-coq-generic-snippets-backend db-init-fun
              backend command arg ignored))))

;; The specific refman backends are defined alongwith their corresponding
;; features below, using the `company-coq--define-refman-abbrevs-feature' macro.

(defun company-coq-context-backend (command &optional arg &rest ignored)
  "`company-mode' backend for hypotheses of the current proof.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "context backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-context-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-context arg))
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-simple arg))
    (`no-cache t)
    (`annotation "h")
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-modules-backend (command &optional arg &rest ignored)
  "`company-mode' backend for Coq modules.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "modules backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-modules-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-modules arg))
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-simple arg))
    (`location (company-coq-location-simple arg))
    (`no-cache t)
    (`match (company-coq-get-prop 'match-end arg))
    (`require-match 'never)))

(defun company-coq-block-end-backend (command &optional arg &rest ignored)
  "`company-mode' backend for the end of Sections and Chapters.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "section end backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-block-end-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-block-end arg))
    (`annotation "end")
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`require-match 'never)))

(defun company-coq-reserved-keywords-backend (command &optional arg &rest ignored)
  "`company-mode' backend for reserved keywords.
COMMAND, ARG and IGNORED: see `company-backends'.

This is mostly useful to prevent completion from kicking in
instead of inserting a newline, after e.g. typing [with].  The
insertion of the actual newline is taken care of by the master
backend; this backend merely ensures that the candidates are
there to begin with."
  (interactive (list 'interactive))
  (company-coq-dbg "reserved keywords backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-reserved-keywords-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-reserved arg))
    (`annotation "reserved")
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`require-match 'never)))

(defun company-coq-search-results-backend (command &optional arg &rest ignored)
  "`company-mode' backend for search results.
Results are computed by parsing the contents of the response buffer.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "search results backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-search-results-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-search-results arg))
    (`match (company-coq-get-prop 'match-end arg))
    (`annotation "search")
    (`sorted nil)
    (`duplicates nil)
    (`ignore-case nil)
    (`location (company-coq-location-definition arg))
    (`doc-buffer (company-coq-doc-buffer-definition arg))
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-math-symbols-backend (command &optional arg &rest ignored)
  "A thin wrapper around `company-math-symbols-unicode'.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (pcase command
    (`interactive (company-begin-backend 'company-coq-math-symbols-backend))
    (_ (let ((result (apply #'company-math-symbols-unicode command arg ignored)))
         (pcase command
           (`prefix (when (and result (not (string-prefix-p "_" result)))
                      (if (> (length result) 1)
                          (cons result t)
                        result)))
           (_ result))))))

(defun company-coq-tagged-candidates (backend prefix)
  "Compute and tag candidates from BACKEND for PREFIX."
  (let ((candidates (cl-loop for candidate in (funcall backend 'candidates prefix)
                             collect (propertize candidate 'company-coq-original-backend backend))))
    (if (funcall backend 'sorted)
        candidates
      (cl-stable-sort candidates (or (funcall backend 'comparison-fun)
                                     #'company-coq-string-lessp-foldcase)))))

(defun company-coq-sort-according-to-reference (seq ref)
  "Return a copy of SEQ, ordered by REF.
Common items come first (in the order in which they appear in
REF), followed by items exclusive to SEQ, in their original
order."
  (append
   ;; Common items
   (cl-remove-if-not (lambda (b) (member b seq)) ref)
   ;; Items only in SEQ
   (cl-remove-if (lambda (b) (member b ref)) seq)))

(defun company-coq-set-backends (backends)
  "Set `company-coq-enabled-backends' to BACKENDS, sorted according to `company-coq-sorted-backends'."
  (setq company-coq-enabled-backends (company-coq-sort-according-to-reference
                           backends company-coq-sorted-backends)))

(defun company-coq--mark-and-move-exact-matches (prefix sorted-candidates)
  "Return a copy of SORTED-CANDIDATES with all exact matches at the front.
PREFIX is the prefix that led to this completion session.  Exact
matches are additionally marked with 'exact-match."
  (let ((exact-matches nil)
        (plain-matches nil)
        (fuzzy-matches nil)
        (prefix-length (length prefix)))
    (dolist (candidate sorted-candidates)
      (cond
       ((string= prefix candidate)
        (push (propertize candidate 'exact-match t) exact-matches))
       ((and (eq (company-coq-get-prop 'match-beginning candidate) 0)
             (eq (company-coq-get-prop 'match-end candidate) prefix-length))
        (push candidate plain-matches))
       (t
        (push candidate fuzzy-matches))))
    (append (nreverse exact-matches)
            (nreverse plain-matches)
            (nreverse fuzzy-matches))))

(defun company-coq-candidates-master (prefix)
  "Compute all company-coq candidates for PREFIX."
  (company-coq--mark-and-move-exact-matches
   prefix
   (cl-loop for backend in company-coq-enabled-backends
            nconc (company-coq-tagged-candidates backend prefix))))

(defun company-coq-delegate-to-backend (command arg)
  "Pass COMMAND ARG IGNORED to the backend that ARG came from."
  (when (stringp arg)
    (-if-let* ((backend (company-coq-get-prop 'company-coq-original-backend arg)))
        (funcall backend command arg)
      ;; `pre-render (for annotations) is the only case where candidates may
      ;; appear without a -backend tag, and that case is handled by
      ;; `company-coq-master-backend' already
      (cl-assert nil))))

(defun company-coq-post-completion-master (arg)
  "Try post-completing ARG.
If the backend that produced ARG returns nil after
post-completing, insert a newline.  This heuristic ensures that
when users press RET after typing the top completion in full,
that completion a newline will be inserted.
Note that this only happens if the `company-defaults' feature
is enabled."
  (unless (company-coq-delegate-to-backend 'post-completion arg)
    (when (and (company-coq-get-prop 'exact-match arg)
               (company-coq-feature-active-p 'company-defaults))
      (call-interactively #'newline))))

(defun company-coq-master-backend (command &optional arg &rest ignored)
  "The master company-coq backend, merging results of other backends.
COMMAND, ARG and IGNORED: see `company-backends'.

This backend is used instead of company's native multi-backends,
because it makes it easier to enable or disable backends."
  (interactive (list 'interactive))
  (company-coq-dbg "master backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-master-backend))
    (`prefix (company-coq-prefix-at-point))
    (`candidates (company-coq-candidates-master arg))
    (`duplicates nil)
    (`ignore-case nil)
    (`sorted t) ;; Prevent company from re-sorting results
    (`no-cache t)
    (`require-match 'never)
    (`pre-render arg) ;; Show fontified candidates
    (`post-completion (company-coq-post-completion-master arg))
    (_ (company-coq-delegate-to-backend command arg))))

(defvar company-coq-choices-list nil)
(defvar company-coq-saved-idle-delay nil)

(defun company-coq-choose-value (values)
  "Set company up so that a completion list will popup with values VALUES.
This is a bit tricky, because it's not sufficient to just call
`company-begin-backend'; the reason is that company doesn't let
backends recursively calling it, and this function may be called
as the result of expanding a snippet, and thus as a descendant of
a company function.  Instead of calling it directly, we set the
idle delay to 0, and we override `this-command' to allow
completion to proceed."
  (unless company-coq-saved-idle-delay
    (setq company-coq-saved-idle-delay company-idle-delay))
  ;; (yas-verify-value values)
  (if yas-moving-away-p
      (company-coq-forget-choices)
    (setq company-coq-choices-list values
          this-command 'self-insert-command
          company-idle-delay 0))
  nil) ;; yas-text would work as well

(defun company-coq-forget-choices ()
  "Reset company after completing a choice through the choice backend.
See also `company-coq-choose-value'"
  (setq company-coq-choices-list nil
        company-idle-delay (or company-coq-saved-idle-delay company-idle-delay)
        company-coq-saved-idle-delay nil))

(defun company-coq-point-in-field ()
  "Check if point is in a yasnippet field."
  (and (boundp 'yas--active-field-overlay)
       (overlay-start yas--active-field-overlay)
       (overlay-end   yas--active-field-overlay)
       (<= (overlay-start yas--active-field-overlay) (point))
       (>= (overlay-end   yas--active-field-overlay) (point))))

(defun company-coq-choices-prefix ()
  "Compute prefix at point, for completion of a list of choices."
  (when (and company-coq-choices-list
             (company-coq-point-in-field))
    (cons (company-grab-word) t)))

(defun company-coq-choices-post-completion ()
  "Reset company and move to the next field.
See also `company-coq-choose-value'."
  (company-coq-forget-choices)
  (yas-next-field))

(defun company-coq-choices-backend (command &optional arg &rest ignored)
  "`company-mode' backend for holes allowing a pre-determined set of values.
COMMAND, ARG and IGNORED: see `company-backends'."
  (interactive (list 'interactive))
  (company-coq-dbg "choices backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-choices-backend))
    (`prefix (company-coq-choices-prefix))
    (`candidates (company-coq-complete-prefix-substring arg company-coq-choices-list t))
    (`post-completion (company-coq-choices-post-completion))
    (`sorted t)))

(defconst company-coq--core-map
  (let ((cc-map (make-sparse-keymap)))
    (define-key cc-map [remap proof-goto-point] #'company-coq-proof-goto-point)
    cc-map)
  "Keymap for core company-coq keybindings.
Do not edit this keymap: instead, edit `company-coq-map'.")

(defvar company-coq-map
  (let ((cc-map (make-sparse-keymap)))
    (define-key cc-map (kbd "C-c C-/")          #'company-coq-fold)
    (define-key cc-map (kbd "C-c C-\\")          #'company-coq-unfold)
    (define-key cc-map (kbd "C-c C-,")          #'company-coq-occur)
    (define-key cc-map (kbd "C-c C-&")          #'company-coq-grep-symbol)
    (define-key cc-map (kbd "C-c C-d")          #'company-coq-doc)
    (define-key cc-map (kbd "C-<return>")       #'company-manual-begin)
    (define-key cc-map (kbd "C-c C-a C-d")      #'company-coq-diff-dwim)
    (define-key cc-map (kbd "C-c C-a C-e")      #'company-coq-document-error)
    (define-key cc-map (kbd "C-c C-a C-x")      #'company-coq-lemma-from-goal)
    (define-key cc-map (kbd "C-c C-e")          #'company-coq-eval-last-sexp)
    (define-key cc-map (kbd "<M-return>")       #'company-coq-insert-match-rule-simple)
    (define-key cc-map (kbd "<M-S-return>")     #'company-coq-insert-match-rule-complex)
    (define-key cc-map (kbd "<C-down-mouse-1>") #'company-coq-show-definition-overlay-under-pointer)
    (define-key cc-map (kbd "<C-mouse-1>")      #'company-coq-clear-definition-overlay)
    (define-key cc-map (kbd "<menu>")           #'company-coq-toggle-definition-overlay)
    (define-key cc-map (kbd "<M-f12>")          #'company-coq-toggle-definition-overlay)
    (define-key cc-map (kbd "<backtab>")        #'company-coq-features/code-folding-toggle-block)
    (define-key cc-map (kbd "<S-tab>")          #'company-coq-features/code-folding-toggle-block)
    (define-key cc-map (kbd "<S-iso-lefttab>")  #'company-coq-features/code-folding-toggle-block)
    (define-key cc-map (kbd "SPC")              #'company-coq-maybe-exit-snippet)
    (define-key cc-map (kbd "RET")              #'company-coq-maybe-exit-snippet)
    (define-key cc-map (kbd "M-.")              #'company-coq-jump-to-definition)
    (define-key cc-map [remap coq-insert-match] #'company-coq-insert-match-construct)
    (define-key cc-map [remap narrow-to-defun]  #'company-coq-narrow-to-defun)
    cc-map)
  "Keymap of company-coq keybindings.
These keybindings are activated by `company-coq--keybindings-minor-mode'.")

(define-minor-mode company-coq--keybindings-minor-mode
  "Minor mode providing convenient company-coq keybindings."
  :lighter nil
  :keymap company-coq-map)

(defvar company-coq-electric-exit-characters '(?\; ?.)
  "Characters that exit the current snippet.")

(defun company-coq-after-exit-char ()
  "Check if previous character is in `company-coq-electric-exit-characters'."
  (member (char-before (point)) company-coq-electric-exit-characters))

(defun company-coq-current-yas-field-if-last (snippet)
  "Return the current YAS field of SNIPPET, if it is the last one."
  (-when-let* ((field (overlay-get yas--active-field-overlay 'yas--field))
               (fields (yas--snippet-fields snippet))
               (index (cl-position field fields)))
    (when (equal index (1- (length fields)))
      field)))

(defun company-coq-snippet-at-point ()
  "Get the snippet under the current point."
  (car (if (fboundp 'yas-active-snippets)
           (yas-active-snippets) ;; FIXME remove check when yas 0.12 lands
         (with-no-warnings (yas--snippets-at-point)))))

(defun company-coq-exit-snippet-if-at-exit-point ()
  "Check if exiting the CURRENT-SNIPPET would be a good idea."
  ;; Just typed ';' or '.'
  (when (company-coq-after-exit-char)
    ;; In a field of a snippet
    (-when-let* ((snippet (company-coq-snippet-at-point))
                 (field (company-coq-current-yas-field-if-last snippet)))
      (let* ((ppss (syntax-ppss))
             (paren-beginning (nth 1 ppss)))
        ;; Not in a parens opened after the current field
        (when (or (null paren-beginning)
                  (< paren-beginning (yas--field-start field)))
          (yas-exit-snippet (company-coq-snippet-at-point)))))))

(defun company-coq-maybe-exit-snippet (arg)
  "Exit the current snippet, if any.
Pass ARG to the function that would have been called had the
keybinding that called this not been intercepted."
  (interactive "p")
  (company-coq-exit-snippet-if-at-exit-point)
  (let* ((company-coq--keybindings-minor-mode nil)
         (original-func (key-binding (this-command-keys-vector) t)))
    (if original-func (call-interactively original-func)
      (self-insert-command arg))))

;; Needed for delete-selection-mode to work properly
(put 'company-coq-maybe-exit-snippet 'delete-selection t)

(defun company-coq-proof-goto-point (&rest args)
  "Pass ARGS to `proof-goto-point', hiding company dialog."
  (interactive)
  (when (bound-and-true-p company-mode)
    (company-abort))
  (apply #'proof-goto-point args))

(defmacro company-coq-repeat-until-fixpoint-or-scan-error (body retform)
  "Repeat BODY until a fixpoint or a scan error is reached, then eval RETFORM.
Execution of both forms is wrapped in `save-excursion'."
  (declare (debug t))
  `(save-excursion
     (condition-case nil
         (let ((prev-point nil))
           (while (not (equal prev-point (point)))
             (setq prev-point (point))
             ,body))
       (scan-error nil))
     ,retform))

(defun company-coq-beginning-of-proof ()
  "Go to beginning of proof."
  (interactive)
  (company-coq-repeat-until-fixpoint-or-scan-error
   (smie-backward-sexp-command 1) (point-at-bol)))

(defun company-coq-end-of-proof ()
  "Go to end of proof."
  (interactive)
  (company-coq-repeat-until-fixpoint-or-scan-error
   (smie-forward-sexp-command 1) (point-at-eol)))

(defun company-coq-narrow-to-defun ()
  "Narrow to current proof."
  (interactive)
  (narrow-to-region (company-coq-beginning-of-proof) (company-coq-end-of-proof)))

(defun company-coq-region-whitespace-p (beg end)
  "Check if region from BEG to END is blank."
  (save-excursion
    (goto-char beg)
    (skip-chars-forward " \t\r\n" end)
    (equal (point) end)))

(defmacro company-coq-on-blank-line (before after &rest body)
  "Remove whitespace, add BEFORE and AFTER around point, run BODY, and reindent.
BEFORE and AFTER can be the symbols space, newline, or nil."
  (declare (indent defun)
           (debug t))
  `(progn
     (delete-region (save-excursion (skip-chars-backward " " (point-at-bol)) (point))
                    (save-excursion (skip-chars-forward " " (point-at-eol)) (point)))
     (unless (eq (point) (point-at-bol))
       (insert ,before))
     (unless (eq (point) (point-at-eol))
       (save-excursion (insert ,after)))
     ,@body
     (indent-according-to-mode)))

(defun company-coq-insert-match-rule (snippet)
  "Insert SNIPPET on a blank line and indent."
  (when (featurep 'yasnippet)
    (company-coq-on-blank-line "\n" ""
      (yas-expand-snippet snippet))))

(defun company-coq-insert-match-rule-simple (&optional arg)
  "Insert a simple match rule.
With prefix ARG, insert an inductive constructor."
  (interactive "P")
  (company-coq-error-unless-feature-active 'snippets)
  (if (consp arg)
      (company-coq-insert-match-rule "| ${constructor} : $0")
    (company-coq-insert-match-rule "| ${_} => $0")))

(defun company-coq-insert-match-rule-complex (&optional arg)
  "Insert a complex match goal rule.
With prefix ARG, insert an inductive constructor with arguments."
  (interactive "P")
  (company-coq-error-unless-feature-active 'snippets)
  (if (consp arg)
      (company-coq-insert-match-rule "| ${constructor} : ${args} -> $0")
    (company-coq-insert-match-rule "| [ ${H: ${hyps}} |- ${_} ] => $0")))

(defconst company-coq--lemma-from-goal-prompt
  "Hypothesis to keep (name of hypothesis, or %s when done)? ")

(defun company-coq-lemma-from-goal-interact ()
  "Interactively collect a lemma name and hypothesis names."
  (let ((hyps       nil)
        (lemma-name "")
        (candidates `(,@(car (company-coq-run-then-collect-hypotheses-and-goal "Show")) "[done]")))
    (while (string-equal lemma-name "")
      (setq lemma-name (read-string "Lemma name? ")))
    (while (> (length candidates) 1) ;; "[done]" is always in there
      (let* ((key (if (bound-and-true-p helm-mode) "C-RET" "C-j"))
             (prompt (format company-coq--lemma-from-goal-prompt key))
             (hyp (completing-read prompt candidates nil t)))
        (if (member hyp '("" "[done]"))
            (setq candidates nil)
          (setq candidates (remove hyp candidates))
          (push hyp hyps))))
    (list lemma-name hyps)))

(defcustom company-coq-lemma-from-goal-adds-intros t
  "If non-nil, add an ‘intros’ line to extracted lemmas.
This extra line ensures that the new proof inherits hypothesis
names from previous proof."
  :group 'company-coq
  :type 'boolean)

(defun company-coq--new-intros (old-intros)
  "Return an intro statement for newly added parts of the goal.
OLD-INTROS is the result of Show Intros before new parts were
added."
  (let ((new-intros (company-coq-ask-prover-swallow-errors "Show Intros.")))
    (if (and old-intros new-intros)
        (let* ((old-split (split-string old-intros))
               (new-split (split-string new-intros))
               (nb-added (max 0 (- (length new-split) (length old-split)))))
          (-if-let* ((kept (-take nb-added new-split)))
              (format "intros %s.\n" (mapconcat 'identity kept " "))
            ""))
      "")))

(defun company-coq-lemma-from-goal--clear-unprotected-cmd (protected)
  "Generate a command to clear unprotected hypotheses.
Protected hypotheses are those that the goal and the hypotheses
in PROTECTED depend on."
  (let* ((tracker (mapconcat (lambda (hyp)
                               (format "let dummy := (%s) in" hyp))
                             protected " ")))
    (format "repeat match goal with company_coq_hyp__: _ |- _ => clear dependent company_coq_hyp__; %s idtac end" tracker)))

(defconst company-coq-lemma-from-goal--generalization-forms
  "repeat match goal with H:_ |- _ => generalize dependent H; try (generalize dependent H; fail 1) end"
  "Ltac script to produce a lemma statement.
The try (…) part ensures that section variables don't cause an
infinite loop (they are not cleared by [generalize dependent]).")

(defun company-coq-lemma-from-goal (lemma-name hyps)
  "Create a new lemma LEMMA-NAME and insert it.
Interactively, prompt the user for LEMMA-NAME, as well as
hypotheses HYPS to add to the lemma.  Depndencies of the goal and
of these hypotheses are also added to the lemma."
  (interactive (company-coq-lemma-from-goal-interact))
  (proof-shell-ready-prover)
  (-if-let* ((statenum (car (coq-last-prompt-info-safe))))
      (unwind-protect
          (-if-let* ((intros-before (company-coq-ask-prover-swallow-errors "Show Intros."))
                     (clear-cmd (company-coq-lemma-from-goal--clear-unprotected-cmd hyps))
                     (full-cmd (concat clear-cmd "; " company-coq-lemma-from-goal--generalization-forms))
                     (lemma (cadr (company-coq-run-then-collect-hypotheses-and-goal full-cmd)))
                     (intros (if company-coq-lemma-from-goal-adds-intros (company-coq--new-intros intros-before) "")))
              (company-coq-insert-indented (format "Lemma %s:\n%s.\nProof.\n%s" lemma-name lemma intros))
            (error "Lemma extraction failed"))
        (company-coq-ask-prover (format "BackTo %d." statenum)))
    (user-error "Please start a proof before extracting a lemma")))

(defun company-coq-insert-match-construct (type)
  "Insert a match expression for TYPE.
Similar to `coq-insert-match', but using YAS.  If the
pg-improvements feature isn't active, fallback to the regular
function."
  (interactive (list
                (if (company-coq-feature-active-p 'pg-improvements)
                    (read-from-minibuffer "Type to destruct (e.g. nat, bool, list, …): ")
                  'fallback)))
  (if (eq type 'fallback)
      (call-interactively #'coq-insert-match)
    (proof-shell-ready-prover)
    (let* ((question (format "Show Match %s" type))
           (response (company-coq-ask-prover question)))
      (if (company-coq-unless-error response)
          (let* ((cleaned (replace-regexp-in-string "\\s-+\\'" "" response))
                 (snippet (replace-regexp-in-string "=>$" "=> #" cleaned)))
            (yas-expand-snippet (company-coq-dabbrev-to-yas snippet)))
        (error response)))))

(defun company-coq-insert-as-clause-1 ()
  "Compute the as clause at point."
  (save-excursion
    (let* ((pt (point)))
      (re-search-backward "[;.]" (point-at-bol) t)
      (with-no-warnings (coq-find-real-start))
      (if (<= pt (point))
          (error "Cannot find a command to as an as clause to.  Try destruct [name] as!")
        (let* ((command (company-coq-trim (buffer-substring-no-properties (point) pt)))
               (infoh (with-no-warnings (coq-hack-cmd-for-infoH (concat command "."))))
               (response (company-coq-ask-prover infoh)))
          (when (string-match "<infoH>\\([^<]*\\)</infoH>" response)
            (let* ((match-form (match-string 1 response)))
              (if (string-match-p "^[| ]*$" match-form)
                  (user-error "Couldn't find names to introduce; this feature is still pretty experimental")
                (concat "as [" (replace-regexp-in-string "  +" " " (company-coq-trim match-form) t t) "]")))))))))

(defun company-coq-insert-as-clause ()
  "Insert an as clause for the command at point.
This is experimental, and only supported in 8.5."
  (interactive)
  (unless (company-coq-ask-prover-swallow-errors "infoH idtac.")
    (user-error "This features requires Coq 8.5 (for infoH) and works in proof context only"))
  (unless (and (fboundp 'coq-hack-cmd-for-infoH)
               (fboundp 'coq-find-real-start))
    (error "This feature requires a recent version of Proof General (it's on GitHub now)"))
  (insert (company-coq-insert-as-clause-1))
  (let ((last-command-event ?.))
    (proof-electric-terminator)))

(defun company-coq-normalize-error (msg)
  "Normalize error MSG to look it up in a list of errors."
  (let* ((truncated (replace-regexp-in-string "\\(?:.\\|[\n]\\)*Error:\\s-" "" msg))
         (cleaned   (replace-regexp-in-string "\"[^\"]+\"" "" truncated))
         (upped     (upcase cleaned))
         (split     (split-string upped "[^[:word:]0-9]+" t))
         (sorted    (sort split #'string<)))
    sorted))

(defun company-coq-find-errors-overlap (reference msg)
  "Compare two messages REFERENCE and MSG.
MSG must already be normalized."
  (let* ((norm-ref (company-coq-normalize-error (car reference)))
         (inter    (company-coq-sorted-intersection msg norm-ref)))
    (cons (cons (/ (float (length inter)) (length norm-ref))
                (length norm-ref))
          reference)))

(defun company-coq->> (x y)
  "Sort conses X and Y lexicographically."
  (or (> (car x) (car y))
      (and (= (car x) (car y))
           (> (cdr y) (cdr x)))))

(defun company-coq-find-closest-errors (msg)
  "Return know errors, sorted by proximity to MSG."
  (when (company-coq-error-message-p msg)
    (let* ((normalized    (company-coq-normalize-error msg))
           (intersections (cl-loop for reference in company-coq--refman-error-abbrevs
                                   collect (company-coq-find-errors-overlap reference normalized))))
      (sort intersections (lambda (x y) (company-coq->> (car x) (car y))))))) ;; LATER get maximum instead?

(defconst company-coq-error-doc-min-score 0.5
  "Minimum score for two errors to match.
Scores are computed by `company-coq-find-errors-overlap'.")

(defun company-coq-browse-error-messages ()
  "Browse list of all error messages."
  (interactive)
  (let* ((msg (completing-read "Error message: " company-coq--refman-error-abbrevs nil t))
         (anchor (cdr-safe (assoc msg company-coq--refman-error-abbrevs))))
    (when anchor
      (when (company-coq-doc-buffer-refman anchor t)
        (company-coq--help-hide-docs)))))

(defun company-coq-guess-error-message-from-response ()
  "Show documentation for error message in Coq's response, if available."
  (interactive)
  (let* ((err (company-coq-with-current-buffer-maybe proof-response-buffer (buffer-string)))
         (hit (and err (car (company-coq-find-closest-errors err)))))
    (company-coq-dbg "Top reference [%s] has score [%s]" (cadr hit) (car hit))
    (cond
     ((null hit)
      (user-error (substitute-command-keys "No error found.  Use C-u \\[company-coq-document-error] to browse errors")))
     ((< (caar hit) company-coq-error-doc-min-score)
      (error "No documentation found for this error"))
     (t
      (when (company-coq-doc-buffer-refman (cddr hit) t)
        (company-coq--help-hide-docs))))))

(defun company-coq-document-error (&optional arg)
  "Show documentation for error message in Coq's response, if available.
With prefix ARG, let user pick the error message."
  (interactive "P")
  (if (consp arg)
      (company-coq-browse-error-messages)
    (company-coq-guess-error-message-from-response)))

(defun company-coq-eval-last-sexp (arg)
  "Send the last SEXP to Coq as a Compute command.
With prefix ARG, insert output at point."
  (interactive "P")
  (let ((standard-output (if arg (current-buffer) t))
        (question (format "Eval compute in (%s)."
                          (buffer-substring-no-properties
                           (save-excursion (backward-sexp) (point))
                           (point)))))
    (message "%s" (company-coq-ask-prover question))))

(defun company-coq-search-in-coq-buffer (regexp)
  "Search for REGEXP in *coq* buffer.
Useful for debugging tactics in versions of Coq prior to 8.5: use
[idtac \"-->\" message] to print [message] to output, and
`company-coq-search-in-coq-buffer' to locate lines starting with
\"^-->\"."
  (interactive "MRegexp search in *coq* buffer: ")
  (-if-let* ((coq-buffer (get-buffer-create "*coq*"))
             (same-window-buffer-names '("*Occur*")))
      (with-current-buffer coq-buffer
        (occur regexp))
    (error "*coq* buffer not found")))

(defun company-coq-fontify-buffer ()
  "Refontify the current buffer."
  (with-no-warnings
    (if company-coq-emacs-below-25-p
        ;; Actually calls jit-lock-refontify, which doesn't refontify immediately
        (font-lock-fontify-buffer)
      (let ((font-lock-fontified t))
        (font-lock-flush)))))

(defconst company-coq--font-lock-vars '(font-lock-keywords
                             font-lock-keywords-only
                             font-lock-keywords-case-fold-search
                             font-lock-syntax-table
                             font-lock-syntactic-face-function)
  "Font-lock variables that influence fontification.")

(defun company-coq--fontify-buffer-with (&optional ref-buffer)
  "Fontify current buffer according to settings in REF-BUFFER."
  (setq ref-buffer (or ref-buffer
                       (when (buffer-live-p proof-script-buffer)
                         proof-script-buffer)
                       (current-buffer)))
  (cl-loop for var in company-coq--font-lock-vars
           do (set (make-local-variable var)
                   (buffer-local-value var ref-buffer)))
  (ignore-errors
    ;; Some modes, such as whitespace-mode, rely on buffer-local state to do
    ;; their fontification.  Thus copying only font-lock variables is not
    ;; enough; one would need to copy these modes private variables as well.
    ;; See GH-124.  FIXME we could just create a temporary Coq buffer at the
    ;; beginning of the session, and reuse it
    (font-lock-default-fontify-region (point-min) (point-max) nil)))

(defun company-coq--fontify-string (str &optional ref-buffer)
  "Fontify STR, using font-locking settings of REF-BUFFER."
  (with-temp-buffer
    (insert str)
    (company-coq--fontify-buffer-with ref-buffer)
    (buffer-string)))

(defface company-coq-inline-docs-face
  '((t :inherit region))
  "Default face for inline docs."
  :group 'company-coq-faces)

(defun company-coq--prepare-for-definition-overlay (strs offset &optional max-lines)
  "Prepare STRS for display as an inline documentation string.
Return value is a string that includes properties surrounding it
with two thin horizontal lines, indented by OFFSET, and truncted
to show at most MAX-LINES."
  (let* ((max-lines (or max-lines 8))
         (strs (mapcar #'company-coq-get-header strs))
         (script-buf (current-buffer)))
    (with-temp-buffer
      (cl-loop for str in strs
               do (insert str "\n"))
      (company-coq-truncate-buffer (point-min) max-lines " …")
      (company-coq--fontify-buffer-with script-buf)
      (let ((real-offset (max 0 (min offset (- (window-body-width) (company-coq-max-line-length) 5)))))
        (company-coq-prefix-all-lines (make-string real-offset ?\s)))
      (font-lock-append-text-property (point-min) (point-max) 'face 'default)
      (company-coq-insert-spacer (point-min))
      (company-coq-insert-spacer (point-max))
      (buffer-string))))

(defun company-coq--count-lines-under-point ()
  "Count number of lines beyond POINT."
  (save-excursion
    (let ((line-move-visual 1)
          (win-start (window-start nil))
          (win-height (window-body-height)))
      (cl-loop for available = win-height then (1- available)
               while (and (> (point) win-start))
               do (vertical-motion -1)
               finally return available))))

(defun company-coq-point-at-bovl ()
  "Return point that `beginning-of-visual-line' would jump to."
  (save-excursion
    (beginning-of-visual-line)
    (point)))

(defun company-coq--show-definition-overlay-at-point ()
  "Show inline definition of symbol at point."
  (let* ((sb-pos  (company-coq-symbol-at-point-with-pos)))
    (unless sb-pos (error "No symbol here"))
    (let* ((ins-pos (save-excursion (and (forward-line 1)
                                         (> (point-at-bol) (cdr sb-pos))
                                         (point-at-bol)))))
      (unless ins-pos (error "No newline at end of file"))
      (-if-let* ((docs (company-coq-doc-buffer-collect-outputs
                        (car sb-pos) (list company-coq-doc-cmd
                                           company-coq-tactic-def-cmd
                                           company-coq-def-cmd)
                        (list company-coq-type-cmd))))
          (let* ((offset (company-coq-text-width (company-coq-point-at-bovl) (cdr sb-pos)))
                 (max-h (max 4 (min 16 (- (company-coq--count-lines-under-point) 2))))
                 (ins-str (company-coq--prepare-for-definition-overlay docs offset max-h)))
            (setq company-coq-definition-overlay (make-overlay ins-pos ins-pos))
            (overlay-put company-coq-definition-overlay 'after-string ins-str))
        (company-coq--maybe-complain-docs-not-found t "information" (car sb-pos))))))

(defun company-coq-error-unless-feature-active (cc-feature)
  "Display an error, unless CC-FEATURE is enabled."
  (unless (company-coq-feature-active-p cc-feature)
    (user-error "The `%s' feature is disabled" cc-feature)))

(defun company-coq-toggle-definition-overlay ()
  "Toggle inline docs for symbol at point."
  (interactive)
  (company-coq-error-unless-feature-active 'inline-docs)
  (if company-coq-definition-overlay
      (company-coq-clear-definition-overlay)
    (company-coq--show-definition-overlay-at-point)
    (message (substitute-command-keys "Press \\[company-coq-toggle-definition-overlay] again to hide the inline docs."))))

(defun company-coq-show-definition-overlay-under-pointer (event)
  "Show inline definition for symbol under pointer.
EVENT is the mouse EVENT that triggered the call t this
function."
  (interactive "e")
  (company-coq-error-unless-feature-active 'inline-docs)
  (let* ((window  (posn-window (event-start event)))
         (buffer  (and window (window-buffer window))))
    (if buffer
        (with-current-buffer buffer
          (when (company-coq--proof-buffer-p)
            (save-excursion
              (mouse-set-point event)
              (company-coq-clear-definition-overlay)
              (company-coq--show-definition-overlay-at-point))))
      (mouse-set-point event))))

(defun company-coq-clear-definition-overlay ()
  "Clear inline definition popup."
  (interactive)
  (when company-coq-definition-overlay
    (delete-overlay company-coq-definition-overlay)
    (setq company-coq-definition-overlay nil)))

(defun company-coq-prover-init ()
  "Handle the prover init event, recording interesting information.
This function runs every time a new instance of the prover
starts.  It does basic capability detection and records known
tactic notations (thus ensuring that they are ignored in
subsequent invocations)."
  (setq company-coq--coqtop-patched-result 'unknown)
  (when (company-coq-prover-available-p)
    (company-coq-dbg "Doing early capability detection and filter initialization")
    (company-coq-detect-capabilities)
    (company-coq-tactic-initialize-notations-filter)))

(defconst company-coq--tutorial-tty-fonts-message
  "\n\n    (On TTYs, set ‘company-coq-features/prettify-symbols-in-terminals’ to t to enable prettification.)"
  "Message inserted in the tutorial on TTY terminals.")

(defconst company-coq--tutorial-buffer-name
  "*company-coq-tutorial*"
  "Name given to the company-coq tutorial buffer.")

;;;###autoload
(defun company-coq-tutorial ()
  "Open the company-coq tutorial, creating a new buffer if needed."
  (interactive)
  (let* ((tutorial-name   company-coq--tutorial-buffer-name)
         (tutorial-buffer (get-buffer tutorial-name))
         (tutorial-path   (expand-file-name "tutorial.v" company-coq-refman-path)))
    (with-current-buffer (get-buffer-create tutorial-name)
      (unless tutorial-buffer
        (insert-file-contents tutorial-path nil nil nil t)
        (when (search-forward "{% TTY-FONTS-MESSAGE %}" nil t)
          (replace-match (if (display-graphic-p) ""
                           company-coq--tutorial-tty-fonts-message)
                         t t)
          (when (functionp fill-paragraph-function)
            ;; Aquamacs overrides fill-paragraph
            (funcall fill-paragraph-function)))
        (goto-char (point-min))
        (coq-mode)
        (company-coq-mode)
        (company-coq--setup-secondary-buffer)
        (setq-local proof-script-fly-past-comments nil))
      (pop-to-buffer-same-window (current-buffer)))))

(defun company-coq-get-comment-opener (pos)
  "Read comment opener at position POS."
  (when pos
    (ignore-errors
      (save-excursion
        (goto-char pos)
        (buffer-substring (point) (progn (skip-chars-forward "(*!+" (+ 5 (point))) (1+ (point))))))))

(defun company-coq-syntactic-face-function (state)
  "Determine which face to use based on parsing state STATE."
  (pcase-let ((`(_ _ _ ,in-string ,comment-depth _ _ _ ,comment-opener-pos . ,_) state))
    (cond
     (in-string font-lock-string-face)
     ((or comment-depth (numberp comment-depth))
      (let* ((comment-opener (company-coq-get-comment-opener comment-opener-pos))
             (matches        (lambda (pattern) (string-match-p (concat "\\`" (regexp-quote pattern)) comment-opener))))
        (cond
         ((funcall matches "(*!")   'company-coq-comment-h3-face)
         ((funcall matches "(*+")   'company-coq-comment-h2-face)
         ((funcall matches "(*** ") 'company-coq-comment-h1-face)
         ((funcall matches "(**")   font-lock-doc-face)
         (t        font-lock-comment-face)))))))

(defun company-coq-fill-nobreak-predicate ()
  "Check if paragraph surrounding point may be filled."
  (not (memq (get-text-property (point) 'face) '(font-lock-doc-face font-lock-comment-face))))

(eval-and-compile
  (defun company-coq-feature-toggle-function (feature-symbol)
    "Return symbol of toggle function for feature FEATURE-SYMBOL."
    (intern (format "company-coq-features/%s" (symbol-name feature-symbol)))))

(defmacro company-coq-do-in-coq-buffers (&rest body)
  "Run BODY in all `coq-mode' buffers."
  (declare (indent defun)
           (debug t))
  `(dolist (company-coq-do-in-coq-buffers--buffer (buffer-list))
     (with-current-buffer company-coq-do-in-coq-buffers--buffer
       (when (company-coq-coq-mode-p)
         ,@body))))

(defmacro company-coq-do-in-goals-buffer (&rest body)
  "Run BODY in goals buffer, if available."
  (declare (indent defun)
           (debug t))
  `(company-coq-with-current-buffer-maybe proof-goals-buffer
     ,@body))

(defmacro company-coq-do-in-response-buffer (&rest body)
  "Run BODY in response buffer, if available."
  (declare (indent defun)
           (debug t))
  `(company-coq-with-current-buffer-maybe proof-response-buffer
     ,@body))

(defmacro company-coq-do-in-all-buffers (&rest body)
  "Run BODY in all Coq-related buffers."
  (declare (indent defun)
           (debug t))
  `(progn
     (company-coq-do-in-coq-buffers ,@body)
     (company-coq-do-in-goals-buffer ,@body)
     (company-coq-do-in-response-buffer ,@body)))

(defvar-local company-coq-mode nil
  "Non-nil if company-coq-mode is enabled.
Use the command `company-coq-mode' to change this variable.")

(eval-and-compile
  (defvar company-coq-available-features nil
    "Alist of available company-coq features, with documentation.

Each entry of this list must be a cons (name . description).
Each name, once fed to `company-coq-feature-toggle-function',
must correspond to a function taking one argument and indicating
whether to turn the feature on or off (see `define-minor-mode').

This alist is populated as a side effect of
`company-coq-define-feature'.")

  (defun company-coq-disabled-features--custom-type-docstring (doc)
    "Format DOC as the docstring of one of company-coq features.
Proactively calls `substitute-command-keys', as the later call
made by customize when constructing the documentation buffer
would otherwise remove text properties on docstrings requiring
changes."
    (let* ((lines (split-string (substitute-command-keys doc) "\n" t))
           (indent (make-string 5 32)))
      (concat (propertize (car lines) 'face '(:weight bold)) "\n"
              (mapconcat (lambda (line)
                           (concat indent (propertize line 'face '(:height 0.9))))
                         (cdr lines) "\n"))))

  (defun company-coq-disabled-features--custom-type ()
    "Compute a :type for company-coq-disabled-features."
    `(set ,@(cl-loop for (feature . description) in company-coq-available-features
                     collect `(const :tag ,(company-coq-disabled-features--custom-type-docstring description)
                                     ,feature))))

  (defun company-coq-disabled-features--update-type ()
    "Update the custom :type of company-coq-disabled-features."
    (put 'company-coq-disabled-features 'custom-type
         (company-coq-disabled-features--custom-type))))

(defun company-coq--set-disabled-features (symbol value)
  "Set SYMBOL to VALUE, toggling company-coq features as needed."
  ;; First check that the whole file has been loaded; if not, this call comes
  ;; from the defcustom form at load time, and it should not do anything fancy
  (when (featurep 'company-coq)
    (when (eq symbol 'company-coq-disabled-features)
      (let* ((previously-disabled (company-coq-value-or-nil 'company-coq-disabled-features))
             (newly-disabled (cl-set-difference value previously-disabled))
             (newly-enabled (cl-set-difference previously-disabled value)))
        (company-coq-do-in-coq-buffers
          (company-coq-toggle-features newly-disabled nil)
          (company-coq-toggle-features newly-enabled t)))))
  (set-default symbol value))

(defcustom company-coq-disabled-features nil
  "List of disabled company-coq features.

The list of all available features is in
`company-coq-available-features'.  Use
`company-coq-describe-feature' to get help about one of these
features.

Some of these features are experimental; use
`company-coq-live-on-the-edge' to enable them anyhow.

Editing this variable through the customize interface applies
changes immediately.  From Lisp code, make sure to set this
variable before enabling `company-coq-mode', or set it
using `customize-set-variable'.

Technical note: The `:type' of this defcustom is recomputed every
time a new feature is added."
  :group 'company-coq
  :set #'company-coq--set-disabled-features
  :type (company-coq-disabled-features--custom-type))

(defcustom company-coq-live-on-the-edge nil
  "Whether to enable experimental features of company-coq.
See also `company-coq-disabled-features'."
  :group 'company-coq
  :type 'boolean)

(defun company-coq-feature-active-p (feature)
  "Check if company-coq feature FEATURE is active."
  (let ((toggle-function (company-coq-feature-toggle-function feature)))
    (and (get toggle-function 'company-coq-feature-active)
         (or (not (get toggle-function 'company-coq-feature-experimental))
             company-coq-live-on-the-edge)
         (or (not (get toggle-function 'company-coq-feature-requires-patched-coqtop))
             (company-coq--coqtop-patched-p)))))

(eval-and-compile
  (defconst company-coq-define-feature-doc-format
    "Toggle the %s feature.

With a prefix argument ARG, enable the feature if ARG is positive, and
disable it otherwise.  If called from Lisp, enable the feature if
ARG is omitted or nil, and toggle it if ARG is `toggle'.

To persistently disable a feature, use
`company-coq-disabled-features'.

Documentation for this feature:
%s"))

(defmacro company-coq-define-feature (symbol args doc &rest body)
  "Define company-coq feature SYMBOL.

In particular, define a toggle function taking one argument
ARG (the first element of ARGS, which must be a singleton list).
ARG may be 'on, or 'off; this is the new status of the mode.  The
documentation of the function is constructed from DOC.  The body
of the function is BODY.

Defining a feature adds it to `company-coq-available-features'."
  (declare (indent defun)
           (debug (&define symbolp lambda-list stringp def-body)))
  (let* ((toggle-function (company-coq-feature-toggle-function symbol))
         (docs (format company-coq-define-feature-doc-format (symbol-name symbol) doc))
         (arg (car args)))
    (unless (equal 1 (length args))
      (error "Features take a single argument"))
    `(progn
       ;; No need to set `company-coq-feature-active' here; in fact, setting it would cause
       ;; reloading this file to deactivate all active features.
       ;;
       ;; Register this feature
       (add-to-list 'company-coq-available-features (cons ',symbol ,doc) t)
       (company-coq-disabled-features--update-type)
       ;; Define the actual function
       (defun ,toggle-function (,arg)
         ,docs
         (interactive (or current-prefix-arg '(toggle)))
         (cond
          ((eq ,arg 'toggle)
           (,toggle-function (if (company-coq-feature-active-p ',symbol) 'off 'on)))
          ((or (eq ,arg 'on) (and (numberp arg) (> ,arg 0)))
           (setq ,arg 'on)
           (unless (company-coq-value-or-nil 'company-coq-mode)
             (user-error "%s depends on `company-coq-mode'" ,(symbol-name symbol)))
           (put ',toggle-function 'company-coq-feature-active t))
          ((or (eq ,arg 'off) (and (numberp arg) (<= ,arg 0)))
           (setq ,arg 'off)
           (put ',toggle-function 'company-coq-feature-active nil)))
         (prog1 (progn ,@body)
           (when (called-interactively-p 'interactive)
             (message "Feature %s %s" ,(symbol-name symbol) (if (company-coq-feature-active-p ',symbol) "activated" "deactivated"))))))))

(defvar company-coq--refontification-requested nil
  "Whether a refontification is needed, due to feature changes.")

(defvar-local company-coq--refontification-delayed nil
  "Whether `company-coq-request-refontification' should delay refontifications.")

(defun company-coq-request-refontification ()
  "Request a refontification of the buffer."
  (if company-coq--refontification-delayed
      (setq-local company-coq--refontification-requested t)
    ;; Toggling a single feature does not delay refontification
    (company-coq-fontify-buffer)))

(defun company-coq--perform-requested-refontification ()
  "Refontify the buffer, if requested."
  (when company-coq--refontification-requested
    (setq-local company-coq--refontification-requested nil)
    (company-coq-fontify-buffer)))

(defmacro company-coq-with-delayed-refontification (&rest body)
  "Run BODY, grouping all refontifications at the end."
  (declare (indent defun)
           (debug t))
  `(progn
     (setq company-coq--refontification-delayed t)
     (prog1 (progn ,@body)
       (company-coq-do-in-all-buffers (company-coq--perform-requested-refontification))
       (setq company-coq--refontification-delayed nil))))

(defun company-coq-toggle-features (enabled-or-disabled-features status)
  "Enable or disable ENABLED-OR-DISABLED-FEATURES.
If STATUS is non-nil, enable each feature in
ENABLED-OR-DISABLED-FEATURES.  Otherwise, disable them."
  (company-coq-with-delayed-refontification
    (dolist (feature enabled-or-disabled-features)
      (let ((toggle-func (company-coq-feature-toggle-function feature)))
        (funcall toggle-func (if status 1 -1))))))

(defun company-coq-read-feature (verb)
  "Read a feature name with VERB from the user."
  (list (intern (completing-read (format "Feature to %s? " verb)
                                 (mapcar #'car company-coq-available-features) nil t))))

;;;###autoload
(defun company-coq-describe-feature (feature)
  "Describe company-coq feature FEATURE."
  (interactive (company-coq-read-feature "describe"))
  (describe-function (company-coq-feature-toggle-function feature)))

(defun company-coq-toggle-feature (feature)
  "Toggle company-coq feature FEATURE.
Interactively, prompt for FEATURE."
  (interactive (company-coq-read-feature "toggle"))
  (call-interactively (company-coq-feature-toggle-function feature)))

(defun company-coq-add-backend (backend)
  "Add BACKEND to `company-coq-enabled-backends'."
  (company-coq-set-backends (cons backend company-coq-enabled-backends)))

(defun company-coq-remove-backend (backend)
  "Remove BACKEND from `company-coq-enabled-backends'."
  (company-coq-set-backends (remove backend company-coq-enabled-backends)))

(defun company-coq--init-pg ()
  "Require the right PG modules.
Since PG displays a welcome screen when `require'd, we must delay
loading as much as possible."
  (with-no-warnings (proof-ready-for-assistant 'coq)) ;; Required by proof-shell
  (require 'pg-vars)      ;; `proof-shell-proof-completed'
  (require 'pg-user)      ;; `proof-goto-point'
  (require 'proof-shell)  ;; `proof-shell-available-p'
  (require 'proof-config) ;; `proof-fly-past-comments'
  (require 'proof-script) ;; `proof-unprocessed-begin'
  (require 'coq-syntax)   ;; `coq-tactics-db'
  (require 'coq-indent)   ;; `coq-looking-at-comment'
  (require 'coq))         ;; `coq-insert-match'

(defconst company-coq--input-hooks '(proof-assert-command-hook
                          proof-shell-insert-hook)
  "Hooks that denote user input.")

(defun company-coq--listen-for-input (handler)
  "Register HANDLER to be called when input is sent to the prover."
  (mapc (lambda (hook) (add-hook hook handler)) company-coq--input-hooks))

(defun company-coq--unlisten-for-input (handler)
  "Unregister HANDLER to be called when input is sent to the prover."
  (mapc (lambda (hook) (add-hook hook handler)) company-coq--input-hooks))

(defconst company-coq--output-hooks '(proof-shell-handle-delayed-output-hook
                           proof-shell-handle-error-or-interrupt-hook)
  "Hooks that denote prover output.")

(defun company-coq--listen-for-output (handler)
  "Register HANDLER to be called when output is sent by the prover."
  (mapc (lambda (hook) (add-hook hook handler)) company-coq--output-hooks))

(defun company-coq--unlisten-for-output (handler)
  "Unregister HANDLER to be called when output is sent by the prover."
  (mapc (lambda (hook) (add-hook hook handler)) company-coq--output-hooks))

(company-coq-define-feature core (arg)
  "Core components.
Do not disable this feature"
  (pcase arg
    (`on
     (company-coq--init-pg)
     (company-coq--record-selected-window)
     (company-coq-do-in-coq-buffers (yas-minor-mode))
     (add-hook 'post-command-hook #'company-coq--record-selected-window)
     (add-hook 'proof-shell-init-hook #'company-coq-prover-init)
     (add-hook 'proof-state-change-hook #'company-coq-state-change)
     (add-hook 'proof-shell-insert-hook #'company-coq-maybe-proof-input-reload-things)
     (add-hook 'proof-shell-handle-delayed-output-hook #'company-coq-maybe-proof-output-reload-things)
     (add-hook 'proof-shell-handle-error-or-interrupt-hook #'company-coq--update-context)
     (add-hook 'yas-after-exit-snippet-hook #'company-coq-forget-choices))
    (`off
     (company-coq-do-in-coq-buffers (yas-minor-mode -1))
     (remove-hook 'post-command-hook #'company-coq--record-selected-window)
     (remove-hook 'proof-shell-init-hook #'company-coq-prover-init)
     (remove-hook 'proof-state-change-hook #'company-coq-state-change)
     (remove-hook 'proof-shell-insert-hook #'company-coq-maybe-proof-input-reload-things)
     (remove-hook 'proof-shell-handle-delayed-output-hook #'company-coq-maybe-proof-output-reload-things)
     (remove-hook 'proof-shell-handle-error-or-interrupt-hook #'company-coq--update-context)
     (remove-hook 'yas-after-exit-snippet-hook #'company-coq-forget-choices))))

(defun company-coq--add-auxiliary-buffers-hook (hook &optional append local)
  "Add HOOK to `coq-response-mode-hook' and `coq-goals-mode-hook'.
APPEND and LOCAL are as in `add-hook'."
  (add-hook 'coq-response-mode-hook hook append local)
  (add-hook 'coq-goals-mode-hook hook append local))

(defun company-coq--remove-auxiliary-buffers-hook (hook &optional local)
  "Remove HOOK from `coq-response-mode-hook' and `coq-goals-mode-hook'.
LOCAL is as in `add-hook'."
  (remove-hook 'coq-response-mode-hook hook local)
  (remove-hook 'coq-goals-mode-hook hook local))

(defun company-coq--hello ()
  "Show a company-coq–related greeting."
  (message "%s" (substitute-command-keys "Welcome to company-coq! Use \\[company-coq-tutorial] to get started.")))

(company-coq-define-feature hello (arg)
  "Startup message.
Shows a greeting when company-coq starts."
  (pcase arg
    (`on
     (when (and company-coq-mode (buffer-name) (not (string-match-p "\\` ?\\*" (buffer-name))))
       (run-with-timer 0 nil #'company-coq--hello)))))

(defun company-coq-features/keybindings--enable ()
  "Enable company-coq keybindings in current buffer."
  (company-coq--keybindings-minor-mode))

(defun company-coq-features/keybindings--disable ()
  "Disable company-coq keybindings in current buffer."
  (company-coq--keybindings-minor-mode -1))

(company-coq-define-feature keybindings (arg)
  "Company-Coq keybindings.
Activates `company-coq-map', a keymap containing many shortcuts
to commonly used company-coq features."
  (pcase arg
    (`on
     (company-coq-do-in-all-buffers (company-coq-features/keybindings--enable))
     (company-coq--add-auxiliary-buffers-hook #'company-coq-features/keybindings--enable))
    (`off
     (company-coq-do-in-all-buffers (company-coq-features/keybindings--disable))
     (company-coq--remove-auxiliary-buffers-hook #'company-coq-features/keybindings--enable))))

(company-coq-define-feature inline-docs (arg)
  "Inline documentation popups.
Lets you display documentation for most theorems, tactics and
types using <C-click> or <menu>."
  (pcase arg
    (`off (company-coq-do-in-coq-buffers (company-coq-clear-definition-overlay)))))

(defcustom company-coq-features/prettify-symbols-in-terminals nil
  "If set, set up prettification in TTY frames as well."
  :group 'company-coq
  :type 'boolean)

(defun company-coq-features/prettify-symbols--enable-1 (ref-buffer)
  "Set up prettify-symbols in the current buffer.
REF-BUFFER is used to retrieve the buffer-local values of
`prettify-symbols-alist' etc."
  (when (boundp 'prettify-symbols-alist)
    (setq-local prettify-symbols-alist
                (with-current-buffer ref-buffer
                  (-distinct (append company-coq-local-symbols
                                     company-coq-dir-local-symbols
                                     company-coq-prettify-symbols-alist
                                     prettify-symbols-alist)))))
  (when (and (or (display-graphic-p) company-coq-features/prettify-symbols-in-terminals)
             (fboundp #'prettify-symbols-mode))
    (company-coq-suppress-warnings
      ;; Must explicitly turn off prettify-symbols-mode; otherwise its gets
      ;; turned on twice, so its keywords get added twice. This is a bug in
      ;; `prettify-symbols-mode'
      (prettify-symbols-mode -1)
      (prettify-symbols-mode))))

(defun company-coq-features/prettify-symbols--same-ish-syntax (other ref)
  "Check if the syntax class of OTHER is similar to that of REF."
  (memq (char-syntax (or other ?\s))
        (if (memq (char-syntax ref) '(?w ?_))
            '(?w ?_)
          '(?. ?\\))))

(defun company-coq-features/prettify-symbols--predicate-1 (pos)
  "Check if POS should be prettified."
  (save-excursion
    (goto-char pos)
    (let ((pp (syntax-ppss)))
      (or (company-coq--in-code-p-1 pp)
          (company-coq--in-notation-string-1 pp)))))

(defun company-coq-features/prettify-symbols--predicate (start end &optional _match)
  "Decide whether START..END should be prettified.
Differs from `prettify-symbols-default-compose-p' insofar as it
allows composition in “Notation” strings, and in code comments.
Only effective in Emacs 25."
  (interactive "r")
  (and (not (company-coq-features/prettify-symbols--same-ish-syntax
             (char-before start) (char-after start)))
       (not (company-coq-features/prettify-symbols--same-ish-syntax
             (char-after end) (char-before end)))
       ;; Test both endpoints, since both sides of the ‘*’ of comments are not
       ;; in comments themselves
       (company-coq-features/prettify-symbols--predicate-1 start)
       (company-coq-features/prettify-symbols--predicate-1 end)))

(defun company-coq-features/prettify-symbols--enable-script ()
  "Set up prettify-symbols in the current (scripting) buffer."
  (when (boundp 'prettify-symbols-compose-predicate)
    (setq-local prettify-symbols-compose-predicate
                #'company-coq-features/prettify-symbols--predicate))
  (company-coq-features/prettify-symbols--enable-1 (current-buffer)))

(defun company-coq-features/prettify-symbols--enable-other ()
  "Set up prettify-symbols in the current (goals or response) buffer."
  (company-coq-features/prettify-symbols--enable-1 (if (buffer-live-p proof-script-buffer)
                                            proof-script-buffer
                                          (current-buffer))))

(defun company-coq-features/prettify-symbols--enable-others ()
  "Enable prettify-symbols in response and goals buffers."
  (company-coq-do-in-goals-buffer (company-coq-features/prettify-symbols--enable-other))
  (company-coq-do-in-response-buffer (company-coq-features/prettify-symbols--enable-other))
  (company-coq--add-auxiliary-buffers-hook #'company-coq-features/prettify-symbols--enable-other))

(defun company-coq-features/prettify-symbols--enable ()
  "Enable prettify-symbols in all Coq buffers."
  (company-coq-do-in-coq-buffers (company-coq-features/prettify-symbols--enable-script))
  (company-coq-features/prettify-symbols--enable-others))

(defun company-coq-features/prettify-symbols--disable ()
  "Disable prettify-symbols in all Coq buffers."
  (when (fboundp #'prettify-symbols-mode)
    (company-coq-suppress-warnings
      (company-coq-do-in-all-buffers (prettify-symbols-mode -1))
      (company-coq--remove-auxiliary-buffers-hook #'company-coq-features/prettify-symbols--enable-other))))

(defun company-coq-features/prettify-symbols--update-table ()
  "Update table of prettification symbols from file-local vars."
  (when (or (assoc 'company-coq-local-symbols file-local-variables-alist)
            (assoc 'company-coq-dir-local-symbols dir-local-variables-alist))
    (company-coq-features/prettify-symbols--enable)))

(company-coq-define-feature prettify-symbols (arg)
  "Pretty math symbols (e.g. `forall' → `∀').
Transparently prettifies math symbols, using unicode characters
for display (the buffer contents are not modified, though).
(requires emacs 24.4 or later)"
  (pcase arg
    (`on
     (company-coq-features/prettify-symbols--enable)
     (add-hook 'hack-local-variables-hook #'company-coq-features/prettify-symbols--update-table)
     (add-hook 'proof-activate-scripting-hook #'company-coq-features/prettify-symbols--enable-others))
    (`off
     (company-coq-features/prettify-symbols--disable)
     (remove-hook 'hack-local-variables-hook #'company-coq-features/prettify-symbols--update-table)
     (remove-hook 'proof-activate-scripting-hook #'company-coq-features/prettify-symbols--enable-others))))

(defface company-coq-features/smart-subscripts-face
  '((t :height 1.0))
  "Face used to display subscripts."
  :group 'company-coq-faces)

(defun company-coq-features/smart-subscripts--compute-spec (spec)
  "Compute font-locking spec for subscript at point, using SPEC.
Returns an empty spec in comments (but not in code blocks in
comments).  Also returns an empty spec on non-graphic displays."
  `(face ,@(if (and (company-coq-not-in-comment-text-or-string-p)
                    (display-graphic-p))
               spec
             '(nil))))

(defun company-coq-features/smart-subscripts--subscript-spec ()
  "Compute font-locking spec for subscript at point."
  (company-coq-features/smart-subscripts--compute-spec
   '(company-coq-features/smart-subscripts-face display (raise -0.25))))

(defun company-coq-features/smart-subscripts--separator-spec ()
  "Compute font-locking spec for subscript separator at point."
  (company-coq-features/smart-subscripts--compute-spec
   '(nil invisible company-coq-features/smart-subscripts)))

(defconst company-coq-features/smart-subscripts--spec
  ;; Works because '.' isn't part of symbols
  `((,(concat "\\_<" company-coq-symbol-regexp-no-dots-no-numbers "\\(_*[0-9]+\\)'*\\_>")
     (1 (company-coq-features/smart-subscripts--subscript-spec) append))
    ;; (,(concat "\\_<" company-coq-symbol-regexp-no-dots "\\(''\\)\\([0-9a-zA-Z]+\\)'*\\_>")
    ;;  (1 (company-coq-features/smart-subscripts--separator-spec) prepend)
    ;;  (2 (company-coq-features/smart-subscripts--supscript-spec) append))
    (,(concat "\\_<" company-coq-symbol-regexp-no-dots "\\(__\\)\\([a-zA-Zα-ωΑ-Ω][0-9a-zA-Zα-ωΑ-Ω]*\\)'*\\_>")
     (1 (company-coq-features/smart-subscripts--separator-spec) prepend)
     (2 (company-coq-features/smart-subscripts--subscript-spec) append)))
  "Font-lock spec for subscripts in proof script.")

(defun company-coq-features/smart-subscripts--sep-bounds (&optional point)
  "Compute bounds of subscript marker around POINT, if any.
Also see `company-coq-features/smart-subscripts--reveal-overlay'."
  (unless point
    (setq point (point)))
  (let ((before (char-before point))
        (after (char-after point)))
    (cond
     ((and (eq before ?_) (eq after ?_))
      (cons (1- point) (1+ point)))
     ((and (eq before ?_) (eq (char-before (1- point)) ?_))
      (cons (- point 2) point))
     ((and (eq after ?_) (eq (char-after (1+ point)) ?_))
      (cons point (+ point 2))))))

(defvar-local company-coq-features/smart-subscripts--reveal-overlay nil
  "Saved bounds of subscript marker.")

(defun company-coq-features/smart-subscripts--reveal ()
  "Ensure that subscript marker at point is visible.
Subscript markers are double underscores (“__”) that separate an
identifier and a subscript."
  ;; prettify-symbols-unprettify-at-point uses text properties to achieve an
  ;; effect similar to this, but that forces it to fight against
  ;; font-locking. Using an overlay is simpler and works in our case. The only
  ;; tricky part is when “__” is changed to “_a_”. In that case we delete the
  ;; overlay, and the command loop adjusts the point (Bug #22761)
  (unless (overlayp company-coq-features/smart-subscripts--reveal-overlay)
    (let ((ov (make-overlay 0 0 nil t)))
      (overlay-put ov 'invisible 'company-coq-features/smart-subscripts--off)
      (setq company-coq-features/smart-subscripts--reveal-overlay ov)))
  ;; Inhibit point motion if point is was revealed
  (when (eq (get-char-property (point) 'invisible)
            'company-coq-features/smart-subscripts--off)
    ;; This is needed in the case where “__” is changed to “_a_”, since in that
    ;; case the overlay is deleted and not recreated, causing the point to be
    ;; adjusted at the end of command loop
    (setq disable-point-adjustment t))
  ;; Hide previous marker
  (delete-overlay company-coq-features/smart-subscripts--reveal-overlay)
  ;; Reveal current marker
  (-when-let* ((bounds (company-coq-features/smart-subscripts--sep-bounds)))
    (move-overlay company-coq-features/smart-subscripts--reveal-overlay
                  (car bounds) (cdr bounds))))

(defun company-coq-features/smart-subscripts--enable ()
  "Enable subscript prettification in current buffer."
  (font-lock-add-keywords nil company-coq-features/smart-subscripts--spec 'add)
  (add-to-invisibility-spec 'company-coq-features/smart-subscripts)
  (add-hook 'post-command-hook #'company-coq-features/smart-subscripts--reveal nil t)
  ;; hideshow and outline use overlays, so won't be confused by this:
  (make-local-variable 'font-lock-extra-managed-props)
  (add-to-list 'font-lock-extra-managed-props 'display)
  (add-to-list 'font-lock-extra-managed-props 'invisible)
  (company-coq-request-refontification))

(defun company-coq-features/smart-subscripts--disable ()
  "Disable subscript prettification in current buffer."
  (font-lock-remove-keywords nil company-coq-features/smart-subscripts--spec)
  (remove-hook 'post-command-hook #'company-coq-features/smart-subscripts--reveal t)
  (kill-local-variable 'company-coq-features/smart-subscripts--reveal-overlay)
  (remove-from-invisibility-spec 'company-coq-features/smart-subscripts)
  (company-coq-request-refontification))

(company-coq-define-feature smart-subscripts (arg)
  "Smart subscripts: a1 → a₁ and a__n → aₙ.
Transparently displays subscripts."
  (pcase arg
    (`on
     (company-coq-do-in-all-buffers (company-coq-features/smart-subscripts--enable))
     (company-coq--add-auxiliary-buffers-hook #'company-coq-features/smart-subscripts--enable))
    (`off
     (company-coq-do-in-all-buffers (company-coq-features/smart-subscripts--disable))
     (company-coq--remove-auxiliary-buffers-hook #'company-coq-features/smart-subscripts--enable))))

(company-coq-define-feature snippets (arg)
  "Snippets for various common Coq forms.
Enables keybindings and completion for common Coq patterns, such
as branches of a [match goal] construct. Custom patterns can be
added to `company-coq-custom-snippets'."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-user-snippets-backend))
    (`off (company-coq-remove-backend #'company-coq-user-snippets-backend))))

(defcustom company-coq-goal-line-character (if (display-graphic-p) ?\s ?─)
  "Character used to display the goal line.
Set to a space by default on graphical displays; the line is
emulated using a :strike-through property (set as part of
`company-coq-goal-line-face').  That doesn't work on TTYs, so we
use a box character there.  Suggested values: `═' or `─'."
  :group 'company-coq
  :type '(character))

(defface company-coq-goal-line-face
  '((((type tty)) ())
    (t (:strike-through t)))
  "Face used to highlight the goal line.
This face is made to inherit the height of the default face,
every time it is used, to prevent the face-remapping-alist from
wrapping the line."
  :group 'company-coq-faces)

(defface company-coq-goal-line-space-face
  '((t ()))
  "Face used to spaces before the goal line."
  :group 'company-coq-faces)

(defun company-coq-features/pg-improvements--goals-buffer-enable ()
  "Apply company-coq improvements to current buffer."
  (font-lock-add-keywords nil company-coq-goal-separator-spec t)
  (add-to-list (make-local-variable 'font-lock-extra-managed-props) 'display)
  (setq-local show-trailing-whitespace nil)
  (company-coq-request-refontification))

(defun company-coq-features/pg-improvements--goals-buffer-disable ()
  "Remove company-coq improvements from current buffer."
  (font-lock-remove-keywords nil company-coq-goal-separator-spec)
  (kill-local-variable 'show-trailing-whitespace)
  (company-coq-request-refontification))

(defun company-coq-features/pg-improvements--response-buffer-enable ()
  "Apply company-coq improvements to current buffer."
  (visual-line-mode))

(defun company-coq-features/pg-improvements--response-buffer-disable ()
  "Remove company-coq improvements from current buffer."
  (visual-line-mode -1))

(defconst company-coq-features/pg-improvements--font-lock-extras
  '(("\\_<pose proof\\_>" 0 'proof-tactics-name-face prepend)
    ("\\(?:\\W\\|\\`\\)\\(@\\)\\_<" 1 'font-lock-constant-face append)
    ("\\(?:\\W\\|\\`\\)\\(\\?\\(?:\\s_\\|\\sw\\)+\\)\\_>" 1 'font-lock-variable-name-face append))
  "Additional font-lock specs for the main buffer.")

(defun company-coq-features/pg-improvements--main-buffer-enable ()
  "Apply company-coq improvements to (current) main buffer."
  (show-paren-mode)
  (font-lock-add-keywords nil company-coq-features/pg-improvements--font-lock-extras 'add)
  (add-to-list (make-local-variable 'font-lock-extra-managed-props) 'help-echo)
  (setq-local fill-nobreak-predicate #'company-coq-fill-nobreak-predicate)
  (setq-local help-at-pt-display-when-idle t)
  (help-at-pt-set-timer)
  (company-coq-request-refontification))

(defun company-coq-features/pg-improvements--main-buffer-disable ()
  "Remove company-coq improvements from (current) main buffer."
  (show-paren-mode -1)
  (font-lock-remove-keywords nil company-coq-features/pg-improvements--font-lock-extras)
  (kill-local-variable 'fill-nobreak-predicate)
  (kill-local-variable 'help-at-pt-display-when-idle)
  (help-at-pt-cancel-timer)
  (company-coq-request-refontification))

(company-coq-define-feature pg-improvements (arg)
  "Discrete improvements to Proof General.
Prettifies the goals line, adds a few missing highlighting
patterns, etc."
  (pcase arg
    (`on
     (company-coq-do-in-coq-buffers (company-coq-features/pg-improvements--main-buffer-enable))
     (company-coq-do-in-response-buffer (company-coq-features/pg-improvements--response-buffer-enable))
     (company-coq-do-in-goals-buffer (company-coq-features/pg-improvements--goals-buffer-enable))
     (add-hook 'coq-goals-mode-hook #'company-coq-features/pg-improvements--goals-buffer-enable)
     (add-hook 'coq-response-mode-hook #'company-coq-features/pg-improvements--response-buffer-enable))
    (`off
     (company-coq-do-in-coq-buffers (company-coq-features/pg-improvements--main-buffer-disable))
     (company-coq-do-in-response-buffer (company-coq-features/pg-improvements--response-buffer-disable))
     (company-coq-do-in-goals-buffer (company-coq-features/pg-improvements--goals-buffer-disable))
     (remove-hook 'coq-goals-mode-hook #'company-coq-features/pg-improvements--goals-buffer-enable)
     (remove-hook 'coq-response-mode-hook #'company-coq-features/pg-improvements--response-buffer-enable))))

(defun company-coq-features/show-key--populate (entries table)
  "Load ENTRIES into TABLE.
ENTRIES is a list of (category latex-string symbol string?)
lists.  TABLE is a hashtable."
  (dolist (entry entries)
    (pcase entry
      ((or `(,_ ,latex ,symbol)           ; ("arrow" "\\mapsto" #X21A6)
           `(,_ ,latex ,symbol ,_)        ; ("mathrel" "\\searrow" 8600 "↘")
           `(,_ ,_ ,latex ,symbol ,_)     ; ("fourier" "mathrel" "\\leqslant" 10877 "⩽")
           `(,_ ,_ ,latex ,symbol ,_ ,_)) ; ("amssymb" "mathord" "\\blacksquare" 11035 "⬛" t)
       (when (eq (aref latex 0) ?\\) ;; Exclude ("literal" "mathalpha" "i" 105 "i" t)
         (puthash symbol (cons latex (gethash symbol table)) table))))))

(defconst company-coq-features/show-key--table
  (let ((table (make-hash-table :size 4096)))
    (company-coq-features/show-key--populate math-symbol-list-basic table)
    (company-coq-features/show-key--populate math-symbol-list-extended table)
    (company-coq-features/show-key--populate (bound-and-true-p math-symbol-list-packages) table)
    table)
  "Table of (symbol → latex-string) mappings.")

(defun company-coq-features/show-key--wrap (str)
  "Explain how to invoke company-math on STR.
That is, wrap STR in “‘’ RET” or “‘’ \\[company-manual-begin]
RET”, and substitute command keys."
  (substitute-command-keys
   (format (if (> (length str) 3)
               "‘%s RET’"
             "‘%s \\[company-manual-begin] RET’")
           str)))

(defun company-coq-features/show-key--echo-1 (char)
  "Find ways to input CHAR with `company-coq-math-symbols-backend'."
  ;; Test on ‘∈’, ‘⊕’, ‘β’, and ‘∅’
  (when (> char 128)
    (let ((input-strings (-uniq (gethash char company-coq-features/show-key--table))))
      (cond
       ((cddr input-strings)
        (concat (mapconcat #'company-coq-features/show-key--wrap (butlast input-strings) ", ")
                ", or " (company-coq-features/show-key--wrap (car (last input-strings)))))
       ((cdr input-strings)
        (concat (company-coq-features/show-key--wrap (car input-strings))
                " or " (company-coq-features/show-key--wrap (cadr input-strings))))
       ((car input-strings)
        (company-coq-features/show-key--wrap (car input-strings)))))))

(defun company-coq--composition-bounds (pos)
  "Compute bounds of composition at POS."
  (when (get-text-property pos 'composition)
    (cons (previous-single-char-property-change (1+ pos) 'composition nil (point-at-bol))
          (next-single-char-property-change pos 'composition nil (point-at-eol)))))

(defun company-coq-features/show-key--echo ()
  "Show a message describing how to input the symbol at point."
  (interactive)
  (when (company-coq--proof-buffer-p)
    (let ((message-log-max nil)) ;; Don't record messages
      (-if-let* ((char (char-after (point)))
                 (desc (company-coq-features/show-key--echo-1 char)))
          (-> "To input `%s', type %s."
              (format (char-to-string char) desc)
              (substitute-command-keys)
              (message))
        (-when-let* (((beg . end) (company-coq--composition-bounds (point))))
          (-> "`%s' is a prettified version of `%s'."
              (format (buffer-substring beg end) (buffer-substring-no-properties beg end))
              (message)))))))

(defvar company-coq-features/show-key--timer nil
  "Timer calling `company-coq-features/show-key--echo'.")

(company-coq-define-feature show-key (arg)
  "Tips on inputting special characters.
Shows a message in the echo area when the cursor is on a special
character."
  (pcase arg
    (`on
     (unless company-coq-features/show-key--timer
       (setq company-coq-features/show-key--timer
             (run-with-idle-timer 0.2 t #'company-coq-features/show-key--echo))))
    (`off
     (when company-coq-features/show-key--timer
       (cancel-timer company-coq-features/show-key--timer)))))

(company-coq-define-feature title-comments (arg)
  "Special comments [(***, (*+, and (*!].
Handles comments beginning with (***, (*+, and (*! as title
markers of decreasing importance."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on (setq-local font-lock-syntactic-face-function #'company-coq-syntactic-face-function))
      (`off (kill-local-variable 'font-lock-syntactic-face-function)))
    (company-coq-request-refontification)))

(defconst company-coq-features/coqdoc--spec
  '(("^\\s-*\\(?1:(\\*\\*\\s-\\)\\s-*\\(?2:\\*+\\)\\s-*\\(?3:.*?\\)\\(?:\\s-*\\**)\\)?\\s-*$"
     (3 (let ((depth (length (match-string 2))))
          (pcase depth
            (1 'company-coq-coqdoc-h1-face)
            (2 'company-coq-coqdoc-h2-face)
            (3 'company-coq-coqdoc-h3-face)
            (4 'company-coq-coqdoc-h4-face)
            (_ 'font-lock-doc-face)))
        append))))

(company-coq-define-feature coqdoc (arg)
  "CoqDoc comments [(** *, (** **, (** ***, etc.].
Handles comments beginning with (** followed by multiple `*' as
title markers of decreasing importance."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on (font-lock-add-keywords nil company-coq-features/coqdoc--spec 'add))
      (`off (font-lock-remove-keywords nil company-coq-features/coqdoc--spec)))
    (company-coq-request-refontification)))

(company-coq-define-feature obsolete-warnings (arg)
  "Code style warnings [experimental].
Highlights uses of obsolete Coq constructs."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on (font-lock-add-keywords nil company-coq-deprecated-spec 'add))
      (`off (font-lock-remove-keywords nil company-coq-deprecated-spec)))
    (company-coq-request-refontification)))

(company-coq-define-feature outline (arg)
  "Proof outlines.
Configures `outline-minor-mode' for use with Coq.  Supports
folding at the level of Proofs."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on
       (setq-local outline-level #'company-coq-outline-level)
       (setq-local outline-regexp company-coq-outline-regexp)
       (setq-local outline-heading-end-regexp company-coq-outline-heading-end-regexp)
       (outline-minor-mode))
      (`off
       (kill-local-variable 'outline-level)
       (kill-local-variable 'outline-regexp)
       (kill-local-variable 'outline-heading-end-regexp)
       (outline-minor-mode -1)))))

(defconst company-coq-features/code-folding--bullet-regexp
  "^\\s-*\\(?1:[*+-]+\\)\\(?:[ \t]\\|$\\)"
  "Regexp matching bullets.
This uses $ instead of \\n because \\n would confuse hideshow into
thinking that the line to fold from is the next one.")

(defconst company-coq-features/code-folding--brace-regexp
  "\\(?1:{\\)\\(?:[ \t]\\|$\\)"
  "Regexp matching braces.
Requiring a space helps with implicit args.  See
`company-coq-features/code-folding--bullet-regexp' about the use
of $ instead of \n.")

(defconst company-coq-features/code-folding--line-beginning-regexp
  "^[[:space:]*+-]*[*+-]\\s-+"
  "Regexp matching bullets from the beginning of the line.")

(defconst company-coq-features/code-folding--hs-regexp
  (concat "\\(?:"
          company-coq-features/code-folding--bullet-regexp "\\|"
          company-coq-features/code-folding--brace-regexp "\\)")
  "Regexp matching hide-show openers.")

;; NOTE: The documentation of hs-special-modes-alist specifically warns against
;; leading spaces in regexps, but we need them to tell bullets apart from
;; operators.
(defconst company-coq-features/code-folding--hs-spec
  `(coq-mode ,company-coq-features/code-folding--hs-regexp "}" "(\\*" nil nil)
  "Hide-show specification for Coq buffers.
The closing '}' is not made optional, because `looking-back'
wouldn't ever match it if it was.  `hs-minor-mode' doesn't mind a
missing end marker (it uses `forward-sexp' to find the end of
each block).")

(defface company-coq-features/code-folding-bullet-face
  '((t (:inherit link)))
  "Face used to change numbers to subscripts in hypothese names."
  :group 'company-coq-faces)

(defmacro company-coq--with-point-at-click (evt &rest body)
  "Set buffer, window, and point from EVT, then run BODY."
  (declare (indent defun)
           (debug t))
  `(let* ((--position (event-start ,evt))
          (--window (posn-window --position))
          (--buffer (window-buffer --window)))
     (with-selected-window --window
       (with-current-buffer --buffer
         (goto-char (posn-point --position))
         ,@body))))

(defun company-coq-features/code-folding--click-bullet (event)
  "Fold or unfold bullet at beginning of clicked line.
EVENT is the corresponding mouse event."
  (interactive "e")
  (company-coq--with-point-at-click event
    (company-coq-features/code-folding-toggle-bullet-at-point)))

(defun company-coq-features/code-folding-toggle-bullet-at-point (&optional beg fold-or-unfold)
  "Fold or unfold bullet at point.
If BEG is specified, skip the bullet detection logic and assume
BEG is a good position to call hideshow functions.  If
FOLD-OR-UNFOLD is `fold', force folding; if `unfold', force
unfolding; otherwise, toggle."
  (interactive)
  (-when-let* ((beg (cond (beg beg)
                          ((member (char-after) '(?* ?+ ?-))
                           (point-at-bol))
                          ((member (char-after) '(?{))
                           (point)))))
    (save-excursion
      (goto-char beg)
      (unless fold-or-unfold
        (setq fold-or-unfold (if (hs-overlay-at (point-at-eol)) 'unfold 'fold)))
      (cond
       ((eq fold-or-unfold 'unfold) (hs-show-block))
       ((eq fold-or-unfold 'fold) (hs-hide-block-at-point))))))

(defconst company-coq-features/code-folding--keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<mouse-1>") #'company-coq-features/code-folding--click-bullet)
    (define-key map (kbd "RET") #'company-coq-features/code-folding-toggle-bullet-at-point)
    map)
  "Keymap for bullets.")

(defconst company-coq-features/code-folding--bullet-fl-spec
  `(face company-coq-features/code-folding-bullet-face
         front-sticky nil
         rear-nonsticky t
         mouse-face highlight
         keymap ,company-coq-features/code-folding--keymap
         help-echo "Click (or press RET on) this bullet to hide or show its body.")
  "Display spec for bullets.
Using the keymap property works only if
`pg-span-context-menu-keymap' is set to nil.  Otherwise PG's
overlays take priority, and the code-folding keymap is ignored.
To override that, this code used to used local-map instead of a
keymap; and since it was a local map it had to copy
`coq-mode-map', which wasn't loaded at `require' time, so it had
to be a defun.")

(defun company-coq-features/code-folding--really-on-bullet-p (point)
  "Check if POINT is on a bullet."
  (save-match-data
    (save-excursion
      (goto-char point)
      (let ((sx (syntax-ppss)))
        (and
         ;; Not in a string
         (not (nth 3 sx))
         ;; Not in a comment
         (not (nth 4 sx))
         ;; Not a bullet in the middle of a line
         (or (eq (char-after) ?{)
             (-when-let* ((furthest-bullet (save-excursion
                                             (beginning-of-line)
                                             (when (looking-at company-coq-features/code-folding--line-beginning-regexp)
                                               (match-end 0)))))
               (<= (point) furthest-bullet)))
         ;; Not on a brace closed on the same line
         (not (and (eq (char-after) ?{)
                   (save-excursion
                     ;; Parent depth goes to -1 iff we find the matching '}'
                     (< (nth 6 (parse-partial-sexp (1+ point) (point-at-eol) -1)) 0))))
         ;; Really at the toplevel of a proof.
         ;; NOTE: This check works very well for bullets (but not for braces),
         ;; but it is too slow, so it's disabled
         (or t (save-excursion
                 (backward-up-list)
                 (looking-back "Proof" (point-at-bol)))))))))

(defun company-coq-features/code-folding--next-bullet (search-fn &optional regexp bound)
  "Find a bullet using SEARCH-FN and put point on it.
REGEXP and BOUND are passed to SEARCH-FN, as in
`re-search-forward'.  SEARCH-FN must make it so that the first
match group starts on the bullet.  If REGEXP is nil, use
`company-coq-features/code-folding--hs-regexp'."
  (unless regexp
    (setq regexp company-coq-features/code-folding--hs-regexp))
  (let ((saved-end nil))
    (save-excursion
      (while (and (setq saved-end (funcall search-fn regexp bound t))
                  (not (company-coq-features/code-folding--really-on-bullet-p
                        (match-beginning 1))))))
    (when saved-end
      (goto-char saved-end))))

(defun company-coq-features/code-folding--block-start ()
  "Find start of current bullet- (or brace-) delimited block."
  (company-coq-error-unless-feature-active 'code-folding)
  (pcase-let* ((`(,block-start . ,block-end)
                (save-excursion
                  (when (company-coq-features/code-folding--next-bullet
                         're-search-backward company-coq-features/code-folding--hs-regexp)
                    (cons (point) (progn (forward-sexp) (point)))))))
    (when (and block-start (>= block-end (point)))
      block-start)))

(defun company-coq-features/code-folding-fold-all ()
  "Fold all bullets and braces in current (narrowed) buffer."
  (save-excursion
    (goto-char (point-max))
    (while (company-coq-features/code-folding--next-bullet #'re-search-backward)
      (hs-hide-block-at-point)
      (goto-char (point-at-bol)))))

(defun company-coq-features/code-folding-unfold-all ()
  "Unfold all bullets and braces in current (narrowed) buffer."
  (dolist (ov (overlays-in (point-min) (point-max)))
    (when (overlay-get ov 'hs)
      (delete-overlay ov))))

(defvar company-coq-features/code-folding-toggle-block--globally-folded nil
  "Non-nil if last toggling hid all blocks.")

(defvar company-coq-features/code-folding-toggle-block--saved-arg nil
  "If set, future code folding toggles will be global.")

(defun company-coq-features/code-folding-toggle-block (arg)
  "Fold or unfold current bullet or brace pair.
With prefix ARG, toggle all bullets and braces."
  (interactive "P")
  ;; Remember prefix arg across consecutive invocations
  (unless (eq this-command last-command)
    (setq company-coq-features/code-folding-toggle-block--saved-arg nil))
  (setq arg (or arg company-coq-features/code-folding-toggle-block--saved-arg))
  ;; Toggle visibility
  (cond
   ((null arg)
    (setq company-coq-features/code-folding-toggle-block--globally-folded nil)
    (-when-let* ((block-start (company-coq-features/code-folding--block-start)))
      (company-coq-features/code-folding-toggle-bullet-at-point block-start)
      (message (substitute-command-keys "Use \\[universal-argument] \\[company-coq-features/code-folding-toggle-block] to hide or show all blocks."))))
   (t
    (if company-coq-features/code-folding-toggle-block--globally-folded
        (company-coq-features/code-folding-unfold-all)
      (company-coq-features/code-folding-fold-all))
    (setq company-coq-features/code-folding-toggle-block--globally-folded
          (not company-coq-features/code-folding-toggle-block--globally-folded))
    (message (substitute-command-keys "Repeat \\[company-coq-features/code-folding-toggle-block] to hide or show all blocks (no need to repeat \\[universal-argument])."))))
  (setq company-coq-features/code-folding-toggle-block--saved-arg arg))

(defvar company-coq-features/code-folding--overlays
  '(outline hs)
  "Which overlays contribute to code folding in this buffer.
Only overlays whose invisible property is `eq' to one of these
values are taken into account (and unfolded by)
`company-coq-features/code-folding--unfold-at-point' when a
command places the point in an invisible section.")

(defvar company-coq-features/code-folding--unfolding-commands
  '(proof-toolbar-next
    proof-assert-next-command
    proof-assert-next-command-interactive
    proof-toolbar-undo
    proof-undo-last-successful-command
    proof-toolbar-use
    proof-process-buffer
    proof-toolbar-retract
    proof-retract-buffer)
  "Which commands unfold folded sections after completing.
This list is used by `company-coq-features/code-folding--unfold-at-point' to
determine whether to unfold a code section after the point moves
into it.  If the code section isn't unfolded, the command loop
automatically moves the point out of it.")

(defun company-coq-features/code-folding--folding-overlays-at (pos)
  "List overlays that contribute to making POS invisible."
  (-filter (lambda (overlay)
             (memq (overlay-get overlay 'invisible)
                   company-coq-features/code-folding--overlays))
           (overlays-at pos)))

(defun company-coq-features/code-folding--unfold-at-point ()
  "Delete overlays making the point invisible.
This must be run as a post-command hook; it is not meant for
interactive use."
  (when (memq this-command company-coq-features/code-folding--unfolding-commands)
    (mapc #'delete-overlay (company-coq-features/code-folding--folding-overlays-at (point)))))

(defconst company-coq-features/code-folding--bullet-fl-keywords
  `((,(apply-partially #'company-coq-features/code-folding--next-bullet
                       #'re-search-forward company-coq-features/code-folding--hs-regexp)
     1 company-coq-features/code-folding--bullet-fl-spec nil))
  "Font-lock spec for bullets.")

(defcustom company-coq-features/code-folding-ellipsis " […]"
  "Ellipsis used for code folding.
Suggested values: […] [⤶] [↲] [▶] [⏩] [▸]."
  :type 'string
  :group 'company-coq)

(defface company-coq-features/code-folding-ellipsis-face
  '((t (:underline nil :inherit font-lock-preprocessor-face)))
  "Face used to display `company-coq-features/code-folding-ellipsis'."
  :group 'company-coq-faces)

(defun company-coq-features/code-folding--set-display-table ()
  "Add `company-coq-features/code-folding-ellipsis' to current buffer's display table."
  (unless buffer-display-table
    (setq buffer-display-table (make-display-table)))
  (set-display-table-slot buffer-display-table 4 ;; 4 is the '...' slot
                          (vconcat (mapcar (lambda (c) (make-glyph-code c 'company-coq-features/code-folding-ellipsis-face))
                                           company-coq-features/code-folding-ellipsis))))

(defun company-coq--set-up-font-lock-for-links ()
  "Configure font-lock to highlight bullets and braces."
  (make-local-variable 'font-lock-extra-managed-props)
  (add-to-list 'font-lock-extra-managed-props 'front-sticky)
  (add-to-list 'font-lock-extra-managed-props 'rear-nonsticky)
  (add-to-list 'font-lock-extra-managed-props 'mouse-face)
  (add-to-list 'font-lock-extra-managed-props 'keymap))

(defcustom company-coq-initial-fold-state nil
  "Initial folding state of Coq buffers.
One of nil (no folding), `bullets' (fold bullets and braces), and
`all' (fold everything, i.e. definitions and bullets).  This is
useful as a file-local variable."
  :group 'company-coq
  :type '(choice
          (const :tag "Fold nothing" nil)
          (const :tag "Fold bullets" bullets)
          (const :tag "Fold everything (definitions and bullets)" all))
  :safe #'symbolp)

(defun company-coq-features/code-folding-reset-to-initial-state (&optional force)
  "Fold parts of current buffer according to `company-coq-initial-fold-state'.
With FORCE, unfold everything before folding."
  (interactive '(t))
  (when force
    (company-coq-features/code-folding-unfold-all))
  (pcase company-coq-initial-fold-state
    (`bullets
     (company-coq-features/code-folding-fold-all))
    (`all
     (company-coq-features/code-folding-fold-all)
     (company-coq-call-compat 'outline-hide-body 'hide-body))))

(defun company-coq--remove-pg-keymaps ()
  "Ensure that PG overlays don't override out own local keymaps."
  (setq-local pg-span-context-menu-keymap nil)
  (dolist (ov (overlays-in (point-min) (point-max)))
    (when (and (overlay-get ov 'pghelp)
               (overlay-get ov 'keymap))
      (overlay-put ov 'keymap nil))))

(company-coq-define-feature code-folding (arg)
  "Code folding.
Configures `hs-minor-mode' for use with Coq.  Supports folding
bullets and curly braces."
  (pcase arg
    (`on
     (add-to-list 'hs-special-modes-alist company-coq-features/code-folding--hs-spec)
     (company-coq-do-in-coq-buffers
       (hs-minor-mode)
       (setq-local hs-allow-nesting t)
       (company-coq-features/code-folding--set-display-table)
       (company-coq--remove-pg-keymaps)
       (company-coq--set-up-font-lock-for-links)
       (font-lock-add-keywords nil company-coq-features/code-folding--bullet-fl-keywords 'add)
       (add-hook 'post-command-hook #'company-coq-features/code-folding--unfold-at-point t t)
       (add-hook 'hack-local-variables-hook #'company-coq-features/code-folding-reset-to-initial-state nil t)
       (company-coq-request-refontification)))
    (`off
     (setq hs-special-modes-alist (delete company-coq-features/code-folding--hs-spec hs-special-modes-alist))
     (company-coq-do-in-coq-buffers
       (hs-minor-mode -1)
       (kill-local-variable 'hs-allow-nesting)
       (kill-local-variable 'buffer-display-table)
       (kill-local-variable 'pg-span-context-menu-keymap)
       (font-lock-remove-keywords nil company-coq-features/code-folding--bullet-fl-keywords)
       (remove-hook 'post-command-hook #'company-coq-features/code-folding--unfold-at-point t)
       (remove-hook 'hack-local-variables-hook #'company-coq-features/code-folding-reset-to-initial-state t)
       (company-coq-request-refontification)))))

(defcustom company-coq-features/alerts-long-running-task-threshold 5
  "Minimum duration of a long-running sequence of commands.

Notifications are shown after Coq finishes processing all
commands, for any sequence of commands that took more than this
many seconds to complete (completion time is counted starting
after the last user input)."
  :group 'company-coq
  :type 'integer)

(defcustom company-coq-features/alerts-title-format "Prover ready! (proof took %s)"
  "Format string for the title of notifications."
  :group 'company-coq
  :type 'string)

(defcustom company-coq-features/alerts-body-function #'company-coq-features/alerts--alert-body
  "Function called to compute the body of notifications."
  :group 'company-coq
  :type 'function)

(defvar company-coq-features/alerts--last-interaction nil
  "Last time input was sent to the prover.")

(defvar company-coq-features/alerts--has-focus t
  "Whether Emacs currently has focus.
If non-nil, alerts are not displayed.")

(defun company-coq-features/alerts--focus-in ()
  "Register that Emacs got focus."
  (setq company-coq-features/alerts--has-focus t))

(defun company-coq-features/alerts--focus-out ()
  "Register that Emacs lost focus."
  (setq company-coq-features/alerts--has-focus nil))

(defun company-coq-features/alerts--handle-input (&rest _)
  "Notice that some input was just sent to the prover."
  (setq company-coq-features/alerts--last-interaction (current-time)))

(defun company-coq-features/alerts--handle-output (&rest _)
  "Notice that some output just came from the prover."
  (run-with-timer 0 nil #'company-coq-features/alerts--maybe-alert))

(defun company-coq-features/alerts--time-since-last-interaction ()
  "Compute the time elapsed since the last interaction."
  (and company-coq-features/alerts--last-interaction
       (float-time (time-since company-coq-features/alerts--last-interaction))))

(defun company-coq-features/alerts--maybe-alert ()
  "Show a notification if the prover is waiting for input."
  (when (and company-coq-features/alerts--last-interaction
             (not company-coq-features/alerts--has-focus)
             (company-coq-prover-available-p)
             (cl-every #'null proof-action-list)
             (> (company-coq-features/alerts--time-since-last-interaction)
                company-coq-features/alerts-long-running-task-threshold))
    (company-coq-features/alerts--alert)))

(defun company-coq-features/alerts--truncate (msg)
  "Truncate MSG, in preparation for alert."
  (replace-regexp-in-string " *\\(\n\\|\r\\) *" " " ;; " ⏎ "
                            (if (> (length msg) 80)
                                (concat (substring msg 0 80) "…")
                              msg)
                            t t))

(defun company-coq-features/alerts--alert-body ()
  "Compute body of notification."
  (company-coq-features/alerts--truncate
   (or (company-coq-with-current-buffer-maybe proof-response-buffer
         (buffer-substring-no-properties (point-min) (point-max)))
       (pcase proof-shell-last-output-kind
         ;; Ok to use last-output here despite Coq-mode's swallowing, as we
         ;; looked at response buffer first
         (`error proof-shell-last-output)
         (_      proof-shell-last-response-output))
       "")))

(defun company-coq--icon (&optional rotation)
  "Return the path to the icon of company-coq.
If ROTATION is non-nil, return the path to a rotated copy."
  (let ((path (expand-file-name (format (if (eq frame-background-mode 'dark)
                                            "icons/rooster-dark-%d.png"
                                          "icons/rooster-light-%d.png")
                                        (or rotation 0))
                                company-coq-refman-path)))
    (and (file-exists-p path) path)))

(defun company-coq-features/alerts--alert ()
  "Display and alert with a company-coq-features/alerts-specific message."
  (let* ((elapsed (float-time (time-since company-coq-features/alerts--last-interaction)))
         (title (format company-coq-features/alerts-title-format (company-coq-seconds-to-string elapsed)))
         (body (funcall company-coq-features/alerts-body-function)))
    (setq company-coq-features/alerts--last-interaction nil)
    (cond
     ((functionp 'alert)
      (company-coq-suppress-warnings
        (alert
         body
         :severity 'normal
         :icon (or (company-coq--icon) (bound-and-true-p alert-default-icon))
         :title (format company-coq-features/alerts-title-format (company-coq-seconds-to-string elapsed))
         :buffer proof-script-buffer)))
     ((functionp 'notifications-notify)
      (company-coq-suppress-warnings
        (notifications-notify
         :body body
         :urgency 'normal
         :title title
         :app-icon (or (company-coq--icon) (bound-and-true-p notifications-application-icon))))))))

(company-coq-define-feature alerts (arg)
  "Notifications for completion of long-running proofs.
Uses alert.el to display a notification when a proof completes."
  (pcase arg
    (`on
     (add-hook 'focus-in-hook #'company-coq-features/alerts--focus-in)
     (add-hook 'focus-out-hook #'company-coq-features/alerts--focus-out)
     (company-coq--listen-for-input #'company-coq-features/alerts--handle-input)
     (company-coq--listen-for-output #'company-coq-features/alerts--handle-output))
    (`off
     (remove-hook 'focus-in-hook #'company-coq-features/alerts--focus-in)
     (remove-hook 'focus-out-hook #'company-coq-features/alerts--focus-out)
     (company-coq--unlisten-for-input #'company-coq-features/alerts--handle-input)
     (company-coq--unlisten-for-output #'company-coq-features/alerts--handle-output))))

(defvar company-coq-features/spinner--rotation 0
  "Current orientation, in degrees, of the modeline spinner.
May be negative; in that case, it should be considered null.")

(defvar company-coq-features/spinner--rotation-step 30
  "Amplitude of an individual rotation of the modeline spinner.")

(defvar company-coq-features/spinner--initial-rotation -360
  "Initial orientation of the modeline spinner.
Anything below 0 causes the spinner to wait for a small while
before actually spinning.")

(defvar company-coq-features/spinner--spinning nil
  "Whether the modeline icon is currently spinning.")

(defvar company-coq-features/spinner-delay 0.05
  "Delay, in seconds, between two refreshes of the modeline spinner.")

(defun company-coq-features/spinner--maybe-stop ()
  "Stop spinning if necessary."
  (unless (and (company-coq-prover-busy-p) (company-coq-feature-active-p 'spinner))
    (cancel-function-timers #'company-coq-features/spinner--spin)
    (setq company-coq-features/spinner--spinning nil)))

(defun company-coq-features/spinner--spin ()
  "Update the rotation of the modeline spinner.
If the prover is idle, stop spinning after completing a full
rotation."
  (cl-assert (or company-coq-features/spinner--spinning (= company-coq-features/spinner--rotation 0)))
  (when company-coq-features/spinner--spinning
    (cl-incf company-coq-features/spinner--rotation company-coq-features/spinner--rotation-step)
    (when (>= company-coq-features/spinner--rotation 360)
      (setq company-coq-features/spinner--rotation 0))
    (when (= company-coq-features/spinner--rotation 0)
      (company-coq-features/spinner--maybe-stop)))
  (company-coq-do-in-coq-buffers (force-mode-line-update)))

(defun company-coq-features/spinner--start ()
  "Start spinning the modeline icon."
  (company-coq-dbg "company-coq-features/spinner--start called")
  (when (company-coq-feature-active-p 'spinner)
    (unless company-coq-features/spinner--spinning
      (setq company-coq-features/spinner--spinning t)
      (setq company-coq-features/spinner--rotation company-coq-features/spinner--initial-rotation)
      (run-with-timer 0 company-coq-features/spinner-delay #'company-coq-features/spinner--spin))))

(company-coq-define-feature spinner (arg)
  "Busy spinner.
Spins the modeline icon when Coq is busy."
  (pcase arg
    (`on
     (company-coq-features/spinner--start)
     (company-coq--listen-for-input #'company-coq-features/spinner--start))
    (`off
     (company-coq--unlisten-for-input #'company-coq-features/spinner--start))))

(company-coq-define-feature cross-ref (arg)
  "Cross references and browsing to definition.
Lets you jump to the definition of a symbol by pressing M-. on it.")

(defun company-coq--diff-dwim-help-message ()
  "Suggest to use a keybinding instead of a link to open a diff."
  (message "%s" (substitute-command-keys "Press q to close this diff. Next time, you can use \\<company-coq-map>\\[company-coq-diff-dwim] to open it faster.")))

(defun company-coq-features/error-diffs--hyperlink-action (_btn)
  "Handle a click on the “diff” button for errors."
  (company-coq-diff-unification-error)
  (company-coq--diff-dwim-help-message))

(defun company-coq--remove-overlays (buffer prop)
  "Delete overlays in BUFFER with PROP."
  (company-coq-with-current-buffer-maybe buffer
    (dolist (ov (overlays-in (point-min) (point-max)))
      (when (overlay-get ov prop)
        (delete-overlay ov)))))

(defun company-coq--make-link-string (pre link post action help-echo)
  "Create a link.
Concatenate PRE, LINK, and POST to get the link's text, only
applying the link to LINK.  ACTION and HELP-ECHO are passed to the button
library."
  (with-temp-buffer
    (insert pre)
    (insert-text-button link
                        'follow-link t
                        'action action
                        'help-echo help-echo)
    (insert post)
    (buffer-string)))

(defun company-coq-features/error-diffs--make-link-string ()
  "Create link to diff of unification error."
  (company-coq--make-link-string " (" "diff" ")" #'company-coq-features/error-diffs--hyperlink-action
                      "Compare the terms mentioned by this error message."))

(defun company-coq-features/error-diffs--add-link ()
  "Add a link to current response if it's a unification error."
  (company-coq--remove-overlays proof-response-buffer 'company-coq-features/error-diffs)
  (company-coq-with-current-buffer-maybe proof-response-buffer
    (save-excursion
      (goto-char (point-min))
      (when (save-excursion (re-search-forward company-coq-unification-error-quick-regexp nil t))
        (when (re-search-forward company-coq-unification-error-header nil t)
          (let ((ov (make-overlay (match-beginning 0) (match-end 0))))
            (overlay-put ov 'company-coq-features/error-diffs t)
            (overlay-put ov 'after-string (company-coq-features/error-diffs--make-link-string))))))))

(company-coq-define-feature error-diffs (arg)
  "Diffs of unification errors.
Add a link to unification errors to show a diff."
  (pcase arg
    (`on (company-coq--listen-for-output #'company-coq-features/error-diffs--add-link))
    (`off (company-coq--unlisten-for-output #'company-coq-features/error-diffs--add-link))))

(defun company-coq-features/refactorings--reqs-compute-module-fqn (mod-name)
  "Find fully qualified name of MOD-NAME.
In case of error return a cons (error . ERROR-MSG)"
  (save-match-data
    (let* ((cmd (format company-coq-locate-lib-cmd mod-name))
           (out (company-coq-ask-prover cmd)))
      (if (string-match company-coq-locate-lib-output-format out)
          (match-string-no-properties 1 out)
        `(error . ,out)))))

(defun company-coq-features/refactorings--reqs-add-overlay (from to fqn)
  "Add an fully qualified module name overlay covering FROM .. TO.
This overlay is used to display an fully qualified (FQN) version
of a module name, before replacing that name (after getting a
confirmation form the user)."
  (let ((ov (make-overlay from to)))
    (overlay-put ov 'company-coq-fqn-of-module fqn)
    ov))

(defun company-coq-features/refactorings--reqs-add-overlays (limit display)
  "Change [Require Import]s up to LIMIT to use fully qualified names.
Use overlays to display fully qualified names.  If DISPLAY is
nil, record fully qualified names using overlays, but don't give
them visible properties."
  (let ((end-m (make-marker))
        (overlays nil))
    (set-marker end-m limit)
    (while (re-search-forward company-coq-module-name-regexp end-m t)
      (let* ((rel-name (match-string 0))
             (abs-name (company-coq-features/refactorings--reqs-compute-module-fqn rel-name)))
        (unless (equal rel-name abs-name)
          (let ((ov (company-coq-features/refactorings--reqs-add-overlay
                     (match-beginning 0) (match-end 0) abs-name)))
            (push ov overlays)
            (when display
              (pcase abs-name
                ((pred stringp)
                 (overlay-put ov 'display abs-name)
                 (overlay-put ov 'face 'highlight))
                (`(error . ,msg)
                 (overlay-put ov 'help-echo msg)
                 (overlay-put ov 'face font-lock-warning-face))))))))
    (set-marker end-m nil)
    overlays))

(defun company-coq-features/refactorings--reqs-commit (ovs)
  "Perform replacements suggested by overlays in OVS."
  (save-excursion
    (dolist (ov ovs)
      (let ((abs (overlay-get ov 'company-coq-fqn-of-module))
            (inhibit-modification-hooks t))
        (when (stringp abs)
          (goto-char (overlay-start ov))
          (delete-region (point) (overlay-end ov))
          (insert abs))))))

(defconst company-coq-features/refactorings--reqs-header "\\(\\<Require\\(?: Import\\| Export\\)?\\>\\)"
  "Header of [Require] commands that can be fully qualified.")

(defconst company-coq-features/refactorings--reqs-menu
  (let ((map (make-sparse-keymap "Refactor imports")))
    (define-key map [abs-no-confirm]
      `("Fully qualify module names (no confirmation)" .
        company-coq-features/refactorings-qualify-module-names-without-confirmation))
    (define-key map [abs-confirm]
      '("Fully qualify module names" .
        company-coq-features/refactorings-qualify-module-names))
    map)
  "Menu for right clicks on [Require]s.")

(defun company-coq-features/refactorings--reqs-get-region ()
  "Compute a region in which to fully qualify modules names."
  (if (region-active-p)
      (list (region-beginning) (region-end))
    (company-coq--current-command-bounds)))

(defun company-coq-features/refactorings-qualify-module-names (beg end &optional confirm-changes)
  "Change [Require Import]s to use fully qualified names.
Interactively, use region if avaiilable and current phrase
otherwise, and use overlays to display fully qualified names and
query the user before replacing unless given a prefix argument.
From Lisp, replace forms in BEG .. END, asking for confirmation
if CONFIRM-CHANGES is non-nil."
  (interactive `(,@(company-coq-features/refactorings--reqs-get-region)
                 (not (consp current-prefix-arg))))
  (company-coq-complain-unless-prover-available "refactoring")
  (save-excursion
    (goto-char beg)
    (unless (re-search-forward company-coq-features/refactorings--reqs-header end t)
      (user-error "No [Require]s found in “%s”" (buffer-substring-no-properties beg end)))
    (let ((ovs (company-coq-features/refactorings--reqs-add-overlays end confirm-changes)))
      (unwind-protect
          (cond
           ((null ovs)
            (user-error "All module names on this line are already fully qualified"))
           ((or (not confirm-changes) (y-or-n-p "Apply changes? "))
            (company-coq-features/refactorings--reqs-commit ovs)))
        (mapc #'delete-overlay ovs)))))

(defun company-coq-features/refactorings-qualify-module-names-without-confirmation (beg end)
  "Change [Require Import]s to use fully qualified names.
BEG and END are as in
`company-coq-features/refactorings-qualify-module-names-without-confirmation'."
  (interactive (company-coq-features/refactorings--reqs-get-region))
  (company-coq-features/refactorings-qualify-module-names beg end nil))

(defun company-coq--popup-menu-no-x--read-keymap (keymap)
  "Compute a cons of title and menu entries from KEYMAP."
  (cons (car (-filter #'stringp keymap))
	(cl-loop for pair being the key-bindings of keymap
		 for num = 0 then (1+ num)
		 collect (cons num pair))))

(defun company-coq--popup-menu-no-x--format-entries (entries prefix)
  "Prepare a menu string from menu ENTRIES.
Use PREFIX before each menu entry."
  (mapconcat (lambda (entry)
	       (pcase entry
		 (`(,num ,desc . ,_)
		  (format "%s%d → %s" prefix num desc))))
             entries ""))

(defun company-coq--popup-menu-no-x--prompt-string (entries title prefix)
  "Compute a prompt string from ENTRIES using TITLE.
Prefix each entry with PREFIX."
  (let* ((menu (company-coq--popup-menu-no-x--format-entries entries prefix)))
    (format "%s (press a key):%s" title menu)))

(defun company-coq--popup-menu-no-x--prompt (entries title prefix)
  "Prompt for a choice from ENTRIES.
Pass TITLE and PREFIX to `company-coq--popup-menu-no-x--prompt-string'."
  (let* ((prompt (company-coq--popup-menu-no-x--prompt-string entries title prefix)))
    (message prompt)
    (-when-let* ((input (ignore-errors (string-to-number (char-to-string (read-char))))))
      (cddr (assoc input entries)))))

(defun company-coq--popup-menu-no-x (keymap)
  "Emulate `popup-menu' on KEYMAP using text only.
In Emacs 25 `popup-menu' emulation is not very usable, and on 24
it doesn't work: sometimes it shows an error, sometimes (with
position t) it segfaults."
  (let* ((title-entries (company-coq--popup-menu-no-x--read-keymap keymap))
	 (title (or (car title-entries) "Action"))
	 (entries (-take 10 title-entries)))
    (-when-let* ((choice (company-coq--popup-menu-no-x--prompt entries title "\n  ")))
      (call-interactively choice))))

(defun company-coq-features/refactorings--get-prompt-at-point (separator)
  "Compute the refactoring prompt at point.
Separate entries with SEPARATOR.  Useful for screenshot generation."
  (pcase-let* ((keymap (company-coq-features/refactorings--get-menu-at-point))
               (`(,title . ,entries) (company-coq--popup-menu-no-x--read-keymap keymap)))
    (company-coq--popup-menu-no-x--prompt-string entries title separator)))

(defun company-coq--popup-menu (keymap &optional position)
  "Show a popup menu (based on KEYMAP) at POSITION.
If POSITION is nil, show a text-only menu in the minibuffer."
  (when keymap
    (if position
        ;; `popup-menu' is much nicer than `x-popup-menu'; the latter returns a
        ;; list of events, which one must convert with (apply #'vector actions)
        ;; before callign the resulting command.
        (let ((use-dialog-box nil))
          (popup-menu keymap position))
      (company-coq--popup-menu-no-x keymap))))

(defun company-coq-features/refactorings--get-menu-at-point (&optional pt)
  "Get refactoring menu at point PT."
  (get-text-property (or pt (point)) 'company-coq-features/refactorings--menu))

(defun company-coq-features/refactorings--show-menu-at-point (&optional event)
  "Show refactoring menu at point.
With EVENT, position the menu according to that mouse event."
  (interactive)
  (company-coq--popup-menu (company-coq-features/refactorings--get-menu-at-point) event))

(defun company-coq-features/refactorings--show-menu (event)
  "Show refactoring menu.
EVENT is the corresponding mouse event."
  (interactive "e")
  (company-coq--with-point-at-click event
    (company-coq-features/refactorings--show-menu-at-point event)))

(defconst company-coq-features/refactorings--keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<down-mouse-3>") #'company-coq-features/refactorings--show-menu)
    (define-key map (kbd "<mouse-3>") #'ignore)
    (define-key map (kbd "<C-down-mouse-1>") #'company-coq-features/refactorings--show-menu)
    (define-key map (kbd "<C-mouse-1>") #'ignore)
    (define-key map (kbd "<menu>") #'company-coq-features/refactorings--show-menu-at-point)
    map)
  "Keymap for refactoring tags.
See `company-coq-features/code-folding--keymap' for more info.")

(defface company-coq-features/refactorings-highlight-face
  '((t (:underline "DimGray")))
  "Face used to display refactoring tags."
  :group 'company-coq-faces)

(defconst company-coq-features/refactorings--fl-spec
  ;;"#888a85" ;;,(face-attribute 'default :background)
  `(face company-coq-features/refactorings-highlight-face
         front-sticky nil
         rear-nonsticky t
         pointer hand
         keymap ,company-coq-features/refactorings--keymap
         help-echo "Right click (or C-click) to show the refactoring menu.")
  "Display spec for refactoring tags.")

(defconst company-coq-features/refactorings--fl-keywords
  `((,company-coq-features/refactorings--reqs-header
     (1 `(,@company-coq-features/refactorings--fl-spec
          company-coq-features/refactorings--menu ,company-coq-features/refactorings--reqs-menu)
        append))))

(company-coq-define-feature refactorings (arg)
  "Various refactoring commands (experimental).
Currently focuses on [Require Import/Export] statements."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on
       (company-coq--remove-pg-keymaps)
       (company-coq--set-up-font-lock-for-links)
       (font-lock-add-keywords nil company-coq-features/refactorings--fl-keywords 'append)
       (company-coq-request-refontification))
      (`off
       (kill-local-variable 'pg-span-context-menu-keymap)
       (font-lock-remove-keywords nil company-coq-features/refactorings--fl-keywords)
       (company-coq-request-refontification)))))

(company-coq-define-feature company (arg)
  "Context-sensitive completion.
Configures `company-mode' for use with Coq."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on
       (company-mode)
       (make-local-variable 'company-backends)
       (dolist (backend '(company-coq-master-backend company-coq-choices-backend))
         (setq company-backends (remove backend company-backends))
         (push backend company-backends)))
      (`off
       (company-mode -1)
       (kill-local-variable 'company-backends)))))

(defun company-coq-features/company-defaults--indent-or-complete-common ()
  "Call `company-indent-or-complete-common'."
  (interactive)
  (call-interactively #'company-indent-or-complete-common))

(company-coq-define-feature company-defaults (arg)
  "Convenient defaults for `company-mode'.
Tweaks company-mode settings for smoother use with Coq."
  (company-coq-do-in-coq-buffers
    (pcase arg
      (`on
       (setq-local company-idle-delay 0.01)
       (setq-local company-tooltip-align-annotations t)
       (setq-local company-abort-manual-when-too-short t)
       ;; See https://github.com/cpitclaudel/company-coq/issues/42
       (unless (command-remapping #'company-complete-common nil company-active-map)
         (define-key company-active-map [remap company-complete-common]
           #'company-coq-features/company-defaults--indent-or-complete-common)))
      (`off
       (kill-local-variable 'company-idle-delay)
       (kill-local-variable 'company-tooltip-align-annotations)
       (kill-local-variable 'company-abort-manual-when-too-short)
       (when (eq (command-remapping #'company-complete-common nil company-active-map)
                 #'company-coq-features/company-defaults--indent-or-complete-common)
         (define-key company-active-map [remap company-complete-common] nil))))))

(company-coq-define-feature unicode-math-backend (arg)
  "Completion of LaTeX macros.
Inserts ⊕ when you type \oplus."
  ;; Insert directly in company's backend list, as it doesn't share the same
  ;; prefix as the other backends.
  (company-coq-do-in-coq-buffers
    (make-local-variable 'company-backends)
    (setq company-backends (remove #'company-coq-math-symbols-backend company-backends))
    (pcase arg
      (`on
       (push #'company-coq-math-symbols-backend company-backends)))))

(company-coq-define-feature block-end-backend (arg)
  "Completion of Section and Module names.
Autocompletes names after `End '."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-block-end-backend))
    (`off (company-coq-remove-backend #'company-coq-block-end-backend))))

(company-coq-define-feature reserved-keywords-backend (arg)
  "Completion of Coq reserved keywords.
Autocompletes `fix', `with', `let', etc."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-reserved-keywords-backend))
    (`off (company-coq-remove-backend #'company-coq-reserved-keywords-backend))))

(defmacro company-coq--define-refman-abbrevs-feature (source from to)
  "Create a completion feature for refman source SOURCE.
Complete FROM into TO."
  (let* ((name (symbol-name source))
         (repo-sym (intern (format "company-coq--refman-%s-abbrevs" name)))
         (cache-sym (intern (format "company-coq--refman-%s-abbrevs-cache" name)))
         (init-sym (intern (format "company-coq--init-refman-%s-abbrevs-cache" name)))
         (backend-sym (intern (format "company-coq-refman-%s-abbrevs-backend" name)))
         (feature-sym (intern (format "refman-%s-abbrevs-backend" name))))
    `(progn
       (defvar ,cache-sym nil
         ,(format "Cache of parsed Coq %s abbrevs taken from the RefMan." name))

       (defun ,init-sym (&optional force)
         (interactive '(t))
         ,(format "Load %s abbrevs from refman if needed or FORCE'd." name)
         (company-coq-dbg "%s: Loading abbrevs (if never loaded)" ,(symbol-name init-sym))
         (company-coq-reload-db ',cache-sym (lambda () (mapcar #'company-coq-parse-man-db-entry ,repo-sym)) nil nil nil force))

       (defun ,backend-sym (command &optional arg &rest ignored)
         ,(format "`company-mode' backend for documented Coq %ss.
COMMAND, ARG and IGNORED: see `company-backends'." name)
         (interactive (list 'interactive))
         (company-coq-dbg "refman %s backend: called with command %s" ,name command)
         (company-coq-generic-refman-backend #',init-sym #',backend-sym command arg ignored))

       (company-coq-define-feature ,feature-sym (arg)
         ,(format "Completion of %ss documented in the manual.
Autocompletes `%s' into `%s'." name from to)
         (pcase arg
           (`on (company-coq-add-backend #',backend-sym))
           (`off (company-coq-remove-backend #',backend-sym)))))))

(company-coq--define-refman-abbrevs-feature ltac "tte" "tryif … then … else …")
(company-coq--define-refman-abbrevs-feature tactic "applin" "apply … in …")
(company-coq--define-refman-abbrevs-feature vernac "SLD" "Set Ltac Debug.")
(company-coq--define-refman-abbrevs-feature scope "nat_" "nat_scope")

(company-coq-define-feature pg-backend (arg)
  "Completion of PG abbrevs.
Includes smart completions, such as `intros!'."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-pg-backend))
    (`off (company-coq-remove-backend #'company-coq-pg-backend))))

(company-coq-define-feature context-backend (arg)
  "Completion of hypotheses.
Autocompletes hypothesis names from the current proof context."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-context-backend))
    (`off (company-coq-remove-backend #'company-coq-context-backend))))

(company-coq-define-feature modules-backend (arg)
  "Completion of module names.
Autocompletes after `Require '."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-modules-backend))
    (`off (company-coq-remove-backend #'company-coq-modules-backend))))

(company-coq-define-feature local-definitions-backend (arg)
  "Completion of local definitions.
Autocompletes theorem and tactic names from the current buffer."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-local-definitions-backend))
    (`off (company-coq-remove-backend #'company-coq-local-definitions-backend))))

(company-coq-define-feature search-results-backend (arg)
  "Completion using search results.
Autocompletes theorem names from results of the last search."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-search-results-backend))
    (`off (company-coq-remove-backend #'company-coq-search-results-backend))))

(company-coq-define-feature dynamic-tactics-backend (arg)
  "Completion of tactics (dynamic).
Autocompletes tactics and notations by querying the prover."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-dynamic-tactics-backend))
    (`off (company-coq-remove-backend #'company-coq-dynamic-tactics-backend))))

(company-coq-define-feature dynamic-symbols-backend (arg)
  "Completion of global definitions [experiental, slow].
Autocompletes theorem names by querying the prover.
Use `company-coq-live-on-the-edge' to enable this feature."
  (pcase arg
    (`on (company-coq-add-backend #'company-coq-dynamic-symbols-backend))
    (`off (company-coq-remove-backend #'company-coq-dynamic-symbols-backend))))

(eval-and-compile
  (put (company-coq-feature-toggle-function 'dynamic-symbols-backend)
       'company-coq-feature-experimental t)
  (put (company-coq-feature-toggle-function 'dynamic-symbols-backend)
       'company-coq-feature-requires-patched-coqtop t))

(defun company-coq-warn-obsolete-setting (setting)
  "Warn about the use of obsolete setting SETTING."
  ;; LATER: start issuing warnings for outdated customizations
  (unless t
    (company-coq-warn "Option %S is obsolete. Customize `company-coq-disabled-features' and `company-coq-live-on-the-edge' instead." setting)))

(company-coq-define-feature obsolete-settings (arg)
  "Obsolete settings support (from versions before 1.0).
Understands settings inherited from previous versions of
company-coq."
  (pcase arg
    (`on
     (let ((used-obsolete-settings nil))
       (unless company-coq-autocomplete-context
         (push 'company-coq-autocomplete-context used-obsolete-settings)
         (add-to-list 'company-coq-disabled-features 'context-backend))
       (unless company-coq-autocomplete-modules
         (push 'company-coq-autocomplete-modules used-obsolete-settings)
         (add-to-list 'company-coq-disabled-features 'modules-backends))
       (unless company-coq-autocomplete-symbols
         (push 'company-coq-autocomplete-symbols used-obsolete-settings)
         (add-to-list 'company-coq-disabled-features 'dynamic-symbols-backend))
       (unless company-coq-autocomplete-block-end
         (push 'company-coq-autocomplete-block-end used-obsolete-settings)
         (add-to-list 'company-coq-disabled-features 'block-end-backend))
       (unless company-coq-autocomplete-search-results
         (push 'company-coq-autocomplete-search-results used-obsolete-settings)
         (add-to-list 'company-coq-disabled-features 'search-results-backend))
       (unless company-coq-prettify-symbols
         (push 'company-coq-prettify-symbols used-obsolete-settings)
         (add-to-list 'company-coq-disabled-features 'prettify-symbols))
       (when company-coq-dynamic-autocompletion
         (push 'company-coq-dynamic-autocompletion used-obsolete-settings)
         (setq company-coq-live-on-the-edge t))
       (dolist (setting used-obsolete-settings)
         (company-coq-warn-obsolete-setting setting))))))

(defun company-coq-enabled-features ()
  "Compute the list of enabled company-coq features."
  (cl-remove-if (lambda (b) (member b company-coq-disabled-features))
                (mapcar #'car company-coq-available-features)))

(defvar company-coq--selected-window nil
  "Tracks the currently selected window.")

(defun company-coq--record-selected-window ()
  "Save selected window.
There is no way to access the selected window from
`company-coq--lighter-string', as it is always called with the
current window selected.  Instead, we simply save the selected
window every time it changes.  We need to know the selected
window, because we want to adjust the spinning rooster's
background."
  (unless (eq (selected-window) (minibuffer-window))
    (setq company-coq--selected-window (selected-window))))

(defun company-coq--ligther-image ()
  "Compute the match to the modeline icon."
  (company-coq--icon (max company-coq-features/spinner--rotation 0)))

(defconst company-coq--rooster-char-displayable
  (char-displayable-p ?🐤)
  "Whether 🐤 can be displayed.
This check is costly, so do it only once.")

(defun company-coq--lighter-string ()
  "Compute a string to display in the modeline."
  (let* ((selected-p (eq (selected-window) company-coq--selected-window))
         (mode-line-face (if selected-p 'mode-line 'mode-line-inactive))
         (mode-line-height (face-attribute 'mode-line :height nil 'default))
         (mode-line-background (face-attribute mode-line-face :background nil 'default))
         (display-spec `(image :type imagemagick ;; Image file from emojione
                               :file ,(company-coq--ligther-image) ;; rooster
                               :ascent center
                               :mask heuristic
                               :height ,(ceiling (* 0.14 mode-line-height))
                               ;; Inherit bg explicitly
                               :background ,mode-line-background))
         (can-display-rooster-char (if (display-graphic-p)
                                       company-coq--rooster-char-displayable
                                     company-coq-features/prettify-symbols-in-terminals))
         (lighter-string (if can-display-rooster-char
                             ;; 🐤 🐣 🐓 🐔
                             "company-🐤"
                           "company-coq")))
    (apply #'propertize lighter-string
           (when (and (company-coq--icon) (image-type-available-p 'imagemagick))
             (list 'display display-spec)))))

(defvar company-coq--lighter-var
  ;; See https://emacs.stackexchange.com/questions/18945/can-i-use-an-image-in-my-modeline-lighter
  '(:eval (list " " (company-coq--lighter-string)))
  "Lighter var for `company-coq-mode'.
Must be tagged risky to display properly.")

(put 'company-coq--lighter-var 'risky-local-variable t)

;;;###autoload
(define-minor-mode company-coq-mode
  "Toggle company-coq-mode on or off.

Company-Coq is a collection of Proof-General extensions.  See
https://github.com/cpitclaudel/company-coq/ for a detailed
description, including screenshots and documentation.  First time
users may want to use \\[company-coq-tutorial] to open the
tutorial.

With a prefix argument ARG, enable %s if ARG is
positive, and disable it otherwise.  If called from Lisp, enable
the mode if ARG is omitted or nil, and toggle it if ARG is `toggle'.

\\{company-coq-map}"
  :lighter company-coq--lighter-var
  :group 'company-coq
  :keymap company-coq--core-map
  :variable company-coq-mode
  (let ((enabled company-coq-mode))
    (company-coq-do-in-coq-buffers
      (setq-local company-coq-mode enabled))
    (company-coq-toggle-features (company-coq-enabled-features) enabled)))

;;;###autoload
(defun company-coq-initialize () ;; LATER: Deprecate this
  "Deprecated: Use `company-coq-mode' instead."
  (interactive)
  (company-coq-mode))

(defun company-coq-unload-function ()
  "Unload function for company-coq."
  (company-coq-do-in-coq-buffers (company-coq-mode -1))
  (cl-loop for feature in '(company-coq-abbrev company-coq-tg)
           when (featurep feature)
           do (unload-feature feature t))
  nil)

(defun toggle-company-coq-debug ()
  "Toggle `company-coq-debug'.
When on, print debug messages during operation."
  (interactive)
  (setq company-coq-debug (not company-coq-debug))
  (message "company-coq-debug: %s" company-coq-debug))

;; Local Variables:
;; checkdoc-arguments-in-order-flag: nil
;; checkdoc-verb-check-experimental-flag: nil
;; End:

(provide 'company-coq)
;;; company-coq.el ends here
