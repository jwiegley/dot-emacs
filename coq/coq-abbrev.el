;;; coq-abbrev.el --- coq abbrev table and menus for ProofGeneral mode

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Authors: Healfdene Goguen, Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;

;;; Code:

(require 'proof)
(require 'coq-syntax)

(defun holes-show-doc ()
  (interactive)
  (describe-function 'holes-mode))

(defun coq-local-vars-list-show-doc ()
  (interactive)
  (describe-variable 'coq-local-vars-doc))


(defconst coq-tactics-menu
  (append '("Tactics (menu)"
	    ["Intros (smart)" coq-insert-intros :help "Insert \"intros h1 .. hn.\" where hi are the default names given by Coq."])
	  (coq-build-menu-from-db (append coq-tactics-db coq-solve-tactics-db))))

(defconst coq-tactics-abbrev-table
  (coq-build-abbrev-table-from-db (append coq-tactics-db coq-solve-tactics-db)))

(defconst coq-tacticals-menu
  (append '("Tacticals (menu)")
	  (coq-build-menu-from-db coq-tacticals-db)))

(defconst coq-tacticals-abbrev-table
  (coq-build-abbrev-table-from-db coq-tacticals-db))

(defconst coq-commands-menu
  (append '("Command (menu)"
	    ;["Module/Section (smart)" coq-insert-section-or-module t]
	    ;["Require (smart)" coq-insert-requires t]
	    )
	  (coq-build-menu-from-db coq-commands-db)))

(defconst coq-commands-abbrev-table
  (coq-build-abbrev-table-from-db coq-commands-db))

(defconst coq-terms-menu
  (append '("Term (menu)"
	    ["Match (smart)" coq-insert-match t])
	  (coq-build-menu-from-db coq-terms-db)))

(defconst coq-terms-abbrev-table
  (coq-build-abbrev-table-from-db coq-terms-db))



;;; The abbrev table built from keywords tables
;#s and @{..} are replaced by holes by holes-abbrev-complete
(defun coq-install-abbrevs ()
  "install default abbrev table for coq if no other already is."
  (if (boundp 'coq-mode-abbrev-table)
      ;; da: this test will always fail.  Assume bound-->non-empty
      ;; (not (equal coq-mode-abbrev-table (make-abbrev-table))))
      (message "Coq abbrevs already exists, default not loaded")
    (define-abbrev-table 'coq-mode-abbrev-table
      (append coq-tactics-abbrev-table coq-tacticals-abbrev-table
              coq-commands-abbrev-table coq-terms-abbrev-table))
    ;; if we use default coq abbrev, never ask to save it
    ;; PC: fix trac #382 I comment this. But how to disable abbrev
    ;; saving for coq mode only?
    ;;(setq save-abbrevs nil) ; 
    ;; DA: how about above, just temporarily disable saving?
    (message "Coq default abbrevs loaded")))

(unless (or noninteractive (bound-and-true-p byte-compile-current-file))
  (coq-install-abbrevs))
;;;;;

; Redefining this macro to change the way a string option is asked to
; the user: we pre fill the answer with current value of the option;
(defun proof-defstringset-fn (var &optional othername)
  "Define a function <VAR>-toggle for setting an integer customize setting VAR.
Args as for the macro `proof-defstringset', except will be evaluated."
  (eval
   `(defun ,(if othername othername
	      (intern (concat (symbol-name var) "-stringset"))) (arg)
	      ,(concat "Set `" (symbol-name var) "' to ARG.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-defstringset-fn'.")
;	      (interactive ,(format "sValue for %s (a string, currenly %s): "
;				    (symbol-name var) (symbol-value var)))
	      (interactive (list
			    (read-string
			     (format "Value for %s (float): "
				     (symbol-name (quote ,var))
				     (symbol-value (quote ,var)))
			     (symbol-value (quote ,var)))))
	      (customize-set-variable (quote ,var) arg))))

;; The coq menu partly built from tables

;; Common part (script, response and goals buffers)
(defconst coq-menu-common-entries
  `(
    ["Toggle 3 Windows Mode" proof-three-window-toggle
     :style toggle
     :selected proof-three-window-enable
     :help "Toggles the use of separate windows or frames for Coq responses and goals."
     ]
    ("3 Windows mode layout"
     ["smart"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'smart)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'smart)
      :help "Adapt to frame width (C-c C-l to refresh)"]
     ["hybrid"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'hybrid)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'hybrid)
      :help "two column mode"]
     ["horizontal"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'horizontal)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'horizontal)
      :help "Three column mode"]
     ["vertical"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'vertical)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'vertical)
      :help "One column mode"])
    ["Refresh Windows Layout" proof-layout-windows t]
    ["Toggle tooltips" proof-output-tooltips-toggle
     :style toggle
     :selected proof-output-tooltips
     :help "Toggles Tooltips (popup when hovering commands).\nSet `proof-output-tooltips' to nil to disable it by default."]
    ["Electric Terminator" proof-electric-terminator-toggle
     :style toggle
     :selected proof-electric-terminator-enable
     :help "Automatically send commands when terminator typed"]
    ["Double Hit Electric Terminator" coq-double-hit-toggle
     :style toggle
     :selected coq-double-hit-enable
     :help "Automatically send commands when terminator typed twiced quickly."]
    ("Auto Compilation"
     ["Compile Before Require"
      coq-compile-before-require-toggle
      :style toggle
      :selected coq-compile-before-require
      :help "Check dependencies of required modules and compile on the fly."]
     ["Parallel background compilation"
      coq-compile-parallel-in-background-toggle
      :style toggle
      :selected coq-compile-parallel-in-background
      :active coq-compile-before-require
      :help ,(concat "Compile parallel in background or "
		    "sequentially with blocking ProofGeneral.")]
     ["Keep going"
      coq-compile-keep-going-toggle
      :style toggle
      :selected coq-compile-keep-going
      :active (and coq-compile-before-require
		   coq-compile-parallel-in-background)
      :help ,(concat "Continue background compilation after "
		     "the first error as far as possible")]
     ("Quick compilation"
      ["no quick"
       (customize-set-variable 'coq-compile-quick 'no-quick)
       :style radio
       :selected (eq coq-compile-quick 'no-quick)
       :active (and coq-compile-before-require
		    coq-compile-parallel-in-background)
       :help "Compile without -quick but accept existion .vio's"]
      ["quick no vio2vo"
       (customize-set-variable 'coq-compile-quick 'quick-no-vio2vo)
       :style radio
       :selected (eq coq-compile-quick 'quick-no-vio2vo)
       :active (and coq-compile-before-require
		    coq-compile-parallel-in-background)
       :help "Compile with -quick, accept existing .vo's, don't run vio2vo"]
      ["quick and vio2vo"
       (customize-set-variable 'coq-compile-quick 'quick-and-vio2vo)
       :style radio
       :selected (eq coq-compile-quick 'quick-and-vio2vo)
       :active (and coq-compile-before-require
		    coq-compile-parallel-in-background)
       :help "Compile with -quick, accept existing .vo's, run vio2vo later"]
      ["ensure vo"
       (customize-set-variable 'coq-compile-quick 'ensure-vo)
       :style radio
       :selected (eq coq-compile-quick 'ensure-vo)
       :active (and coq-compile-before-require
		    coq-compile-parallel-in-background)
       :help "Ensure only vo's are used for consistency"]
      )
     ("Auto Save"
      ["Query coq buffers"
       (customize-set-variable 'coq-compile-auto-save 'ask-coq)
       :style radio
       :selected (eq coq-compile-auto-save 'ask-coq)
       :active coq-compile-before-require
       :help "Ask for each coq-mode buffer, except the current buffer"]
      ["Query all buffers"
       (customize-set-variable 'coq-compile-auto-save 'ask-all)
       :style radio
       :selected (eq coq-compile-auto-save 'ask-all)
       :active coq-compile-before-require
       :help "Ask for all buffers"]
      ["Autosave coq buffers"
       (customize-set-variable 'coq-compile-auto-save 'save-coq)
       :style radio
       :selected (eq coq-compile-auto-save 'save-coq)
       :active coq-compile-before-require
       :help "Save all Coq buffers without confirmation, except the current one"]
      ["Autosave all buffers"
       (customize-set-variable 'coq-compile-auto-save 'save-all)
       :style radio
       :selected (eq coq-compile-auto-save 'save-all)
       :active coq-compile-before-require
       :help "Save all buffers without confirmation"]
      )
     ["Lock Ancesotors"
      coq-lock-ancestors-toggle
      :style toggle
      :selected coq-lock-ancestors
      :active coq-compile-before-require
      :help "Lock files of imported modules"]
     ["Confirm External Compilation"
      coq-confirm-external-compilation-toggle
      :style toggle
      :selected coq-confirm-external-compilation
      :active (and coq-compile-before-require
		   (not (equal coq-compile-command "")))
      :help "Confirm external compilation command, see `coq-compile-command'."]
     ["Abort Background Compilation"
      coq-par-emergency-cleanup
      :active (and coq-compile-before-require
		   coq-compile-parallel-in-background)
      :help "Abort background compilation and kill all compilation processes."])
    ""
    ["Print..." coq-Print :help "With prefix arg (C-u): Set Printing All first"]
    ["Check..." coq-Check :help "With prefix arg (C-u): Set Printing All first"]
    ["About..." coq-About :help "With prefix arg (C-u): Set Printing All first"]
    ["Other..." coq-query]
    [ "Store Response" proof-store-response-win :help "Stores the content of response buffer in a dedicated buffer"]
    [ "Store Goal" proof-store-goals-win  :help "Stores the content of goals buffer in a dedicated buffer"]
    ("OTHER QUERIES"
     ["Print Hint" coq-PrintHint t]
     ["Show ith Goal..." coq-Show t]
     ["Show ith Goal... (show implicits)" coq-Show-with-implicits t]
     ["Show ith Goal... (show all)" coq-Show-with-all t]
     ["Show Tree" coq-show-tree t]
     ["Show Proof" coq-show-proof t]
     ["Show Conjectures" coq-show-conjectures t];; maybe not so useful with editing in PG?
     ""
     ["Print..." coq-Print :help "With prefix arg (C-u): Set Printing All first"]
     ["Print... (show implicits)" coq-Print-with-implicits t]
     ["Print... (show all)" coq-Print-with-all t]
     ["Check..." coq-Check :help "With prefix arg (C-u): Set Printing All first"]
     ["Check (show implicits)..." coq-Check-show-implicits t]
     ["Check (show all)..." coq-Check-show-all t]
     ["About..." coq-About :help "With prefix arg (C-u): Set Printing All first"]
     ["About...(show implicits)" coq-About-with-implicits t]
     ["About...(show all)" coq-About-with-all t]
     ["Search..." coq-SearchConstant t]
     ["SearchRewrite..." coq-SearchRewrite t]
     ["SearchAbout (hiding principles)..." coq-SearchAbout t]
     ["SearchAbout..." coq-SearchAbout-all t]
     ["SearchPattern..." coq-SearchIsos t]
     ["Locate constant..." coq-LocateConstant t]
     ["Locate Library..." coq-LocateLibrary t]
     ["Pwd" coq-Pwd t]
     ["Inspect..." coq-Inspect t]
     ["Print Section..." coq-PrintSection t]
     ""
     ["Locate notation..." coq-LocateNotation t]
     ["Print Implicit..." coq-Print t]
     ["Print Scope/Visibility..." coq-PrintScope t])
    ("OPTIONS"
     ["Set Printing All" coq-set-printing-all t]
     ["Unset Printing All" coq-unset-printing-all t]
     ["Set Printing Implicit" coq-set-printing-implicit t]
     ["Unset Printing Implicit" coq-unset-printing-implicit t]
     ["Set Printing Coercions" coq-set-printing-coercions t]
     ["Unset Printing Coercions" coq-unset-printing-coercions t]
     ["Set Printing Compact Contexts" coq-set-printing-implicit t]
     ["Unset Printing Compact Contexts" coq-unset-printing-implicit t]
     ["Set Printing Synth" coq-set-printing-synth t]
     ["Unset Printing Synth" coq-unset-printing-synth t]
     ["Set Printing Universes" coq-set-printing-universes t]
     ["Unset Printing Universes" coq-unset-printing-universes t]
     ["Set Printing Unfocused" coq-set-printing-unfocused t]
     ["Unset Printing Unfocused" coq-unset-printing-unfocused t]
     ["Set Printing Wildcards" coq-set-printing-wildcards t]
     ["Unset Printing Wildcards" coq-unset-printing-wildcards t]
     ["Set Printing Width" coq-ask-adapt-printing-width-and-show t])))

(setq-default coq-menu-entries
  (append coq-menu-common-entries
  `(
    ""
    ("INSERT"
     ["Intros (smart)" coq-insert-intros :help "Insert \"intros h1 .. hn.\" where hi are the default names given by Coq."]
     ""
     ["Tactic (interactive)" coq-insert-tactic t]
     ["Tactical (interactive)" coq-insert-tactical t]
     ["Command (interactive)" coq-insert-command t]
     ["Term (interactive)" coq-insert-term t]
     ""
     ,coq-tactics-menu
     ,coq-tacticals-menu
     ,coq-commands-menu
     ,coq-terms-menu
     ""
     ["Module/Section (smart)" coq-insert-section-or-module t]
     ["Require (smart)" coq-insert-requires t])
    ""
    ("ABBREVS"
     ["Expand At Point" expand-abbrev t]
     ["Unexpand Last" unexpand-abbrev t]
     ["List Abbrevs" list-abbrevs t]
     ["Edit Abbrevs" edit-abbrevs t]
     ["Abbrev Mode" abbrev-mode
      :style toggle
      :selected (and (boundp 'abbrev-mode) abbrev-mode)])
    ""
    ("COQ PROG (ARGS)"
     ["Use project file" coq-toggle-use-project-file
      :style toggle
      :selected (and (boundp 'coq-use-project-file) coq-use-project-file)
      ]
     ["Set Coq Prog *persistently*" coq-ask-insert-coq-prog-name t]
     ["help" coq-local-vars-list-show-doc t]
     ["Compile" coq-Compile t]))))

(setq-default coq-help-menu-entries
  '(["help on setting prog name persistently for a file" 
     coq-local-vars-list-show-doc t]))

(setq-default coq-other-buffers-menu-entries coq-menu-common-entries)

(provide 'coq-abbrev)
