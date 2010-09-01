;;; coq-abbrev.el --- coq abbrev table and menus for ProofGeneral mode
;;
;; Copyright (C) 1994-2009 LFCS Edinburgh.
;; Authors: Healfdene Goguen, Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

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
	    ["Intros (smart)" coq-insert-intros t])
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
    (setq save-abbrevs nil)
    (message "Coq default abbrevs loaded")
    ))

(unless noninteractive
  (coq-install-abbrevs))
;;;;;

;; The coq menu mainly built from tables

(defpgdefault menu-entries
  `(
    ["Toggle 3 windows mode" proof-three-window-toggle t]
     ""
    ["Print..." coq-Print t]
    ["Check..." coq-Check t]
    ["About..." coq-About t]
    [ "Store response" proof-store-response-win t]
    [ "Store goal" proof-store-goals-win t]
    ("OTHER QUERIES"
     ["Print Hint" coq-PrintHint t]
     ["Show ith goal..." coq-Show t]
     ["Show Tree" coq-show-tree t]
     ["Show Proof" coq-show-proof t]
     ["Show Conjectures" coq-show-conjectures t];; maybe not so useful with editing in PG?
     ""
     ["Print..." coq-Print t]
     ["Check..." coq-Check t]
     ["About..." coq-About t]
     ["Search..." coq-SearchConstant t]
     ["SearchRewrite..." coq-SearchRewrite t]
     ["SearchAbout..." coq-SearchAbout t]
     ["SearchPattern..." coq-SearchIsos t]
     ["Locate constant..." coq-LocateConstant t]
     ["Locate Library..." coq-LocateLibrary t]
     ["Pwd" coq-Pwd t]
     ["Inspect..." coq-Inspect t]
     ["Print Section..." coq-PrintSection t]
     ""
     ["Locate notation..." coq-LocateNotation t]
     ["Print Implicit..." coq-Print t]
     ["Print Scope/Visibility..." coq-PrintScope t]
     )
     ""
    ("INSERT"
     ""
     ["tactic (interactive)" coq-insert-tactic t]
     ,coq-tactics-menu
     ["tactical (interactive)" coq-insert-tactical t]
     ,coq-tacticals-menu
     ""
     ["command (interactive)" coq-insert-command t]
     ,coq-commands-menu
     ""
     ["term (interactive)" coq-insert-term t]
     ,coq-terms-menu
     ""
     ["Module/Section (smart)" coq-insert-section-or-module t]
     ["Require (smart)" coq-insert-requires t])
    ""
    ("ABBREVS"
     ["Expand at point" expand-abbrev t]
     ["Unexpand last" unexpand-abbrev t]
     ["List abbrevs" list-abbrevs t]
     ["Edit abbrevs" edit-abbrevs t]
     ["Abbrev mode" abbrev-mode
      :style toggle
      :selected (and (boundp 'abbrev-mode) abbrev-mode)])
    ""
    ("COQ PROG (ARGS)"
     ["Set coq prog *persistently*" coq-ask-insert-coq-prog-name t]
     ["help on setting persistently" coq-local-vars-list-show-doc t]
     ["Compile" coq-Compile t])
    ))

(defpgdefault help-menu-entries
  '(["help on setting prog name persistently for a file" 
     coq-local-vars-list-show-doc t]))


(provide 'coq-abbrev)
