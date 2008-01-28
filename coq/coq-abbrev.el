;;; coq-abbrev.el --- coq abbrev table and menus for ProofGeneral mode
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: Healfdene Goguen, Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

(require 'proof)
(require 'coq-syntax)

(defun holes-show-doc () 
  (interactive)
  (describe-variable 'holes-doc))

(defun coq-local-vars-list-show-doc ()
  (interactive)
  (describe-variable 'coq-local-vars-doc))


(defconst coq-tactics-menu 
  (append '("INSERT TACTICS" 
	    ["Intros (smart)" coq-insert-intros t])
	  (coq-build-menu-from-db (append coq-tactics-db coq-solve-tactics-db))))

(defconst coq-tactics-abbrev-table 
  (coq-build-abbrev-table-from-db (append coq-tactics-db coq-solve-tactics-db)))

(defconst coq-tacticals-menu 
  (append '("INSERT TACTICALS")
	  (coq-build-menu-from-db coq-tacticals-db)))

(defconst coq-tacticals-abbrev-table 
  (coq-build-abbrev-table-from-db coq-tacticals-db))

(defconst coq-commands-menu 
  (append '("INSERT COMMAND" 
	    ["Module/Section (smart)" coq-insert-section-or-module t]
	    ["Require (smart)" coq-insert-requires t])
	  (coq-build-menu-from-db coq-commands-db)))

(defconst coq-commands-abbrev-table 
  (coq-build-abbrev-table-from-db coq-commands-db))

(defconst coq-terms-menu 
  (append '("INSERT TERM" 
	    ["Match (smart)" coq-insert-match t])
	  (coq-build-menu-from-db coq-terms-db)))

(defconst coq-terms-abbrev-table 
  (coq-build-abbrev-table-from-db coq-terms-db))



;;; The abbrev table built from keywords tables
;#s and @{..} are replaced by holes by holes-abbrev-complete
(defun coq-install-abbrevs () 
  "install default abbrev table for coq if no other already is."
  (if (and (boundp 'coq-mode-abbrev-table)
 	   (not (equal coq-mode-abbrev-table (make-abbrev-table)))) 
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
     ["Print..." coq-Print t]
     ["Check..." coq-Check t]
     ["About..." coq-About t]
     ["insert command (interactive)" coq-insert-command t]
     ,coq-commands-menu     
     ["insert term (interactive)" coq-insert-term t]
     ,coq-terms-menu
     ["insert tactic (interactive)" coq-insert-tactic t]
     ,coq-tactics-menu
     ["insert tactical (interactive)" coq-insert-tactical t]
     ,coq-tacticals-menu

     ;; da: I added Show sub menu, not sure if it's helpful, but why not.
     ;; FIXME: submenus should be split off here.  Also, these commands
     ;; should only be available when a proof is open.
     ;; pc: I added things in the show menu and called it QUERIES
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

     ("Holes" 
      ;; da: I tidied this menu a bit.  I personally think this "trick"
      ;; of inserting strings to add documentation looks like a real
      ;; mess in menus ... I've removed it for the three below since 
      ;; the docs below appear in popup in messages anyway.
      ;; 
      ;; "Make a hole active   click on it"
      ;; "Disable a hole   click on it (button 2)"
      ;; "Destroy a hole   click on it (button 3)"
      ["Make hole at point"  holes-set-make-active-hole t]
      ["Make selection a hole"  holes-set-make-active-hole t]
      ["Replace active hole by selection"  holes-replace-update-active-hole t]
      ["Jump to active hole"  holes-set-point-next-hole-destroy t]
      ["Forget all holes in buffer"  holes-clear-all-buffer-holes t]
      ["Tell me about holes?" holes-show-doc t]
      ;; look a bit better at the bottom
      "Make hole with mouse: C-M-select"
      "Replace hole with mouse: C-M-Shift select";; da: does this one work??
      )

     ;; da: I also added abbrev submenu.  Surprising Emacs doesn't have one?
     ("Abbrevs"
      ["Expand at point" expand-abbrev t]
      ["Unexpand last" unexpand-abbrev t]
      ["List abbrevs" list-abbrevs t]
      ["Edit abbrevs" edit-abbrevs t];; da: is it OK to add edit?
      ["Abbrev mode" abbrev-mode 
       :style toggle
       :selected (and (boundp 'abbrev-mode) abbrev-mode)])
     ;; With all these submenus you have to wonder if these things belong
     ;; on the main menu.  Are they the most often used?
     ["Compile" coq-Compile t]
     ["Set coq prog *persistently*" coq-ask-insert-coq-prog-name t]
     ["help on setting persistently" coq-local-vars-list-show-doc t]
     ))

;; da: Moved this from the main menu to the Help submenu.  
;; It also appears under Holes, anyway.
(defpgdefault help-menu-entries
  '(["Tell me about holes?" holes-show-doc t]
    ["help on setting prog name persistently for a file" coq-local-vars-list-show-doc t]))


(provide 'coq-abbrev)

