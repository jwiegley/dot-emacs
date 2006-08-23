;; default abbrev table
; This is for coq V8, you should test coq version before loading

(require 'proof)
(require 'coq-syntax)

(defun holes-show-doc () 
  (interactive)
  (describe-variable 'holes-doc))

(defun coq-local-vars-list-show-doc ()
  (interactive)
  (describe-variable 'coq-local-vars-doc))



;; Computes the max length of strings in a list
(defun max-length-db (db)
  (let ((l db) (res 0))
    (while l
      (let ((lgth (length (car (car l)))))
	(setq res (max lgth res))
	(setq l (cdr l))))
    res))



(defun coq-build-menu-from-db-internal (db lgth menuwidth)
  "Take a keyword database DB and return insertion menus for them."
  (let ((l db) (res ()) (size lgth)
	(keybind-abbrev (substitute-command-keys " \\[expand-abbrev]")))
    (while (and l (> size 0))
      (let* ((hd (car l))(tl (cdr l))	; hd is a list of length 3 or 4
	     (e1 (car hd)) (tl1 (cdr hd)) ; e1 = menu entry
	     (e2 (car tl1)) (tl2 (cdr tl1)) ; e2 = abbreviation
	     (e3 (car tl2)) (tl3 (cdr tl2)) ; e3 = completion 
	     (e4 (car-safe tl3)) (tl4 (cdr-safe tl3)) ; e4 = state changing
	     (e5 (car-safe tl4)) (tl5 (cdr-safe tl4)) ; e5 = colorization string
	     (e6 (car-safe tl5))	; e6 = function for smart insertion
	     (e7 (car-safe (cdr-safe tl5))) ; e7 = if non-nil : hide in menu 
	     (entry-with (max (- menuwidth (length e1)) 0))
	     (spaces (make-string entry-with ? ))
	     ;;(restofmenu (coq-build-menu-from-db-internal tl (- size 1) menuwidth))
	     )
	(when (not e7)			; if not hidden
	  (let ((menu-entry 
		 (vector 
		  ;; menu entry label
		  (concat e1 (if (not e2) "" (concat spaces "(" e2 keybind-abbrev ")")))
		   ;;insertion function if present otherwise insert completion
		   (if e6 e6 `(holes-insert-and-expand ,e3))
		   t)))
	    (setq res (nconc res (list menu-entry)))));; append *in place*
	(setq l tl)
	(setq size (- size 1))))
    res))


(defun coq-build-title-menu (l size)
    (concat (car-safe (car-safe l))
	  " ... "
	  (car-safe (car-safe (nthcdr (- size 1) l)))))


(defun coq-build-menu-from-db (db &optional size)
  "Take a keyword database DB and return a list of insertion menus for
 them.
Submenus contain SIZE entries (default 30)."
  (let* ((l db) (res ())
	(wdth (+ 2 (max-length-db coq-tactics-db)))
	(sz (or size 30)) (lgth (length l)))
    (while l
      (if (<= lgth sz)
	  (setq res 
		(nconc res (list (cons (coq-build-title-menu l lgth)
				       (coq-build-menu-from-db-internal l lgth wdth)))))
	(setq res 
	      (nconc res (list (cons (coq-build-title-menu l sz)
				     (coq-build-menu-from-db-internal l sz wdth))))))
      (setq l (nthcdr sz l))
      (setq lgth (length l)))
    res))

(defun coq-build-abbrev-table-from-db (db)
  (let ((l db) (res ()))
    (while l
      (let* ((hd (car l))(tl (cdr l))	; hd is a list of length 3 or 4
	     (e1 (car hd)) (tl1 (cdr hd)) ; e1 = menu entry
	     (e2 (car tl1)) (tl2 (cdr tl1)) ; e2 = abbreviation
	     (e3 (car tl2)) (tl3 (cdr tl2)) ; e3 = completion 
	     )
	(when e2 (setq res (nconc res (list `(,e2 ,e3 holes-abbrev-complete)))))
	(setq l tl)))
    res))

(defconst coq-tactics-menu 
  (append '("INSERT TACTICS" 
	    ["Intros (smart)" coq-insert-intros t])
	  (coq-build-menu-from-db coq-tactics-db)))

(defconst coq-tactics-abbrev-table 
  (coq-build-abbrev-table-from-db coq-tactics-db))

(defconst coq-tacticals-menu 
  (append '("INSERT TACTICALS" 
	    ["Intros (smart)" coq-insert-intros t])
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
	    ["Match!" coq-insert-match t])
	  (coq-build-menu-from-db coq-terms-db)))

(defconst coq-terms-abbrev-table 
  (coq-build-abbrev-table-from-db coq-terms-db))


;;; The abbrev table built from keywords tables
;#s and @{..} are replaced by holes by holes-abbrev-complete
(if (boundp 'holes-abbrev-complete)
	 ()
  (define-abbrev-table 'coq-mode-abbrev-table
    (append coq-tactics-abbrev-table
	    coq-tacticals-abbrev-table
	    coq-commands-abbrev-table
	    coq-terms-abbrev-table)))

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
      ["Search Rewrite..." coq-SearchRewrite t]
      ["Search About..." coq-SearchAbout t]
      ["Search isos/pattern..." coq-SearchIsos t]
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
     ["Set coq prog name *for this file persistently*" coq-ask-insert-coq-prog-name t]
     ["help on setting prog name persistently for a file" coq-local-vars-list-show-doc t]
     ))

;; da: Moved this from the main menu to the Help submenu.  
;; It also appears under Holes, anyway.
(defpgdefault help-menu-entries
  '(["Tell me about holes?" holes-show-doc t]))


(provide 'coq-abbrev)

