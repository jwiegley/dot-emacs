;; isa-syntax.el Syntax expressions for Isabelle
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;;
(require 'proof-syntax)

;; character syntax

(defun isa-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ ".")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  ".")
  (modify-syntax-entry ?>  ".")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?.  "w")
  (modify-syntax-entry ?_  "w")
  (modify-syntax-entry ?\' "w")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(defun isa-init-output-syntax-table ()
  "Set appropriate values for syntax table for Isabelle output."
  (isa-init-syntax-table)
  ;; ignore strings so font-locking works
  ;; inside them
  (modify-syntax-entry ?\" " ")
  (modify-syntax-entry ?\* ".")
  (modify-syntax-entry ?\( "()")
  (modify-syntax-entry ?\) ")(")
  (modify-syntax-entry ?\{ "(}")
  (modify-syntax-entry ?\} "){"))

;;
;; Syntax for font-lock and other features
;;

;; Note: this command-keyword recognition of the proof script isn't
;; good enough for Isabelle, since we can have arbitrary ML code
;; around.
;; Alternatives: 
;; 1) propose a restricted language consisting of the interactive
;; commands.  Or try Markus Wenzel's Isar proof language!
;; 2) add hooks from Isabelle to say "I've just seen a goal command"
;; or "I've just seen a tactic".  This would allow more accurate
;; counting of undos.  We could even approximate this without hooks,
;; by examining the proof state output carefully.
;;

;; FIXME da:  here are some examples of input failures I've
;; found in real proofs:
;;
;;   val lemma = result() RS spec RS mp;
;;
;; Not recognized as a qed command, and therefore assumed 
;; to be an undoable tactic command.
;;

(defgroup isa-syntax nil
  "Customization of Isabelle syntax for proof mode"
  :group 'isa-settings)

(defcustom isa-keywords-defn
  '("bind_thm" "bind_thms")
  "Isabelle keywords for definitions"
  :group 'isa-syntax
  :type '(repeat string))

;; isa-keywords-goal is used to manage undo actions
(defcustom isa-keywords-goal
  '("Goal" "Goalw" "goal" "goalw" "goalw_cterm" "atomic_goal" "atomic_goalw")
  "Isabelle commands to begin an interactive proof"
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-save
  '("qed" "qed_spec_mp" "no_qed")
  ;; Related commands, but having different types, so PG
  ;; won't bother support them:
  ;; "uresult" "bind_thm" "store_thm"
    "Isabelle commands to extract the proved theorem"
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-commands
  '("by" "byev"
    "ba" "br" "be" "bd" "brs" "bes" "bds"
    "chop" "choplev" "back" "undo" "ProofGeneral.repeat_undo"
    "fa" "fr" "fe" "fd" "frs" "fes" "fds"
    "bw" "bws" "ren"
    ;; batch proofs
    "prove_goal" "qed_goal" "prove_goalw" "qed_goalw" "prove_goalw_cterm")
  "Isabelle command keywords"
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-sml
  '("abstype" "and" "andalso" "as" "case" "datatype" "do" "else" "end"
    "eqtype" "exception" "fn" "fun" "functor" "handle" "if" "in" "include"
    "infix" "infixr" "let" "local" "nonfix" "of" "op" "open" "orelse"
    "raise" "rec" "sharing" "sig" "signature" "struct" "structure" "then"
    "type" "val" "while" "with" "withtype")
    "Standard ML keywords that are nice to have coloured."
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keyword-symbols
  '("=" "=>" "|" ";" "," "(" ")" "-" "." "->" ":" "{" "}" "[" "]" "#")
    "Symbols that are nice to have in bold."
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-sml-names-keywords
  '("fun" "val" "structure" "signature" "functor")
    "Keywords that then define a name."
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-sml-typenames-keywords
  '("type" "eqtype" "datatype")
    "Keywords that define a type, this is only terminated by a '=' or '\n'."
  :group 'isa-syntax
  :type '(repeat string))


;; NB: this means that any adjustments above by customize will
;; only have effect in next session.
(defconst isa-keywords
  (append isa-keywords-goal isa-keywords-save
	  isa-keywords-defn isa-keywords-commands 
          isa-keywords-sml)
  "All keywords in a Isabelle script")

(defconst isa-keywords-proof-commands
  (append isa-keywords-goal isa-keywords-save isa-keywords-commands)
  "Actual Isabelle proof script commands")

;; The most common Isabelle/Pure tacticals
(defconst isa-tacticals
  '("ALLGOALS" "DETERM" "EVERY" "EVERY'" "FIRST" "FIRST'" "FIRSTGOAL"
    "ORELSE" "ORELSE'" "REPEAT" "REPEAT" "REPEAT1" "REPEAT_FIRST"
    "REPEAT_SOME" "SELECT_GOAL" "SOMEGOAL" "THEN" "THEN'" "TRY" "TRYALL"))


;; ----- regular expressions

(defconst isa-id "\\([A-Za-z][A-Za-z0-9'_]*\\)")
(defconst isa-idx (concat isa-id "\\(\\.[0-9]+\\)?"))

(defconst isa-ids (proof-ids isa-id "[ \t]*")
  "Matches a sequence of identifiers separated by whitespace.")

(defconst isa-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"")

(defcustom isa-save-command-regexp
  (proof-regexp-alt
   (proof-anchor-regexp (proof-ids-to-regexp isa-keywords-save))
   ;; match val ... = result blah
   (proof-anchor-regexp
    (concat
     (proof-ids-to-regexp '("val")) ".+=\\s-*"
     "\\(" (proof-ids-to-regexp isa-keywords-save) "\\)")))
  "Regular expression used to match a qed/result."
  :type 'regexp
  :group 'isabelle-config)


;; CHECKED
(defconst isa-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp isa-keywords-save)
	  "\\)\\s-+\"\\(" isa-id "\\)\"\\s-*;"))

(defcustom isa-goal-command-regexp
  (proof-regexp-alt
   (proof-anchor-regexp (proof-ids-to-regexp isa-keywords-goal))
   ;; match val ... = goal blah
   (proof-anchor-regexp
    (concat
     (proof-ids-to-regexp '("val")) ".+=\\s-*"
     "\\(" (proof-ids-to-regexp isa-keywords-goal) "\\)")))
  "Regular expression used to match a goal."
  :type 'regexp
  :group 'isabelle-config)

(defconst isa-string-regexp
  (concat "\\s-*\"\\(" isa-id "\\)\"\\s-*")
  "Regexp matching ML strings, with contents bracketed.")

(defconst isa-goal-with-hole-regexp
  (concat "\\("
	  ;; Don't bother with "val xxx = prove_goal blah".
	  (proof-ids-to-regexp '("qed_goal"))
	  "\\)" isa-string-regexp)
  "Regexp matching goal commands in Isabelle which name a theorem")


(defconst isa-proof-command-regexp
  (proof-ids-to-regexp isa-keywords-proof-commands)
  "Regexp to match proof commands, with no extra output (apart from proof state)")


;; ----- Isabelle inner syntax hilite

(defface isabelle-class-name-face
  '((((type x) (class color) (background light))   
     (:foreground "red"))
    (((type x) (class color) (background dark))   
     (:foreground "red3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-tfree-name-face
  '((((type x) (class color) (background light))   
     (:foreground "purple"))
    (((type x) (class color) (background dark))   
     (:foreground "purple3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-tvar-name-face
  '((((type x) (class color) (background light))   
     (:foreground "purple"))
    (((type x) (class color) (background dark))   
     (:foreground "purple3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-free-name-face
  '((((type x) (class color) (background light))   
     (:foreground "blue"))
    (((type x) (class color) (background dark))   
     (:foreground "blue3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-bound-name-face
  '((((type x) (class color) (background light))   
     (:foreground "green4"))
    (((type x) (class color) (background dark))   
     (:foreground "green"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-var-name-face
  '((((type x) (class color) (background light))   
     (:foreground "darkblue"))
    (((type x) (class color) (background dark))   
     (:foreground "blue3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defconst isabelle-class-name-face 'isabelle-class-name-face)
(defconst isabelle-tfree-name-face 'isabelle-tfree-name-face)
(defconst isabelle-tvar-name-face 'isabelle-tvar-name-face)
(defconst isabelle-free-name-face 'isabelle-free-name-face)
(defconst isabelle-bound-name-face 'isabelle-bound-name-face)
(defconst isabelle-var-name-face 'isabelle-var-name-face)

;; special face for key symbols, make them bold
(defface isa-font-lock-sml-symbol-face
  '((((class color) (background dark)) (:bold t))
    (((class color) (background light)) (:bold t))
    (((class grayscale) (background light)) (:bold t))
    (((class grayscale) (background dark)) (:bold t))
    (t (:bold t)))
  "SML symbol/character highlightling face"
  :group 'proof-faces)

;; regexp for finding function/variable/struct/sig/functor names
(defconst isa-sml-function-var-names-regexp 
  (concat "\\(" (proof-ids-to-regexp isa-sml-names-keywords) "\\)[\ \t]*\\(" isa-id "\\)"))

;; regexp for finding type names, note that types may be compound, 
;; thus this needs to be separate from function names
(defconst isa-sml-type-names-regexp 
  (concat "\\(" (proof-ids-to-regexp isa-sml-typenames-keywords) "\\)\\([^\n=]*\\)[\n=]"))

;; make stuff to be syntax colourd....
(defvar isa-font-lock-keywords-1
  (list
   (cons (proof-ids-to-regexp isa-keywords) 'font-lock-keyword-face)
   (cons (regexp-opt isa-keyword-symbols) 'isa-font-lock-sml-symbol-face)
   (list isa-sml-function-var-names-regexp 2 'font-lock-function-name-face 'append' t)
   (list isa-sml-type-names-regexp 2 'font-lock-function-name-face 'append' t)
   (cons (proof-ids-to-regexp isa-tacticals) 'proof-tacticals-name-face)
   (list isa-goal-with-hole-regexp 2 'font-lock-function-name-face)
   (list isa-save-with-hole-regexp 2 'font-lock-function-name-face)))

(defvar isa-output-font-lock-keywords-1
  (list
   (cons (concat "\351" isa-id "\350") 'isabelle-class-name-face)
   (cons (concat "\352'" isa-id "\350") 'isabelle-tfree-name-face)
   (cons (concat "\353\\?'" isa-idx "\350") 'isabelle-tvar-name-face)
   (cons (concat "\354" isa-id "\350") 'isabelle-free-name-face)
   (cons (concat "\355" isa-id "\350") 'isabelle-bound-name-face)
   (cons (concat "\356\\?" isa-idx "\350") 'isabelle-var-name-face)
   (cons (concat "\357\\?" isa-idx "\350") 'proof-declaration-name-face)
   )
  "*Font-lock table for Isabelle terms.")

(defvar isa-goals-font-lock-keywords 
  (append
   (list 
    "^Level [0-9].*"
    "^No subgoals!$"
    "^Variables:$"
    "^Constants:$"
    "\\s-*[0-9][0-9]?\\. ")
   isa-output-font-lock-keywords-1)
  "*Font-lock table for Isabelle goals output.")


;; ----- indentation

(defconst isa-indent-any-regexp
  (proof-regexp-alt (proof-ids-to-regexp isa-keywords) "\\s(" "\\s)"))
(defconst isa-indent-inner-regexp
  (proof-regexp-alt "\\s(" "\\s)"))
(defconst isa-indent-enclose-regexp
  (proof-ids-to-regexp isa-keywords-save))
(defconst isa-indent-open-regexp
  (proof-regexp-alt (proof-ids-to-regexp isa-keywords-goal) "\\s("))
(defconst isa-indent-close-regexp
  (proof-regexp-alt (proof-ids-to-regexp isa-keywords-save) "\\s)"))

(provide 'isa-syntax)
