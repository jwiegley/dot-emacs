;;
;; $Id$
;; 

(customize-set-variable
 'isabelle-isar-prog-name
 (concat (getenv "ISABELLE") " " (getenv "PROOFGENERAL_LOGIC")))

(customize-set-variable 'proof-assistant-table '((lego	"LEGO"		"\\.l$")(coq	"Coq"		"\\.v$") (isar "Isabelle/Isar" "\\.thy$")))


(customize-set-variable 'proof-script-indent t)
