;;
;; $Id$
;; 

(customize-set-variable
 'isabelle-prog-name
 (concat (getenv "ISABELLE") " " (getenv "PROOFGENERAL_LOGIC")))

(customize-set-variable 'proof-assistant-table '((isa "Isabelle" "\\.ML$\\|\\.thy$")))
