;;
;; $Id$
;; 

(customize-set-variable
 'isabelle-prog-name
 (concat (getenv "ISABELLE") " " (getenv "PROOFGENERAL_LOGIC")))

(customize-set-variable
 (if (equal (getenv "PROOFGENERAL_ASSISTANTS") "isa")
     'isa-x-symbol-enable
   'isar-x-symbol-enable)
 (equal (getenv "PROOFGENERAL_XSYMBOL") "true"))
