;; Canonical file for token language file for PG/isar.

(require 'x-symbol-isabelle)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; x-symbol support
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file isa/x-symbol-isabelle.el
;;

(setq
 proof-xsym-activate-command
 (isar-markup-ml 
  "print_mode := ([\"xsymbols\", \"symbols\"] @ ! print_mode)")
 proof-xsym-deactivate-command
 (isar-markup-ml 
  "print_mode := (Library.gen_rems (op =) (! print_mode, [\"xsymbols\", \"symbols\"]))"))


(provide 'x-symbol-isar)
