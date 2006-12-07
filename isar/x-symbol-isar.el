;; Canonical file for token language file for PG/isar.

(require 'x-symbol-isabelle)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; x-symbol support
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file isar/x-symbol-isabelle.el
;;

(setq
 proof-xsym-activate-command
 (isar-markup-ml 
  "change print_mode (insert (op =) \"xsymbols\")")
 proof-xsym-deactivate-command
 (isar-markup-ml 
  "change print_mode (remove (op =) \"xsymbols\")"))


(provide 'x-symbol-isar)
