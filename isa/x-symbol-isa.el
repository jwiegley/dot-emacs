;; Canonical file for token language file for PG/isar.

(require 'x-symbol-isabelle)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; x-symbol support for Isabelle PG, provided by David von Oheimb.
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file x-symbol-isabelle.el
;;

(setq proof-xsym-extra-modes '(thy-mode)
      proof-xsym-activate-command
      "change print_mode (insert (op =) \"xsymbols\");"
      proof-xsym-deactivate-command
      "change print_mode (remove (op =) \"xsymbols\");")



(provide 'x-symbol-isa)
