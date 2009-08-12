;;; -*- coding: utf-8; -*-
;; coq-unicode-tokens.el --- (No) Tokens for Unicode Tokens package
;;
;; Copyright(C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This file is loaded by `proof-unicode-tokens.el'.
;;
;; It sets the variables defined at the top of unicode-tokens.el,
;; unicode-tokens-<foo> is set from coq-<foo>.  See the corresponding
;; variable for documentation.
;;
;; For Coq, there is no dedicated token syntax, it's preferable to
;; use UTF-8 notation directly (see utf8.v).  So the configuration
;; here just makes some handy shortcuts for symbol input.
;;

(defconst coq-token-format "%s")
(defconst coq-token-match nil)
(defconst coq-hexcode-match nil)

(defcustom coq-token-symbol-map
  '(;; Greek letters
    ("alpha" "α")
    ("beta" "β")
    ("gamma" "γ")
    ("delta" "δ")
    ("epsilon" "ε") ; actually varepsilon (some is epsilon)
    ("zeta" "ζ")
    ("eta" "η")
    ("theta" "θ")
    ("iota" "ι")
    ("kappa" "κ")
    ("lambda" "λ")
    ("mu" "μ")
    ("nu" "ν")
    ("xi" "ξ")
    ("pi" "π")
    ("rho" "ρ")
    ("sigma" "σ")
    ("tau" "τ")
    ("upsilon" "υ")
    ("phi" "ϕ")
    ("chi" "χ")
    ("psi" "ψ")
    ("omega" "ω")
    ("Gamma" "Γ")
    ("Delta" "Δ")
    ("Theta" "Θ")
    ("Lambda" "Λ")
    ("Xi" "Ξ")
    ("Pi" "Π")
    ("Sigma" "Σ")
    ("Upsilon" "Υ")
    ("Phi" "Φ")
    ("Psi" "Ψ")
    ("Omega" "Ω")
    ;; logic
    ("forall" "∀")
    ("exists" "∃")
    ("nat" "ℕ")
    ("real" "ℝ")
    ;; symbols without utf8.v  (but also without context)
    ("=>" "⇒")
    (":=" "≔")
    ("\/" "∨")
    ("/\\" "∧")
    ("->" "→")
    ("~"  "⌉"))
  ;; an alist of token name, unicode char sequence
  "Table mapping Coq tokens to Unicode strings.

You can adjust this table to add entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

When a file is visited, tokens are replaced by the strings
in this table.  When the file is saved, the reverse is done.
The string mapping can be anything, but should be such that
tokens can be uniquely recovered from a decoded text; otherwise
results will be undefined when files are saved."
  :type '(repeat (list (string :tag "Token name")
		       (string :tag "Unicode string")))
  :set 'proof-set-value
  :group 'coq
  :tag "Coq Unicode Token Mapping")


(defcustom coq-shortcut-alist
  '(; short cut, unicode string
    ("<>" . "⋄")
    ("|>" . "⊳")
    ("\\/" . "∨")
    ("/\\" . "∧")
    ("+O" . "⊕")
    ("-O" . "⊖")
    ("xO" . "⊗")
    ("/O" . "⊘")
    (".O" . "⊙")
    ("|+" . "†")
    ("|++" . "‡")
    ("<=" . "≤")
    ("|-" . "⊢")
    (">=" . "≥")
    ("-|" . "⊣")
    ("||" . "∥")
    ("==" . "≡")
    ("~=" . "≃")
    ("~~~" . "≍")
    ("~~" . "≈")
    ("~==" . "≅")
    ("|<>|" . "⋈")
    ("|=" . "⊨")
    ("=." . "≐")
    ("_|_" . "⊥")
    ("</" . "≮")
    (">=/" . "≱")
    ("=/" . "≠")
    ("==/" . "≢")
    ("~/" . "≁")
    ("~=/" . "≄")
    ("~~/" . "≉")
    ("~==/" . "≇")
    ("<-" . "←")
    ("<=" . "⇐")
    ("->" . "→")
    ("=>" . "⇒")
    ("<->" . "↔")
    ("<=>" . "⇔")
    ("|->" . "↦")
    ("<--" . "⟵")
    ("<==" . "⟸")
    ("-->" . "⟶")
    ("==>" . "⟹")
    ("<==>" . "⟷")
    ("|-->" . "⟼")
    ("<--" . "←⎯")
    ("<-->" . "⟷")
    ("<<" . "⟪")
    ("[|" . "⟦")
    (">>" . "⟫")
    ("|]" . "⟧")
    ("``" . "”")
    ("''" . "“")
    ("--" . "–")
    ("---" . "—")
    ("''" . "″")
    ("'''" . "‴")
    ("''''" . "⁗")
    (":=" . "≔")
    ;; some word shortcuts, started with backslash otherwise
    ;; too annoying, perhaps.
    ("\\int" . "ℤ")
    ("\\rat" . "ℚ")
    ("\\complex" . "ℂ")
    ("\\euro" . "€")
    ("\\yen" . "¥")
    ("\\cent" . "¢"))
  "Shortcut key sequence table for Unicode strings.

You can adjust this table to add more entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

These shortcuts are only used for input; no reverse conversion is
performed.  This means that the target strings need to have a defined 
meaning to be useful."
  :type '(repeat (cons (string :tag "Shortcut sequence")
		       (string :tag "Unicode string")))
  :set 'proof-set-value
  :group 'isabelle
  :tag "Coq Unicode Input Shortcuts")

  
;;
;; Controls
;;

(defconst coq-control-char-format-regexp 
  ;; FIXME: fix Coq identifier syntax below
  "\\(\s*%s\s*\\)\\([a-zA-Z0-9']+\\)")

(defconst coq-control-char-format " %s ")

(defconst coq-control-characters 
  '(("Subscript" "__" sub) 
    ("Superscript" "^^" sup)))

(defconst coq-control-region-format-regexp "\\(\s*%s\{\\)\\([^}]*\\)\\(\}\s*\\)")

(defconst coq-control-regions 
  '(("Subscript" "," "" sub)
    ("Superscript" "^" "" sup)
    ("Bold" "BOLD" "" bold)
    ("Italic" "ITALIC" "" italic)
    ("Script" "SCRIPT" "" script)
    ("Frakt"  "FRACT" "" frakt)
    ("Roman"  "ROMAN" "" serif)))



(defcustom coq-fontsymb-properties 
  '((sub      (display (raise -0.4)))
    (sup      (display (raise 0.4)))
    (bold     (face (:weight bold)))
    (italic   (face (:slant italic)))
    (script   (face unicode-tokens-script-font-face))
    (frakt    (face unicode-tokens-fraktur-font-face))
    (serif    (face unicode-tokens-serif-font-face)))
  "Mapping from symbols to property lists used for markup scheme."
  :set 'proof-set-value)





(provide 'coq-unicode-tokens)

;;; coq-unicode-tokens.el ends here
