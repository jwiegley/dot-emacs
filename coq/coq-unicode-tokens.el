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
(defconst coq-charref-format nil)
(defconst coq-token-prefix nil)
(defconst coq-token-suffix nil)
(defconst coq-token-match nil)
(defconst coq-hexcode-match nil)

(defcustom coq-token-name-alist nil
  ;; an alist of token name, unicode char sequence
  "Table mapping Coq tokens to Unicode strings.

You can adjust this table to add entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

When a file is visited, tokens are replaced by the strings
in this table.  When the file is saved, the reverse is done.
The string mapping can be anything, but should be such that
tokens can be uniquely recovered from a decoded text; otherwise
results will be undefined when files are saved."
  :type '(repeat (cons (string :tag "Token name")
		       (string :tag "Unicode string")))
  :set 'proof-set-value
  :group 'isabelle
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
    ("\forall" . "∀")
    ("\exists" . "∃")
    ("\nat" . "ℕ")
    ("\int" . "ℤ")
    ("\rat" . "ℚ")
    ("\real" . "ℝ")
    ("\complex" . "ℂ")
    ("\euro" . "€")
    ("\yen" . "¥")
    ("\cent" . "¢"))
  "Shortcut key sequence table for Unicode strings.

You can adjust this table to add more entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

These shortcuts are only used for input; no reverse conversion is
performed.  But if tokens exist for the target of shortcuts, they
will be used on saving the buffer."
  :type '(repeat (cons (string :tag "Shortcut sequence")
		       (string :tag "Unicode string")))
  :set 'proof-set-value
  :group 'isabelle
  :tag "Coq Unicode Token Mapping")

  




(provide 'coq-unicode-tokens)

;;; coq-unicode-tokens.el ends here
