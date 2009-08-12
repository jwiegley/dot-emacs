;;; -*- coding: utf-8; -*-
;; isar-unicode-tokens.el --- Tokens for Unicode Tokens package
;;
;; Copyright(C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This file is loaded by proof-auxmodes.el for proof-unicode-tokens.el.
;;
;; It sets the variables defined at the top of unicode-tokens.el,
;; unicode-tokens-<foo> is set from isar-<foo>.  See the corresponding
;; variable for documentation.
;;

(require 'proof-unicode-tokens)

;;
;; Controls
;;

(defconst isar-control-region-format-regexp
  "\\(\\\\<\\^%s>\\)\\(.*?\\)\\(\\\\<\\^%s>\\)")

(defconst isar-control-char-format-regexp 
  "\\(\\\\<\\^%s>\\)\\([^\\]\\|\\\\<[A-Za-z]+>\\)")

(defconst isar-control-char-format "\\<^%s>")

(defconst isar-control-characters
  '(("Subscript" "sub" sub) 
    ("Id subscript" "isub" sub)
    ("Superscript" "sup" sup) 
    ("Id superscript" "isup" sup)
    ("Loc" "loc" loc)
    ("Bold" "bold" bold) 
    ("Italic" "italic" italic))) ; unofficial

(defconst isar-control-regions
  '(("Subscript" "bsub" "esub" sub)
    ("Superscript" "bsup" "esup" sup) 
    ; unofficial:
    ("Bold" "bbold" "ebold" bold)
    ("Italic" "bitalic" "eitalic" italic)
    ("Script" "bscript" "escript" script)
    ("Frakt" "bfrakt" "efrakt" frakt)
    ("Roman" "bserif" "eserif" serif)))
    
(defcustom isar-fontsymb-properties 
  '((sub      (display (raise -0.4)))
    (sup      (display (raise 0.4)))
    (loc      (face proof-declaration-name-face))
    (bold     (face (:weight bold)))
    (italic   (face (:slant italic)))
    (script   (face unicode-tokens-script-font-face))
    (frakt    (face unicode-tokens-fraktur-font-face))
    (serif    (face unicode-tokens-serif-font-face)))
  "Mapping from symbols to property lists used for markup scheme."
  :set 'proof-set-value)

;;
;; Symbols
;;

(defconst isar-token-format "\\<%s>")

;(defconst isar-token-variant-format-regexp 
;  "\\\\<\\(%s\\)\\([:][a-zA-Z0-9]+\\)?>") ; syntax change required
(defconst isar-token-variant-format-regexp 
  "\\\\<\\(%s\\)[0-9]*>") ; unofficial interpretation of usual syntax

(defconst isar-greek-letters-tokens
  '(("alpha" "α")
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
    ("Omega" "Ω")))

(defconst isar-misc-letters-tokens
  '(("bool" "IB")
    ("complex" "ℂ")
    ("nat" "ℕ")
    ("rat" "ℚ")
    ("real" "ℝ")
    ("int" "ℤ")))

(defconst isar-symbols-tokens
  '(("leftarrow" "←")
    ("rightarrow" "→")
    ("Leftarrow" "⇐")
    ("Rightarrow" "⇒")
    ("leftrightarrow" "↔")
    ("Leftrightarrow" "⇔")
    ("mapsto" "↦")
    ("longleftarrow" "⟵")
    ("Longleftarrow" "⟸")
    ("longrightarrow" "⟶")
    ("Longrightarrow" "⟹")
    ("longleftrightarrow" "⟷")
    ("Longleftrightarrow" "⟺")
    ("longmapsto" "⟼")
    ("midarrow" "–") ; #x002013 en dash
    ("Midarrow" "‗") ; #x002017 double low line (not mid)
    ("hookleftarrow" "↩")
    ("hookrightarrow" "↪")
    ("leftharpoondown" "↽")
    ("rightharpoondown" "⇁")
    ("leftharpoonup" "↼")
    ("rightharpoonup" "⇀")
    ("rightleftharpoons" "⇌")
    ("leadsto" "↝")
    ("downharpoonleft" "⇃")
    ("downharpoonright" "⇂")
    ("upharpoonleft" "↿")  ;; 
    ("upharpoonright" "↾") ;; overlaps restriction
    ("restriction" "↾")    ;; same as above
    ("Colon" "∷")
    ("up" "↑")
    ("Up" "⇑")
    ("down" "↓")
    ("Down" "⇓")
    ("updown" "↕")
    ("Updown" "⇕")
    ("langle" "⟨")
    ("rangle" "⟩")
    ("lceil" "⌈")
    ("rceil" "⌉")
    ("lfloor" "⌊")
    ("rfloor" "⌋")
    ("lparr" "⦇")
    ("rparr" "⦈")
    ("lbrakk" "⟦")
    ("rbrakk" "⟧")
    ("lbrace" "⦃")
    ("rbrace" "⦄")
    ("guillemotleft" "«")
    ("guillemotright" "»")
    ("bottom" "⊥")
    ("top" "⊤")
    ("and" "∧")
    ("And" "⋀")
    ("or" "∨")
    ("Or" "⋁")
    ("forall" "∀")
    ("exists" "∃")
    ("nexists" "∄")
    ("not" "¬")
    ("box" "□")
    ("diamond" "◇")
    ("turnstile" "⊢")
    ("Turnstile" "⊨")
    ("tturnstile" "⊩")
    ("TTurnstile" "⊫")
    ("stileturn" "⊣")
    ("surd" "√")
    ("le" "≤")
    ("ge" "≥")
    ("lless" "≪")
    ("ggreater" "≫")
    ("lesssim" "⪍")
    ("greatersim" "⪎")
    ("lessapprox" "⪅")
    ("greaterapprox" "⪆")
    ("in" "∈")
    ("notin" "∉")
    ("subset" "⊂")
    ("supset" "⊃")
    ("subseteq" "⊆")
    ("supseteq" "⊇")    
    ("sqsubset" "⊏")
    ("sqsupset" "⊐")
    ("sqsubseteq" "⊑")
    ("sqsupseteq" "⊒")
    ("inter" "∩")
    ("Inter" "⋂")
    ("union" "∪")
    ("Union" "⋃")
    ("squnion" "⊔")
    ("Squnion" "⨆")
    ("sqinter" "⊓")
    ("Sqinter" "⨅")
    ("setminus" "∖")
    ("propto" "∝")
    ("uplus" "⊎")
    ("Uplus" "⨄")
    ("noteq" "≠")
    ("sim" "∼")
    ("doteq" "≐")
    ("simeq" "≃")
    ("approx" "≈")
    ("asymp" "≍")
    ("cong" "≅")
    ("smile" "⌣")
    ("equiv" "≡")
    ("frown" "⌢")
    ("Join" "⨝")
    ("bowtie" "⋈")
    ("prec" "≺")
    ("succ" "≻")
    ("preceq" "≼")
    ("succeq" "≽")
    ("parallel" "∥")
    ("bar" "¦")
    ("plusminus" "±")
    ("minusplus" "∓")
    ("times" "×")
    ("div" "÷")
    ("cdot" "⋅")
    ("star" "⋆")
    ("bullet" "∙")
    ("circ" "∘")
    ("dagger" "†")
    ("ddagger" "‡")
    ("lhd" "⊲")
    ("rhd" "⊳")
    ("unlhd" "⊴")
    ("unrhd" "⊵")
    ("triangleleft" "◁")
    ("triangleright" "▷")
    ("triangle" "▵") ; or △
    ("triangleq" "≜")
    ("oplus" "⊕")
    ("Oplus" "⨁")
    ("otimes" "⊗")
    ("Otimes" "⨂")
    ("odot" "⊙")
    ("Odot" "⨀")
    ("ominus" "⊖")
    ("oslash" "⊘") 
    ("dots" "…")
    ("cdots" "⋯")
    ("Sum" "∑")
    ("Prod" "∏")
    ("Coprod" "∐")
    ("infinity" "∞")
    ("integral" "∫")
    ("ointegral" "∮")
    ("clubsuit" "♣")
    ("diamondsuit" "♢")
    ("heartsuit" "♡")
    ("spadesuit" "♠")
    ("aleph" "ℵ")
    ("emptyset" "∅")
    ("nabla" "∇")
    ("partial" "∂")
    ("Re" "ℜ")
    ("Im" "ℑ")
    ("flat" "♭")
    ("natural" "♮")
    ("sharp" "♯")
    ("angle" "∠")
    ("copyright" "©")
    ("registered" "®")
    ("hyphen" "‐")
    ("inverse" "¯¹") ; X-Symb: just "¯"
    ("onesuperior" "¹")
    ("twosuperior" "²")
    ("threesuperior" "³")
    ("onequarter" "¼")
    ("onehalf" "½")
    ("threequarters" "¾")
    ("ordmasculine" "º")
    ("ordfeminine" "ª")
    ("section" "§")
    ("paragraph" "¶")
    ("exclamdown" "¡")
    ("questiondown" "¿")
    ("euro" "€")
    ("pounds" "£")
    ("yen" "¥")
    ("cent" "¢")
    ("currency" "¤")
    ("degree" "°")
    ("amalg" "⨿")
    ("mho" "℧")
    ("lozenge" "◊")
    ("wp" "℘")
    ("wrong" "≀") ;; #x002307
;;    ("struct" "") ;; TODO
    ("acute" "´")
    ("index" "ı")
    ("dieresis" "¨")
    ("cedilla" "¸")
    ("hungarumlaut" "ʺ")
    ("spacespace" "⁣⁣") ;; two #x002063
;    ("module" "") ??
    ("some" "ϵ")
    
    ;; Not in Standard Isabelle Symbols
    ;; (some are in X-Symbols)

    ("stareq" "≛")
    ("defeq" "≝")
    ("questioneq" "≟")
    ("vartheta" "ϑ")
    ; ("o" "ø")
    ("varpi" "ϖ")
    ("varrho" "ϱ")
    ("varsigma" "ς")
    ("varphi" "φ")
    ("hbar" "ℏ")
    ("ell" "ℓ")
    ("ast" "∗")

    ("bigcirc" "◯")
    ("bigtriangleup" "△")
    ("bigtriangledown" "▽")
    ("ni" "∋")
    ("mid" "∣")
    ("notlt" "≮")
    ("notle" "≰")
    ("notprec" "⊀")
    ("notpreceq" "⋠")
    ("notsubset" "⊄")
    ("notsubseteq" "⊈")
    ("notsqsubseteq" "⋢")
    ("notgt" "≯")
    ("notge" "≱")
    ("notsucc" "⊁")
    ("notsucceq" "⋡")
    ("notsupset" "⊅")
    ("notsupseteq" "⊉")
    ("notsqsupseteq" "⋣")
    ("notequiv" "≢")
    ("notsim" "≁")
    ("notsimeq" "≄")
    ("notapprox" "≉")
    ("notcong" "≇")
    ("notasymp" "≭")
    ("nearrow" "↗")
    ("searrow" "↘")
    ("swarrow" "↙")
    ("nwarrow" "↖")
    ("vdots" "⋮")
    ("ddots" "⋱")
    ("closequote" "’")
    ("openquote" "‘")
    ("opendblquote" "”")
    ("closedblquote" "“")
    ("emdash" "—")
    ("prime" "′")
    ("doubleprime" "″")
    ("tripleprime" "‴")
    ("quadrupleprime" "⁗")
    ("nbspace" " ")
    ("thinspace" " ")
    ("notni" "∌")
    ("colonequals" "≔")
    ("foursuperior" "⁴")
    ("fivesuperior" "⁵")
    ("sixsuperior" "⁶")
    ("sevensuperior" "⁷")
    ("eightsuperior" "⁸")
    ("ninesuperior" "⁹")))

(defun isar-try-char (charset code1 code2)
  (and (charsetp charset) ; prevent error
       (char-to-string (make-char charset code1 code2))))

(defconst isar-symbols-tokens-fallbacks
  `(;; Faked long symbols
    ("longleftarrow" "←-")
    ("Longleftarrow" "⇐–")
    ("longrightarrow" "–→")
    ("Longrightarrow" "–⇒")
    ("longleftrightarrow" "←→")
    ("Longleftrightarrow" "⇐⇒")
    ("longmapsto" "❘→")
    ;; bracket composition alternatives
    ("lparr" "(|")  
    ("rparr" "|)") 
    ;; an example of using characters from another charset.
    ;; to expand this table, see output of M-x list-charset-chars
    ("lbrakk" ,(isar-try-char 'japanese-jisx0208 #x22 #x5A))
    ("rbrakk" ,(isar-try-char 'japanese-jisx0208 #x22 #x5B))
    ("lbrakk" "[|")
    ("rbrakk" "|]")
    ("lbrace" "{|")
    ("rbrace" "|}"))
  "Fallback alternatives to `isar-symbols-tokens'.
The first displayable composition will be displayed to replace the
tokens.")

(defconst isar-bold-nums-tokens 
  '(("zero" "0" bold)
    ("one" "1" bold)
    ("two" "2" bold)
    ("three" "3" bold)
    ("four" "4" bold)
    ("five" "5" bold)
    ("six" "6" bold)
    ("seven" "7" bold)
    ("eight" "8" bold)
    ("nine" "9" bold)))

(defun isar-map-letters (f1 f2 &rest symbs)
  (loop for x below 26
	for c = (+ 65 x)
	collect 
	(cons (funcall f1 c) (cons (funcall f2 c) symbs))))

(defconst isar-script-letters-tokens
  (isar-map-letters (lambda (x) (format "%c" x))
		    (lambda (x) (format "%c" x))
		    'script))

(defconst isar-roman-letters-tokens
  (isar-map-letters (lambda (x) (format "%c" x))
		    (lambda (x) (format "%c" x))
		    'serif))

(defconst isar-fraktur-letters-tokens
  (isar-map-letters (lambda (x) (format "%c%c" x x))
		    (lambda (x) (format "%c" x))
		    'frakt))

;; like defcustom, but want to evaluate default
(custom-declare-variable 'isar-token-symbol-map
   (list 'quote (append
       isar-symbols-tokens
       isar-symbols-tokens-fallbacks
       isar-greek-letters-tokens
       isar-bold-nums-tokens
       isar-script-letters-tokens
       isar-roman-letters-tokens))
  "Table mapping Isabelle symbol token names to Unicode strings.

You can adjust this table to add more entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

The token TNAME is made into the token \\< TNAME >.
The string mapping can be anything, but should be such that
tokens can be uniquely recovered from a decoded text; otherwise
results will be undefined when files are saved."
  ;; FIXME: this isn't right.
  ;; :type '(repeat (list (string :tag "Token name")
  ;; 		       (string :tag "Unicode string")
  ;; 			(choice 
  ;; 			 (const :tag "No style" nil)
  ;; 			 (list
  ;; 			  :inline t
  ;; 			  ;; could generate next automatically from
  ;; 			  ;; isar-control-regions
  ;; 			  (const :tag "Bold" bold)
  ;; 			  (const :tag "Italic" italic)
  ;; 			  (const :tag "Script" script)
  ;; 			  (const :tag "Frakt" frakt)
  ;; 			  (const :tag "Roman" serif)))))
  :set 'proof-set-value
  :group 'isabelle
  :tag "Isabelle Unicode Token Mapping")



(defconst isar-symbol-shortcuts
;    ("<>" . "\<diamond>")
;    ("|>" . "\<triangleright>")
  '(("\\/" . "\\<or>")
    ("/\\" . "\\<and>")
    ("+O" . "\\<oplus>")
    ("-O" . "\\<ominus>")
    ("xO" . "\\<otimes>")
    ("/O" . "\\<oslash>")
    (".O" . "\\<odot>")
    ("|+" . "\\<dagger>")
    ("|++" . "\\<ddagger>")
    ("<=" . "\\<le>")
    ("|-" . "\\<turnstile>")
    (">=" . "\\<ge>")
    ("-|" . "\\<stileturn>")
    ("||" . "\\<parallel>")
    ("==" . "\\<equiv>")
    ("~=" . "\\<noteq>")
    ("~:" . "\\<notin>")
;    ("~=" . "≃")
    ("~~~" . "\\<notapprox>")
    ("~~" . "\\<approx>")
    ("~==" . "\\<cong>")
    ("|<>|" . "\\<bowtie>")
    ("|=" . "\\<Turnstile>")
    ("=." . "\\<doteq>")
    ("_|_" . "\\<bottom>")
    ("</" . "\\<notle>")
    ("~>=" . "\\<notge>")
    ("==/" . "≢")
    ("~/" . "\\<notsim>")
    ("~=/" . "\\<notsimeq>")
    ("~~/" . "\\<notsimeq>")
    ("<-" . "\\<leftarrow>")
;    ("<=" . "\\<Leftarrow>")
    ("->" . "\\<rightarrow>")
    ("=>" . "\\<Rightarrow>")
    ("<->" . "\\<leftrightarrow>")
    ("<=>" . "\\<Leftrightarrow>")
    ("|->" . "\\<mapsto>") 
    ("<--" . "\\<longleftarrow>")
    ("<==" . "\\<Longleftarrow>")
    ("-->" . "\\<longrightarrow>")
    ("==>" . "\\<Longrightarrow>")
    ("<==>" . "\\<Longleftrightarrow>")
    ("|-->" . "\\<longmapsto>")
    ("<-->" . "\\<longleftrightarrow>")
    ("<<" . "\\<guillemotleft>")
    (">>" . "\\<guillemotright>")
    ("[|" . "\\<lbrakk>")
    ("|]" . "\\<rbrakk>")
    ("{|" . "\\<lbrace>")
    ("|}" . "\\<rbrace>")
    ("---" . "\\<emdash>")))

;; like defcustom, but want to evaluate default
(custom-declare-variable 'isar-shortcut-alist
   (list 'quote (append
      isar-symbol-shortcuts
      ;; LaTeX-like syntax for symbol names, easier to type
      (mapcar 
       (lambda (tokentry)
	 (cons (concat "\\" (car tokentry))
	       (format isar-token-format (car tokentry))))
       (append isar-greek-letters-tokens isar-symbols-tokens))))
  "Shortcut key sequence table for token input.

You can adjust this table to add more entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

These shortcuts are only used for input convenience; no reverse 
conversion is performed."
  :type '(repeat (cons (string :tag "Shortcut sequence")
		       (string :tag "Unicode string")))
  :set 'proof-set-value
  :group 'isabelle
  :tag "Isabelle Unicode Input Shortcuts")

  


;;
;; prover symbol support 
;;

(eval-after-load "isar" 
  '(setq 
    proof-tokens-activate-command
    (isar-markup-ml "change print_mode (insert (op =) \"xsymbols\")")
    proof-tokens-deactivate-command
    (isar-markup-ml "change print_mode (remove (op =) \"xsymbols\")")))



(provide 'isar-unicode-tokens)

;;; isar-unicode-tokens.el ends here
