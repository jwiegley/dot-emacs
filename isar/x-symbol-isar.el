;; x-symbol-isar.el   
;; Token language "Isabelle Symbols" for package x-symbol
;;
;;  ID:         $Id$
;;  Author:     David von Oheimb
;;              Updates by Markus Wenzel, Christoph Wedler, David Aspinall.
;;  Copyright   1998 Technische Universitaet Muenchen
;;  License     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; This file is part of the Proof General distribution.

(defvar x-symbol-isar-required-fonts nil)

;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

;; NB da: these next two are also set in proof-x-symbol.el, but
;; it would be handy to be able to use this file away from PG.  
(defvar x-symbol-isar-name "Isabelle Symbol")
(defvar x-symbol-isar-modeline-name "isa")

(defcustom x-symbol-isar-header-groups-alist nil
   "*If non-nil, used in isasym specific grid/menu.
See `x-symbol-header-groups-alist'."
  :group 'x-symbol-isar
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-isar-electric-ignore 
  "[:'][A-Za-z]\\|<=\\|\\[\\[\\|\\]\\]\\|~="
  "*Additional Isabelle version of `x-symbol-electric-ignore'."
  :group 'x-symbol-isar
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)


(defvar x-symbol-isar-required-fonts nil
  "List of features providing fonts for language `isabelle'.")

(defvar x-symbol-isar-extra-menu-items nil
  "Extra menu entries for language `isabelle'.")


(defvar x-symbol-isar-token-grammar
  '(x-symbol-make-grammar
    :encode-spec (((t . "\\\\")))
    :decode-regexp "\\\\+<[A-Za-z]+>"
    :input-spec nil
    :token-list x-symbol-isar-token-list))

(defun x-symbol-isar-token-list (tokens)
  (mapcar (lambda (x) (cons x t)) tokens))

(defvar x-symbol-isar-user-table nil
  "User table defining Isabelle commands, used in `x-symbol-isar-table'.")

(defvar x-symbol-isar-generated-data nil
  "Internal.")


;;;===========================================================================
;;;  No image support
;;;===========================================================================

(defvar x-symbol-isar-master-directory  'ignore)
(defvar x-symbol-isar-image-searchpath '("./"))
(defvar x-symbol-isar-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-isar-image-file-truename-alist nil)
(defvar x-symbol-isar-image-keywords nil)


;;;===========================================================================
;;  super- and subscripts
;;;===========================================================================

;; one char: \<^sup>, \<^sub>, \<^isub>, and \<^isup>
;; spanning: \<^bsup>...\<^esup> and \<^bsub>..\<^esub>

(defcustom x-symbol-isar-subscript-matcher 'x-symbol-isar-subscript-matcher
  "Function matching super-/subscripts for language `isa'.
See language access `x-symbol-LANG-subscript-matcher'."
  :group 'x-symbol-isar
  :type 'function)

(defcustom x-symbol-isar-font-lock-regexp "\\\\<\\^[ib]?su[bp]>"
  "Regexp matching the start tag of Isabelle super- and subscripts."
  :group 'x-symbol-isar
  :type 'regexp)

(defcustom x-symbol-isar-font-lock-limit-regexp "\n\\|\\\\<\\^[be]su[bp]>"
  "Regexp matching the end of line and the start and end tags of Isabelle
spanning super- and subscripts."
  :group 'x-symbol-isar
  :type 'regexp)

(defcustom x-symbol-isar-font-lock-contents-regexp "."
  "*Regexp matching the spanning super- and subscript contents.
This regexp should match the text between the opening and closing super-
or subscript tag."
  :group 'x-symbol-isar  
  :type 'regexp)


;; the [\350-\357].\350\\|\^A[A-H].\^AA part is there to enable single
;; char sub/super scripts with coloured Isabelle output.
(defcustom x-symbol-isar-single-char-regexp 
  "\\([^\\]\\|\\\\<[A-Za-z]+>\\)\\|[\350-\357]\\([^\\]\\|\\\\<[A-Za-z]+>\\)\350\\|\^A[A-H]\\([^\\]\\|\\\\<[A-Za-z]+>\\)\^AA"
  "Return regexp matching \<ident> or c for some char c."
  :group 'x-symbol-isar
  :type 'regexp)

(defun x-symbol-isar-subscript-matcher (limit)  
  (block nil
    (let (open-beg open-end close-end close-beg script-type)
      (while (re-search-forward x-symbol-isar-font-lock-regexp limit t)
        (setq open-beg (match-beginning 0)
              open-end (match-end 0)
              script-type (if (eq (char-after (- open-end 2)) ?b)
                              'x-symbol-sub-face
                           'x-symbol-sup-face))
	(when (not (proof-string-match "[ \t\n]" (string (char-after open-end))))
	  (if (eq (char-after (- open-end 5)) ?b) ; if is spanning sup-/subscript
	      (let ((depth 1)) ; level of nesting
		(while (and (not (eq depth 0))
			    (re-search-forward x-symbol-isar-font-lock-limit-regexp
					       limit 'limit))
		  (setq close-beg (match-beginning 0)
			close-end (match-end 0))
		  (if (eq (char-after (- close-end 1)) ?\n) ; if eol
		      (setq depth 0)
		    (if (eq (char-after (- close-end 5)) ?b) ; if end of span
			(setq depth (+ depth 1))
		      (setq depth (- depth 1)))))
		(when (eq depth 0)
		  (when
		      (save-excursion
			(goto-char open-end)
			(re-search-forward x-symbol-isar-font-lock-contents-regexp
					   close-beg t))
		    (store-match-data (list open-beg close-end
					    open-beg open-end
					    open-end close-beg
					    close-beg close-end))
		    (return script-type)))
		(goto-char close-beg))
	    (when (re-search-forward x-symbol-isar-single-char-regexp
				     limit 'limit)
	      (setq close-end (match-end 0))
	      (store-match-data (list open-beg close-end
				      open-beg open-end
				      open-end close-end))
	      (return script-type))))))))
   
(defun isabelle-match-subscript (limit)
  (if (proof-ass x-symbol-enable)
      (setq x-symbol-isar-subscript-type
            (funcall x-symbol-isar-subscript-matcher limit))))

;; these are used for Isabelle output only. x-symbol does its own
;; setup of font-lock-keywords for the theory buffer
;; (x-symbol-isar-font-lock-keywords does not belong to language
;; access any more)
(defvar x-symbol-isar-font-lock-keywords
  '((isabelle-match-subscript
     (1 x-symbol-invisible-face t)
     (2 (progn x-symbol-isar-subscript-type) prepend)
     (3 x-symbol-invisible-face t t)))
  "Isabelle font-lock keywords for super- and subscripts.")

(defvar x-symbol-isar-font-lock-allowed-faces t)


;;;===========================================================================
;;;  Charsym Info
;;;===========================================================================

(defcustom x-symbol-isar-class-alist
  '((VALID "Isabelle Symbol" (x-symbol-info-face))
    (INVALID "no Isabelle Symbol" (red x-symbol-info-face)))
  "Alist for Isabelle's token classes displayed by info in echo area.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-texi
  :group 'x-symbol-info-strings
;;  :set 'x-symbol-set-cache-variable   [causes compile error]
  :type 'x-symbol-class-info)


(defcustom x-symbol-isar-class-face-alist nil
  "Alist for Isabelle's color scheme in TeXinfo's grid and info.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-isar
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
;;  :set 'x-symbol-set-cache-variable   [causes compile error]
  :type 'x-symbol-class-faces)



;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defvar x-symbol-isar-case-insensitive nil)
(defvar x-symbol-isar-token-shape nil)
(defvar x-symbol-isar-input-token-ignore nil)
(defvar x-symbol-isar-token-list 'identity)

(defvar x-symbol-isar-symbol-table      ; symbols (isabelle font)
  '((visiblespace "\\<spacespace>")
    (Gamma "\\<Gamma>")
    (Delta "\\<Delta>")
    (Theta "\\<Theta>")
    (Lambda "\\<Lambda>")
    (Pi "\\<Pi>")
    (Sigma "\\<Sigma>")
    (Phi "\\<Phi>")
    (Psi "\\<Psi>")
    (Omega "\\<Omega>")
    (alpha "\\<alpha>")
    (beta "\\<beta>")
    (gamma "\\<gamma>")
    (delta "\\<delta>")
    (epsilon1 "\\<epsilon>")
    (zeta "\\<zeta>")
    (eta "\\<eta>")
    (theta "\\<theta>")
    (kappa1 "\\<kappa>")
    (lambda "\\<lambda>")
    (mu "\\<mu>")
    (nu "\\<nu>")
    (xi "\\<xi>")
    (pi "\\<pi>")
    (rho1 "\\<rho>")
    (sigma "\\<sigma>")
    (tau "\\<tau>")
    (phi1 "\\<phi>")
    (chi "\\<chi>")
    (psi "\\<psi>")
    (omega "\\<omega>")
    (notsign "\\<not>")
    (logicaland "\\<and>")
    (logicalor "\\<or>")
    (universal1 "\\<forall>")
    (existential1 "\\<exists>")
    (epsilon "\\<some>")
    (biglogicaland "\\<And>")
    (ceilingleft "\\<lceil>")
    (ceilingright "\\<rceil>")
    (floorleft "\\<lfloor>")
    (floorright "\\<rfloor>")
    (bardash "\\<turnstile>")
    (bardashdbl "\\<Turnstile>")
    (semanticsleft "\\<lbrakk>")
    (semanticsright "\\<rbrakk>")
    (periodcentered "\\<cdot>")
    (element "\\<in>")
    (reflexsubset "\\<subseteq>")
    (intersection "\\<inter>")
    (union "\\<union>")
    (bigintersection "\\<Inter>")
    (bigunion "\\<Union>")
    (sqintersection "\\<sqinter>")
    (squnion "\\<squnion>")
    (bigsqintersection "\\<Sqinter>")
    (bigsqunion "\\<Squnion>")
    (perpendicular "\\<bottom>")
    (dotequal "\\<doteq>")
    (wrong "\\<wrong>")
    (equivalence "\\<equiv>")
    (notequal "\\<noteq>")
    (propersqsubset "\\<sqsubset>")
    (reflexsqsubset "\\<sqsubseteq>")
    (properprec "\\<prec>")
    (reflexprec "\\<preceq>")
    (propersucc "\\<succ>")
    (approxequal "\\<approx>")
    (similar "\\<sim>")
    (simequal "\\<simeq>")
    (lessequal "\\<le>")
    (coloncolon "\\<Colon>")
    (arrowleft "\\<leftarrow>")
    (endash "\\<midarrow>")
    (arrowright "\\<rightarrow>")
    (arrowdblleft "\\<Leftarrow>")
;   (nil "\\<Midarrow>")
    (arrowdblright "\\<Rightarrow>")
    (frown "\\<frown>")
    (mapsto "\\<mapsto>")
    (leadsto "\\<leadsto>")
    (arrowup "\\<up>")
    (arrowdown "\\<down>")
    (notelement "\\<notin>")
    (multiply "\\<times>")
    (circleplus "\\<oplus>")
    (circleminus "\\<ominus>")
    (circlemultiply "\\<otimes>")
    (circleslash "\\<oslash>")
    (propersubset "\\<subset>")
    (infinity "\\<infinity>")
    (box "\\<box>")
    (lozenge1 "\\<diamond>")
    (circ "\\<circ>")
    (bullet "\\<bullet>")
    (bardbl "\\<parallel>")
    (radical "\\<surd>")
    (copyright "\\<copyright>")))

(defvar x-symbol-isar-xsymbol-table    ; xsymbols
  '((Xi "\\<Xi>")
    (Upsilon1 "\\<Upsilon>")
    (iota "\\<iota>")
    (upsilon "\\<upsilon>")
    (plusminus "\\<plusminus>")
    (division "\\<div>")
    (longarrowright "\\<longrightarrow>")
    (longarrowleft "\\<longleftarrow>")
    (longarrowboth "\\<longleftrightarrow>")
    (longarrowdblright "\\<Longrightarrow>")
    (longarrowdblleft "\\<Longleftarrow>")
    (longarrowdblboth "\\<Longleftrightarrow>")
    (brokenbar "\\<bar>")
    (hyphen "\\<hyphen>")
    (macron "\\<inverse>")
    (exclamdown "\\<exclamdown>")
    (questiondown "\\<questiondown>")
    (guillemotleft "\\<guillemotleft>")
    (guillemotright "\\<guillemotright>")
    (degree "\\<degree>")
    (onesuperior "\\<onesuperior>")
    (onequarter "\\<onequarter>")
    (twosuperior "\\<twosuperior>")
    (onehalf "\\<onehalf>")
    (threesuperior "\\<threesuperior>")
    (threequarters "\\<threequarters>")
    (paragraph "\\<paragraph>")
    (registered "\\<registered>")
    (ordfeminine "\\<ordfeminine>")
    (masculine "\\<ordmasculine>")
    (section "\\<section>")
    (sterling "\\<pounds>")
    (yen "\\<yen>")
    (cent "\\<cent>")
    (currency "\\<currency>")
    (braceleft2 "\\<lbrace>")
    (braceright2 "\\<rbrace>")
    (top "\\<top>")
    (congruent "\\<cong>")
    (club "\\<clubsuit>")
    (diamond "\\<diamondsuit>")
    (heart "\\<heartsuit>")
    (spade "\\<spadesuit>")
    (arrowboth "\\<leftrightarrow>")
    (greaterequal "\\<ge>")
    (proportional "\\<propto>")
    (partialdiff "\\<partial>")
    (ellipsis "\\<dots>")
    (aleph "\\<aleph>")
    (Ifraktur "\\<Im>")
    (Rfraktur "\\<Re>")
    (weierstrass "\\<wp>")
    (emptyset "\\<emptyset>")
    (angle "\\<angle>")
    (gradient "\\<nabla>")
    (product "\\<Prod>")
    (arrowdblboth "\\<Leftrightarrow>")
    (arrowdblup "\\<Up>")
    (arrowdbldown "\\<Down>")
    (angleleft "\\<langle>")
    (angleright "\\<rangle>")
    (summation "\\<Sum>")
    (integral "\\<integral>")
    (circleintegral "\\<ointegral>")
    (dagger "\\<dagger>")
    (sharp "\\<sharp>")
    (star "\\<star>")
    (smltriangleright "\\<triangleright>")
    (triangleleft "\\<lhd>")
    (triangle "\\<triangle>")
    (triangleright "\\<rhd>")
    (trianglelefteq "\\<unlhd>")
    (trianglerighteq "\\<unrhd>")
    (smltriangleleft "\\<triangleleft>")
    (natural "\\<natural>")
    (flat "\\<flat>")
    (amalg "\\<amalg>")
    (Mho "\\<mho>")
    (arrowupdown "\\<updown>")
    (longmapsto "\\<longmapsto>")
    (arrowdblupdown "\\<Updown>")
    (hookleftarrow "\\<hookleftarrow>")
    (hookrightarrow "\\<hookrightarrow>")
    (rightleftharpoons "\\<rightleftharpoons>")
    (leftharpoondown "\\<leftharpoondown>")
    (rightharpoondown "\\<rightharpoondown>")
    (leftharpoonup "\\<leftharpoonup>")
    (rightharpoonup "\\<rightharpoonup>")
    (asym "\\<asymp>")
    (minusplus "\\<minusplus>")
    (bowtie "\\<bowtie>")
    (centraldots "\\<cdots>")
    (circledot "\\<odot>")
    (propersuperset "\\<supset>")
    (reflexsuperset "\\<supseteq>")
    (propersqsuperset "\\<sqsupset>")
    (reflexsqsuperset "\\<sqsupseteq>")
    (lessless "\\<lless>")
    (greatergreater "\\<ggreater>")
    (unionplus "\\<uplus>")
    (backslash3 "\\<setminus>")
    (smile "\\<smile>")
    (reflexsucc "\\<succeq>")
    (dashbar "\\<stileturn>")
    (biglogicalor "\\<Or>")
    (bigunionplus "\\<Uplus>")
    (daggerdbl "\\<ddagger>")
    (bigbowtie "\\<Join>")
    (booleans "\\<bool>")
    (complexnums "\\<complex>")
    (natnums "\\<nat>")
    (rationalnums "\\<rat>")
    (realnums "\\<real>")
    (integers "\\<int>")
    (lesssim "\\<lesssim>")
    (greatersim "\\<greatersim>")
    (lessapprox "\\<lessapprox>")
    (greaterapprox "\\<greaterapprox>")
    (definedas "\\<triangleq>")
    (cataleft "\\<lparr>")
    (cataright "\\<rparr>")
    (bigcircledot "\\<Odot>")
    (bigcirclemultiply "\\<Otimes>")
    (bigcircleplus "\\<Oplus>")
    (coproduct "\\<Coprod>")
    (cedilla "\\<cedilla>")
    (diaeresis "\\<dieresis>")
    (acute "\\<acute>")
    (hungarumlaut "\\<hungarumlaut>")
    (lozenge "\\<lozenge>")
    (smllozenge "\\<struct>")
    (dotlessi "\\<index>")
    (euro "\\<euro>")
    (zero1 "\\<zero>")
    (one1 "\\<one>")
    (two1 "\\<two>")
    (three1 "\\<three>")
    (four1 "\\<four>")
    (five1 "\\<five>")
    (six1 "\\<six>")
    (seven1 "\\<seven>")
    (eight1 "\\<eight>")
    (nine1 "\\<nine>")
    ))

(defun x-symbol-isar-prepare-table (table)
  "Prepare table for Isabelle/Isar."
  (mapcar (lambda (entry)
	    (list (car entry) nil
		  (cadr entry) 
		  (concat "\\" (cadr entry))))
	  table))

(defvar x-symbol-isar-table
  (x-symbol-isar-prepare-table
   (append
    x-symbol-isar-user-table
    x-symbol-isar-symbol-table
    x-symbol-isar-xsymbol-table)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; User-level settings for X-Symbol 
;;
;; this is MODE-ON CODING 8BITS UNIQUE SUBSCRIPTS IMAGE
(defcustom x-symbol-isar-auto-style
  '((proof-ass x-symbol-enable)	 ; MODE-ON: whether to turn on interactively
    nil   ;; x-symbol-coding
    'null ;; x-symbol-8bits	   [NEVER want it; null disables search]
    nil   ;; x-symbol-unique
    t     ;; x-symbol-subscripts
    nil)  ;; x-symbol-image
  "Variable used to document a language access.
See documentation of `x-symbol-auto-style'."
  :group 'x-symbol-isar
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

;; FIXME da: is this needed?
(defcustom x-symbol-isar-auto-coding-alist nil
  "*Alist used to determine the file coding of ISABELLE buffers.
Used in the default value of `x-symbol-auto-mode-alist'.  See
variable `x-symbol-auto-coding-alist' for details."
  :group 'x-symbol-isar
  :group 'x-symbol-mode
  :type 'x-symbol-auto-coding)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; x-symbol support
;;
;; The following settings configure the generic PG package.
;;

(eval-after-load "isar" ;; allow use outside PG
  (setq 
   proof-xsym-activate-command
   (isar-markup-ml "change print_mode (insert (op =) \"xsymbols\")")
   proof-xsym-deactivate-command
   (isar-markup-ml "change print_mode (remove (op =) \"xsymbols\")")))

(provide 'x-symbol-isar)
