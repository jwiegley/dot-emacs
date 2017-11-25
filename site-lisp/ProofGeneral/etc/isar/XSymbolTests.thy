(* Some checks for Unicode Tokens behaviour.  

   This file should be displayed sensibly, and also the
   display back from Isabelle ought to match.

   $Id$
*)

theory XSymbolTests imports Main begin

(* Fri Dec 14 13:20:38 GMT 2007.
   http://proofgeneral.inf.ed.ac.uk/trac/ticket/161
   Sub/superscript output not handled properly when enabled using
   menu.   Fix: add fontification to proof-x-symbol-decode-region,
   fix in proof-x-symbol.el 8.10.
*)

(* response output *)
thm wf_trancl

(* goals output *)
lemma wf_trancl2 : "wf ?r \<Longrightarrow> wf (?r\<^sup>+)"
by auto

(* Thu Sep 25 16:26:47 BST 2003.  
   Problem reported by Norbert Schirmer <norbert.schirmer@web.de>
   Currently, superscript output highlighting seems broken anyway? *)

consts "\<alpha1>":: "'a => 'a" ("\<alpha1>\<^sup>_")
consts "\<alpha2>":: "'a => 'a => 'a" ("\<alpha2>\<^sup>_")
consts "\<alpha3>":: "'a => 'a => 'a => 'a" ("_\<^sup>_\<^sup>_")

consts k:: 'a

term "\<alpha>"
term "a\<^sup>b" (* b should be a blue variable *)
term "\<forall>x. a\<^sup>x" (* x should be a green bound variable *)
term "a\<^sup>k" (* k should be a black constant *)
term "\<alpha>\<^isub>2" (* alpha should be blue variable with subscripted blue 2 *)
term "\<alpha>\<^isup>x"  (* identifier *)

consts sausage:: "'a => 'a => 'a" ("_\<^bsup>_\<^esup>" [1000,1000] 1000)

term "k\<^bsup>long\<^esup>"  (* k black, long is blue *)


(* 28.8.02: bug in pg-remove-specials broke this; now fixed *)

lemma "A ==> A" .  -- OK

consts A :: bool
lemma "A ==> A" .  -- "xsymbols should be displayed!"


(* Test electric token input: writing a token 
like \ <alpha>  (without space, \<alpha>) should immediately 
replace it. *)

constdefs
 P1 :: bool   ("P\<^sub>1")    (* subscript *)
 "P\<^sub>1 == True"
 P2 :: bool   ("P\<^sup>2")    (* superscript *)
 "P\<^sup>2 == True"

 "P\<^loc>x" (* location escape *)

(* Buglet here: if we enable x-sym during scripting,
   goals/response flks are not updated, so xsyms
   do not appear in output windows. Stoping/starting
   prover fixes.
*)

thm P1_def P2_def	(* check display from Isabelle *)

constdefs (* long sub/sups, new 29/12/03, added by Gerwin Klein *)

\<^bitalic>test italics\<^eitalic>
\<^bserif>serif\<^eserif>
\<^bfrakt>fraktur\<^efrakt>
\<^bbold>test\<^ebold>

\<^bsub> asda low\<^esub>
 Plow :: bool ("P\<^bsub>low\<^esub>")		(* spanning subscript *)
  "P\<^bsub>low\<^esub> \<equiv> True"
 Phigh :: bool ("P\<^bsup>high\<^esup>")		(* spanning superscript *)
  "P\<^bsup>high\<^esup> \<equiv> True"

thm Plow_def Phigh_def	(* check display from Isabelle *)

theorem "P\<^sub>1 \<and> P\<^sup>2";  (* check fonts in goals window *)
by (simp add: P1_def P2_def)  (* .. and response window *)

consts
 "P\<^sup>\<alpha>" :: bool   (* superscript of a token char *)
 "\<^bold>P"  :: bool   (* bold character *)
 "\<^italic>i"  :: int 

\<^bitalic>italic?\<^eitalic>

(* test: using a symbol as a subscript *)
(* 9.3.03: this causes nasty prob with pre-command hook,
   x-symbol-invisitiblity-spec type error, at least
   during editing. *)
consts
 intof :: "nat \<Rightarrow> int"  ("_\<^sub>\<int>" 50)
 mynat :: nat ("\<gamma>")
\<one> \<two> \<C> \<J>      \<S> \<h> h \<AA> 

\<^bscript>foo\<^escript>
bar

term "intof 3"

constdefs
 myint :: int
 "myint == \<gamma>\<^sub>\<int>"
 

(* 
 Another X-Symbol oddity: sometimes the _first_ buffer to
 be visited displays _some_ characters as \2xx, e.g.
 for \<circ>.  But subsequent buffers to be visited work
 fine.  Problem is stable for turning x-symbol on/off.
 Revisting the first buffer cures the problem.
 Update: May be inherent problem with non-Mule version of
 X-Symbol (CW suggests)
*)

consts
  iter :: "('a => 'a) => nat => ('a => 'a)"
primrec
  "iter f 0 = id"
  "iter f (Suc n) = f \<circ> (iter f n)"


end

\<A>
\<AA> \<ABC> \<ss> \<pounds> \<yen>

SYMBOL Ideas:

 \<0x888>  for unicode character
 \<alpha:foo> for variants, same display

 \<color:foo> for colour, no sems (dropped in translation)