(* Some checks for X-Symbol behaviour.  

   This file should be displayed sensibly, and also the
   display back from Isabelle ought to match.

   $Id$
*)

theory XSymbolTests = Main:

(* Thu Sep 25 16:26:47 BST 2030.  
   Problem reported by Norbert Schirmer <norbert.schirmer@web.de>
   Currently, superscript output highlighting seems broken anyway? *)

consts silly:: "'a => 'a => 'a" ("_\<^sup>_" [1000,1000] 1000)

consts k:: 'a

term "a\<^sup>b" (* b should be a blue variable *)
term "\<forall> x. a\<^sup>x" (* x should be a green bound variable *)
term "a\<^sup>k" (* k should be a black constant *)



(* 28.8.02: bug in pg-remove-specials broke this; now fixed *)

lemma "A ==> A" .  -- OK

consts A :: bool
lemma "A ==> A" .  -- "xsymbols shuld be displayed!"


(* Test electric token input: writing a token 
like \ <alpha>  (without space, \<alpha>) should immediately 
replace it. *)

constdefs
 P1 :: bool   ("P\<^sub>1")    (* subscript *)
 "P\<^sub>1 == True"
 P2 :: bool   ("P\<^sup>2")    (* superscript *)
 "P\<^sup>2 == True"

(* Buglet here: if we enable x-sym during scripting,
   goals/response flks are not updated, so xsyms
   do not appear in output windows. Stoping/starting
   prover fixes.
*)

thm P1_def P2_def	(* check display from Isabelle *)

constdefs (* long sub/sups, new 29/12/03, added by Gerwin Klein *)

 Plow :: bool ("P\<^bsub>low\<^esub>")		(* spanning subscript *)
  "P\<^bsub>low\<^esub> \<equiv> True"
 Phigh :: bool ("P\<^bsup>high\<^esup>")		(* spanning superscript *)
  "P\<^bsup>high\<^esup> \<equiv> True"

thm Plow_def Phigh_def	(* check display from Isabelle *)

theorem "P\<^sub>1 \<and> P\<^sup>2";  (* check fonts in goals window *)
by (simp add: P1_def P2_def)  (* .. and response window *)

consts
 "P\<^sup>\<alpha>" :: bool   (* superscript of a token char *)
 "\<^bold>X"  :: bool   (* bold character 
			    [not supported in current X-Symbols] *)


(* test: using a symbol as a subscript *)
(* 9.3.03: this causes nasty prob with pre-command hook,
   x-symbol-invisitiblity-spec type error, at least
   during editing. *)
consts
 intof :: "nat \<Rightarrow> int"  ("_\<^sub>\<int>" 50)
 mynat :: nat ("\<gamma>")

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

