(* Some checks for X-Symbol behaviour.  
   $Id$
*)

theory XSymbolTests = Main:

constdefs
 P1 :: bool   ("P\<^sub>1")    (* subscript *)
 "P\<^sub>1 == True"

theorem "P\<^sub>1";    (* check subscript appears in goals window *)
by (simp add: P1_def)  (* .. and response window *)

consts
 "P\<^sup>\<alpha>" :: bool   (* superscript of a token char *)
 "\<^bold>X"  :: bool   (* bold character *)



(* 
 Another X-Symbol oddity: sometimes the _first_ buffer to
 be visited displays _some_ characters wrongly, e.g. \234 
 for \<circ>.  But subsequent buffers to be visited work
 fine.  Problem is stable for turning x-symbol on/off.
 Revisting the first buffer cures the problem.
*)

consts
  iter :: "('a => 'a) => nat => ('a => 'a)"
primrec
  "iter f 0 = id"
  "iter f (Suc n) = f \<circ> (iter f n)"


end

