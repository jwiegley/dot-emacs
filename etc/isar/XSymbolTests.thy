(* Some checks for X-Symbol behaviour.  
   $Id$
*)

theory XSymbolTests = Main:

(* At the moment, electric token input doesn't work
despite being enabled.  So writing a token 
like  \<alpha> doesn't immediately replace it. *)

constdefs
 P1 :: bool   ("P\<^sub>1")    (* subscript *)
 "P\<^sub>1 == True"

(* Buglet here: if we enable x-sym during scripting,
   goals/response flks are not updated, so subscripts
   do not appear in output windows.  
   Restarting prover fixes.
*)

theorem "P\<^sub>1";  (* check subscript appears in goals window *)
by (simp add: P1_def)  (* .. and response window *)

consts
 "P\<^sup>\<alpha>" :: bool   (* superscript of a token char *)
 "\<^bold>X"  :: bool   (* bold character *)


(* Markus reports that · is saved in the file as
an 8-bit character.  I can't repeat that with XEmacs 21.4,
unless I set the relevant X-Symbol menu option. *)

(* 
 Another X-Symbol oddity: sometimes the _first_ buffer to
 be visited displays _some_ characters as \2xx, e.g.
 for \<circ>.  But subsequent buffers to be visited work
 fine.  Problem is stable for turning x-symbol on/off.
 Revisting the first buffer cures the problem.
 I can't easily repeat the problem...
*)

consts
  iter :: "('a => 'a) => nat => ('a => 'a)"
primrec
  "iter f 0 = id"
  "iter f (Suc n) = f \<circ> (iter f n)"


end

