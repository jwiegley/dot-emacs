(* ProofGenearal/isa/depends.ML

   Experimental code for communicating theorem dependencies from Isabelle
   to Proof General.

   This code is taken from thm_deps.ML in Isabelle 2002.  
   It's probably incompatible with other Isabelle versions.

   It is duplicated almost verbatim because what we need is
   hardwired to a call on the browser tool.
*)

(*  Title:      Pure/Thy/thm_deps.ML
    ID:         Id: thm_deps.ML,v 1.12 2001/11/19 16:42:00 berghofe Exp
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Visualize dependencies of theorems.
*)

signature BASIC_THM_DEPS =
sig
  val new_thm_deps : thm list -> unit
end;

signature PG_THM_DEPS =
sig
  include BASIC_THM_DEPS
  val enable : unit -> unit
  val disable : unit -> unit
end;

structure PGThmDeps : PG_THM_DEPS =
struct

open Proofterm;

fun enable () = if ! proofs = 0 then proofs := 1 else ();
fun disable () = proofs := 0;

fun dest_thm_axm (PThm (nt, prf, _, _)) = (nt, prf)
  | dest_thm_axm (PAxm (n, _, _)) = ((n ^ " (Ax)", []), MinProof [])
  | dest_thm_axm _ = (("", []), MinProof []);

fun make_deps_graph (p, AbsP (_, _, prf)) = make_deps_graph (p, prf)
  | make_deps_graph (p, Abst (_, _, prf)) = make_deps_graph (p, prf)
  | make_deps_graph (p, prf1 %% prf2) =
      make_deps_graph (make_deps_graph (p, prf1), prf2)
  | make_deps_graph (p, prf % _) = make_deps_graph (p, prf)
  | make_deps_graph (p, MinProof prfs) = foldl make_deps_graph (p, prfs)
  | make_deps_graph (p as (gra, parents), prf) =
      let val ((name, tags), prf') = dest_thm_axm prf
      in
        if name <> "" andalso not (Drule.has_internal tags) then
          if is_none (Symtab.lookup (gra, name)) then
            let
              val (gra', parents') = make_deps_graph ((gra, []), prf');
              val prefx = #1 (Library.split_last (NameSpace.unpack name));
              val session =
                (case prefx of
                  (x :: _) =>
                    (case ThyInfo.lookup_theory x of
                      Some thy =>
                        let val name = #name (Present.get_info thy)
                        in if name = "" then [] else [name] end 
                    | None => [])
                 | _ => ["global"]);
            in
              if name mem parents' then (gra', parents union parents')
              else (Symtab.update ((name,
                {name = Sign.base_name name, ID = name,
                 dir = space_implode "/" (session @ prefx),
                 unfold = false, path = "", parents = parents'}), gra'),
               name ins parents)
            end
          else (gra, name ins parents)
        else
          make_deps_graph ((gra, parents), prf')
      end;

fun new_thm_deps thms =
  let
    val header = "Proof General, the theorem dependencies are: \"";
    val gra = map snd (Symtab.dest (fst (foldl make_deps_graph ((Symtab.empty, []),
      map (#2 o #der o Thm.rep_thm) thms))));
    val deps = sort_strings (foldl (op union) ([],(map #parents gra)))
    val msg = header ^ (space_implode " " deps) ^ "\""
  in priority msg end;



end;

(* Adjust global context [ how can we do this for Isar? ] *)

structure PGBasicThmDeps : BASIC_THM_DEPS = PGThmDeps;
open PGBasicThmDeps;

val old_qed = qed;
fun qed name = 
  let val _ = old_qed name
      val proved_thm = thm name
   in new_thm_deps [proved_thm] end;

val old_qed_goal = qed_goal;
fun qed_goal name thy goal tacsf =
  let val _ = old_qed_goal name thy goal tacsf
      val proved_thm = thm name
   in new_thm_deps [proved_thm] end;

val old_qed_goalw = qed_goalw;
fun qed_goalw name thy rews goal tacsf =
  let val _ = old_qed_goalw name thy rews goal tacsf
      val proved_thm = thm name
   in new_thm_deps [proved_thm] end;

(* FIXME: this one only in HOL?? *)
val old_qed_spec_mp = qed_spec_mp;
fun qed_spec_mp name = 
  let val _ = old_qed_spec_mp name
      val proved_thm = thm name
   in new_thm_deps [proved_thm] end;


