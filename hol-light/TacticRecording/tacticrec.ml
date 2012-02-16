(* ========================================================================== *)
(* TACTIC RECORDING (HOL LIGHT)                                               *)
(* - Mechanism to record tactic proofs at the user level                      *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2011-2012                           *)
(* ========================================================================== *)


(* This file implements a mechanism for recording tactic proofs at the level  *)
(* of interactive proof steps.  A recorded proof takes the form of a tree of  *)
(* goals, and is capable of capturing both complete and incomplete proofs, as *)
(* well as hierarchy correspoding to tacticals.                               *)

(* The crucial mechanism by which goals in the subgoal package state are      *)
(* linked to parts of the stored goal tree is based on unique goal id         *)
(* numbers.  Each goal in the subgoal package state is annotated with such an *)
(* id, and this is also stored at each level of the goal tree.  As a tactic   *)
(* is executed, the id from the goal in the subgoal package state that it     *)
(* executes on is used to locate the corresponding part of the goal tree, and *)
(* the ids of the resulting subgoals are used to label the corresponding      *)
(* subparts of the goal tree.                                                 *)


open Dltree;;



(* ** MODES ** *)


(* Store goal sequent flag *)

(* Intermediate goal results are only stored if this flag is set.  This can   *)
(* be used to cut down on memory usage.                                       *)

let store_goalsequent_flag = ref true;;



(* ** GOAL TREE DATATYPES & STATE ** *)


(* Goal tree datatype *)

(* This is the datatype for recording tactic proofs as a tree of goals, with  *)
(* structure corresponding to interactive proof steps.  The structural aspect *)
(* is captured by 'gtree0':                                                   *)
(*  Gactive   - Leaf for an active goal in the proof;                         *)
(*  Gexecuted - Node for a goal that has had a tactic successfully executed   *)
(*             on it.  Carries a list of subtrees, one for each of the        *)
(*             resulting subgoals, where the list is empty for a tactic that  *)
(*             completes its goal;                                            *)
(*  Gexit     - Wiring exiting a box, indicating destination goal.            *)

type ginfo =
   (goalid * goalid)                 (* Goal id & Parent id *)
 * string option                     (* Goal name (optional) *)
 * goal option                       (* Goal sequent (optional) *)
 * unit option ref;;                 (* Formal proof (optional) *)

type gstep =
   Gatom of finfo                    (* Atomic tactic *)
 | Gbox of (finfo * gtree * bool)    (* Box for a tactical; flag for special *)

and gtree0 =
   Gactive                                                (* Active goal *)
 | Gexecuted of (gstep *       (* Tactic structure *)     (* Executed tactic *)
                 gtree list)   (* Resulting subgoals *)
 | Gexit of goalid                                        (* Exit the box *)

and gtree =
   ginfo                             (* Various info about goal *)
 * gtree0 ref;;                      (* Goal plumbing *)


(* Example *)

(* Figure 1(b) in Denny et al would be represented by the following:          *)
(*                                                                            *)
(*  (_, ref                                                                   *)
(*   Gexecuted                                                                *)
(*     (Gbox (Some "T1")                                                      *)
(*        (_, ref                                                             *)
(*         Gexecuted                                                          *)
(*           (Gatom (Some "T2"),                                              *)
(*            [ (_, ref Gexecuted (Gatom (Some "WF"), []));                   *)
(*              (_, ref Gexit _) ])),                                         *)
(*      [ (_, ref                                                             *)
(*         Gexecuted                                                          *)
(*           (Gbox (Some "DP")                                                *)
(*              (_, ref                                                       *)
(*               Gexecuted                                                    *)
(*                 (Gatom (Some "Normalise"),                                 *)
(*                  [ (_, ref Gexecuted (Gatom (Some "Taut"), [])) ])),       *)
(*            [])) ]))                                                        *)


(* Destructors *)

let ginfo_id (((id,_),_,_,_):ginfo) : goalid = id;;

let ginfo_pid (((_,pid),_,_,_):ginfo) : goalid = pid;;

let ginfo_name ((_,x_,_,_):ginfo) : string =
  match x_ with
    Some x -> x
  | None   -> failwith "Goal not named";;

let ginfo_sqt ((_,_,sqt_,_):ginfo) : goal =
  match sqt_ with
    Some sqt -> sqt
  | None     -> failwith "Goal sequent not stored";;

let ginfo_fproof ((_,_,_,prf_):ginfo) : unit =
  match !prf_ with
    Some prf -> prf
  | None     -> failwith "Goal's formal proof not stored";;

let gtree_id ((info,_):gtree) = ginfo_id info;;
let gtree_pid ((info,_):gtree) = ginfo_pid info;;
let gtree_name ((info,_):gtree) = ginfo_name info;;
let gtree_sqt ((info,_):gtree) = ginfo_sqt info;;
let gtree_fproof ((info,_):gtree) = ginfo_fproof info;;

let gstep_tactic (gstp:gstep) =
  match gstp with
    Gatom info | Gbox (info,_,_) -> info;;

let gtree_proof ((_,gtrm):gtree) =
  match (!gtrm) with
    Gexecuted (gstp,_) -> gstp
  | _                  -> failwith "gtree_proof: Not executed";;

let gtree_tactic gtr =
  (gstep_tactic o gtree_proof) gtr;;

let gtree_tactic1 ((_,gtrm) as gtr :gtree) =
  match !gtrm with
    Gactive -> active_info
  | _       -> gtree_tactic gtr;;


(* Tests *)

let is_active_gtree ((_,gtrm):gtree) =
  match !gtrm with
    Gactive -> true
  | _       -> false;;


(* Dummy values *)

let dummy_goal_info : ginfo = ((0,0), None, None, ref None);;

let dummy_goal_tree : gtree = (dummy_goal_info, ref Gactive);;


(* Goal tree database *)

let the_goal_tree = ref dummy_goal_tree;;


(* Location database *)

(* This database is maintained in parallel with the goal tree, to enable fast *)
(* location of the subtree corresponding to a goal (as opposed to laboriously *)
(* traversing the tree to find the branch with the right id).                 *)

let the_gtree_locations = (dltree_empty () : (goalid, gtree ref) dltree);;

let get_gtree id = !(dltree_lookup id the_gtree_locations);;

let deregister_gtree gtr =
  (dltree_remove (gtree_id gtr) the_gtree_locations);;

let register_gtree gtr =
  (dltree_insert (gtree_id gtr, ref gtr) the_gtree_locations);;


(* Initialisation of the goal tree state *)

let init_goal_tree g =
  let g_ = if (!store_goalsequent_flag) then Some g else None in
  let ginfo = ((!the_goal_id_counter,0), None, g_, ref None) in
  let gtr = (ginfo, ref Gactive) in
  (the_goal_tree := gtr;
   dltree_reempty the_gtree_locations;
   register_gtree gtr);;



(* ** GTREE UTILITIES ** *)


(* All children *)

let rec gtree_all_children gtr =
  let (_,gtrm) = gtr in
  match (!gtrm) with
    Gexecuted (gstp,gtrs)
       -> (gstep_all_children gstp) @
          gtrs @
          flat (map gtree_all_children gtrs)
  | _  -> []

and gstep_all_children gstp =
  match gstp with
    Gbox (_,gtr,false) -> gtr::(gtree_all_children gtr)
  | Gatom _ | Gbox _   -> [];;



(* ** PLUMBING ** *)

(* These utilities do the plumbing for tactic applications and tactical       *)
(* applications, promoting operations from goals to xgoals and incorporating  *)
(* the results into gtrees.                                                   *)


(* Creating a sub gtree *)

(* This creates a new xgoal for a goal, giving it a fresh id and registering  *)
(* it in the locations database.  Used on all new subgoals.                   *)

let new_active_subgtree pid (g:goal) : goalid * gtree =
  let id = (inc_goal_id_counter (); !the_goal_id_counter) in
  let g_ = if (!store_goalsequent_flag) then Some g else None in
  let info = ((id,pid), None, g_, ref None) in
  let gtr = (info, ref Gactive) in
  (register_gtree gtr;
   (id,gtr));;


(* Extension *)

(* This extends a gtree with the subgoals resulting from applying a tactic.   *)

let extend_gtree (pid:goalid) (gstp:gstep) (gs':goal list) : xgoal list =
  let gtr = get_gtree pid in
  let (_,gtrm) = gtr in
  let () = try assert (!gtrm = Gactive)
           with Assert_failure _ ->
                   failwith "extend_gtree: Internal error - Not active" in
  let (ids',gtrs) = unzip (map (new_active_subgtree pid) gs') in
  let gxs' = zip gs' ids' in
  (gtrm := Gexecuted (gstp,gtrs);
   gxs');;


(* Deletion *)

(* This deletes from a gtree the result of applying a tactic to a given goal, *)
(* also deleting the resulting subgoals from the locations database.          *)

let delete_step (id:goalid) =
  let gtr = get_gtree id in
  let (_,gtrm) = gtr in
  let () = match (!gtrm) with
             Gexecuted _ -> ()
           | _ -> failwith "delete_step: Internal error - Not executed" in
  let gtrs = gtree_all_children gtr in
  (gtrm := Gactive;
   do_list deregister_gtree gtrs);;


(* Externalising *)

(* This is used for turning a box's active subgoal to exit wiring.            *)

let externalise_gtree ((id0,id):goalid*goalid) : unit =
  let (_,gtrm) = get_gtree id0 in
  match (!gtrm) with
    Gactive -> (gtrm := Gexit id)
  | _ -> failwith "externalise_gtree: Internal error - Not active";;



(* ** WRAPPER FUNCTIONS ** *)

(* These functions are for promoting existing tactics and tacticals.          *)


(* Tactic wrapper *)

(* This is for wrapping around a tactic, to promote it to work on xgoals and  *)
(* incorporate the results into an existing gtree.                            *)

let tactic_wrap0 finfo (tac:tactic) (gx:xgoal) : xgoalstate =
  let (g,id) = dest_xgoal gx in
  let (meta,gs',just) = tac g in
  let gxs' = extend_gtree id (Gatom finfo) gs' in
  (meta,gxs',just);;

let tactic_wrap x tac =
  tactic_wrap0 (Some x, []) tac;;

let string_tactic_wrap x (tac:string->tactic) (s:string) : xtactic =
  tactic_wrap0 (Some x, [Fstring s]) (tac s);;

let term_tactic_wrap x (tac:term->tactic) (tm:term) : xtactic =
  tactic_wrap0 (Some x, [Fterm tm]) (tac tm);;

let termpair_tactic_wrap x (tac:term*term->tactic) (tm1,tm2) : xtactic =
  tactic_wrap0 (Some x, [Fpair (Fterm tm1, Fterm tm2)]) (tac (tm1,tm2));;

let termlist_tactic_wrap x (tac:term list->tactic) tms : xtactic =
  tactic_wrap0 (Some x, [Flist (map (fun tm -> Fterm tm) tms)]) (tac tms);;

let thm_tactic_wrap x (tac:thm->tactic) (xth:xthm) : xtactic =
  let (th,prf) = dest_xthm xth in
  tactic_wrap0 (Some x, [Fthm prf]) (tac th);;

let thmlist_tactic_wrap x (tac:thm list->tactic) (xths:xthm list) : xtactic =
  let (ths,prfs) = unzip (map dest_xthm xths) in
  tactic_wrap0 (Some x, [Flist (map (fun prf -> Fthm prf) prfs)]) (tac ths);;

let stringthm_tactic_wrap x (tac:string->thm->tactic) s (xth:xthm) : xtactic =
  let (th,prf) = dest_xthm xth in
  tactic_wrap0 (Some x, [Fstring s; Fthm prf]) (tac s th);;


(* xCONV_TAC - a special case I think; not a tactical *)

let t_tm = `T`;;

let xCONV_TAC (cx:xconv) (gx:xgoal) : xgoalstate =
  let (g,id) = dest_xgoal gx in

  let (asl,w) = g in
  let thx = cx w in
  let (th,proof) = dest_xthm thx in
  let tm = concl th in
  let finfo = (Some "CONV_TAC", [finfo_as_meta_arg proof]) in

  let tac g =
     if (aconv tm w)
       then (null_meta, [], fun i [] -> INSTANTIATE_ALL i th)
     else let l,r = dest_eq tm in
       if not (aconv l w)
       then failwith "CONV_TAC: bad equation"
     else if (r = t_tm)
       then (null_meta, [], fun i [] -> INSTANTIATE_ALL i (EQT_ELIM th))
       else (null_meta, [(asl,r)],
             fun i [th0] -> EQ_MP (INSTANTIATE_ALL i (SYM th)) th0) in

  let (meta,gs,just) = tac g in
  let gxs = extend_gtree id (Gatom finfo) gs in
  (meta,gxs,just);;


(* Tactical wrapper *)

(* This is for wrapping around a tactical, to incorporate the results into a  *)
(* box in an existing gtree, where the execution of the tactical's tactics is *)
(* captured inside the box, so that they can be stepped through and/or        *)
(* refactored.  Thus we cannot take the tactical as a black box; it must      *)
(* already be promoted to work with xtactics and xgoals.  This must done by   *)
(* hand for each tactical by trivially adjusting its original source code.    *)

let tactical_wrap0 finfo (xttcl:'a->xtactic) (arg:'a) (gx:xgoal) : xgoalstate =
  let (g,id) = dest_xgoal gx in
  let (id0,gtr0) = new_active_subgtree id g in
  let gx0 = mk_xgoal (g,id0) in
  let (meta,gxs0,just) = xttcl arg gx0 in
  let (gs0,ids0) = unzip (map dest_xgoal gxs0) in
  let gxs = extend_gtree id (Gbox (finfo,gtr0,false)) gs0 in
  let ids = map xgoal_id gxs in
  (do_list externalise_gtree (zip ids0 ids);
   (meta,gxs,just));;

let tactical_wrap x (xttcl:'a->xtactic) (xtac:'a) : xtactic =
  tactical_wrap0 (Some x, []) xttcl xtac;;

let btactical_wrap x (xttcl:'a->'b->xtactic) (xtac1:'a) (xtac2:'b) : xtactic =
  tactical_wrap0 (Some x, []) (xttcl xtac1) xtac2;;

let int_tactical_wrap x (xttcl:int->'a->xtactic) (n:int) (xtac:'a) : xtactic =
  tactical_wrap0 (Some x, [Fint n]) (xttcl n) xtac;;

let list_tactical_wrap x (xttcl:('a->xtactic)->'a list->xtactic)
                         (xtac:'a->xtactic) (l:'a list) : xtactic =
  tactical_wrap0 (Some x, []) (xttcl xtac) l;;


(* xSUBGOAL_THEN - seems to be another special case *)

let xASSUME = conv_wrap "ASSUME" ASSUME;;

let xSUBGOAL_THEN (tm:term) (ttac:xthm_tactic) (gx:xgoal) : xgoalstate =
  let arg = xASSUME tm in

  let (g,id) = dest_xgoal gx in
  let (id0,gtr0) = new_active_subgtree id g in
  let gx0 = mk_xgoal (g,id0) in
  let (meta,gxs0,just) = ttac arg gx0 in
  let (gs0,ids0) = unzip (map dest_xgoal gxs0) in

  let (asl,_) = g in
  let g2 = (asl,tm) in
  let finfo = (Some "SUBGOAL_THEN",
               [Fterm tm; (finfo_as_meta_arg o gtree_tactic) gtr0]) in

  let gxs = extend_gtree id (Gbox (finfo,gtr0,true)) (g2::gs0) in
  let ids1 = map xgoal_id (tl gxs) in
  let just' = fun i l -> PROVE_HYP (hd l) (just i (tl l)) in
  (do_list externalise_gtree (zip ids0 ids1);
   (meta,gxs,just'));;


(*
let SUBGOAL_TAC s tm prfs =
  match prfs with
   p::ps -> (warn (ps <> []) "SUBGOAL_TAC: additional subproofs ignored";
             SUBGOAL_THEN tm (LABEL_TAC s) THENL [p; ALL_TAC])
  | [] -> failwith "SUBGOAL_TAC: no subproof given";;

let (FREEZE_THEN :thm_tactical) =
  fun ttac th (asl,w) ->
    let meta,gl,just = ttac (ASSUME(concl th)) (asl,w) in
    meta,gl,fun i l -> PROVE_HYP th (just i l);;
*)



(* ** SUBGOAL PACKAGE OPERATIONS FOR XGOALS ** *)

(* A few of the xtactic subgoal package commands are adjusted here.           *)


(* Starting/finishing a tactic proof *)

(* For commands that start a tactic proof, 'mk_xgoalstate' is adjusted to     *)
(* initialise the goal tree.  Commands that return a tactic proof's resulting *)
(* theorem, the theorem is adjusted to be an 'xthm' that carries a reference  *)
(* to the goal tree.                                                          *)

let mk_xgoalstate (g:goal) : xgoalstate =
  let result = mk_xgoalstate g in
  (init_goal_tree g;
   result);;

let (xTAC_PROOF : goal * xtactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_xgoalstate g in
    let _,sgs,just = xby tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals";;

let xprove(t,tac) =
  let th = xTAC_PROOF(([],t),tac) in
  let t' = concl th in
  if t' = t then th else
  try EQ_MP (ALPHA t' t) th
  with Failure _ -> failwith "prove: justification generated wrong theorem";;

let xset_goal(asl,w) =
  current_xgoalstack :=
    [mk_xgoalstate(map (fun t -> "",ASSUME t) asl,w)];
  !current_xgoalstack;;

let xg t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   xset_goal([],t);;


(* Undoing a tactic proof step *)

(* 'xb' needs to be adjusted to deleted the undone step in the goal tree.     *)

let xb () =
  let result = xb () in
  let (_,gxs,_) = hd result in
  let (_,id) = hd gxs in
  (delete_step id;
   result);;



(* ** GTREE OPERATIONS ** *)


(* Goal id graph *)

let rec gtree_graph0 gtr graph0 =
  let (info,gtrm) = gtr in
  let ((id,pid),_,g_,_) = info in
  match !gtrm with
    Gactive
       -> (pid,id)::graph0
  | Gexit id
       -> failwith "???"
  | Gexecuted (_,gtrs)
       -> (pid,id)::(foldr gtree_graph0 gtrs graph0);;

let gtree_graph () =
  let nns = gtree_graph0 (!the_goal_tree) [] in
  tl nns;;                (* remove (0,0) at head of dumped list *)


(* Goal id trace *)

let rec gtree_id_trace gtr =
  let (_,gtrm) = gtr in
  match !gtrm with
    Gactive
       -> [gtree_id gtr]
  | Gexit id
       -> let gtr1 = get_gtree id in
          gtree_id_trace gtr1
  | Gexecuted (gstp,gtrs1)
       -> (match gstp with
             Gatom _ | Gbox (_,_,true)
                -> (gtree_id gtr) :: flat (map gtree_id_trace gtrs1)
           | Gbox (_,gtr1,false)
                -> gtree_id_trace gtr1);;


(* Tactic trace *)

let rec gtree_tactic_trace gtr =
  map (gtree_tactic1 o get_gtree) (gtree_id_trace gtr);;

