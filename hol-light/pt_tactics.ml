(* 
   Modified HOL Light goalstack to support Hendrik Tew's Prooftree
   application via Proof General.

   Mark Adams, David Aspinall
   January 2012.

   This file contains some functions that are modified from the
   original HOL Light code, and is therefore subject to the HOL Light
   copyright, see the file LICENSE-HOL-LIGHT in this directory.

   TODO:
    1) rebind top-level identifiers for g, e, r, b and add a flag
       to turn on/off extended behaviour
*)



(* ------------------------------------------------------------------------- *)
(* Goal counter for providing goad ids.                                      *)
(* ------------------------------------------------------------------------- *)

type goal_id = int;;

let string_of_goal_id id = string_of_int id;;

let the_goal_counter = ref (0 : goal_id);;

let inc_goal_counter () =
  (the_goal_counter := !the_goal_counter + 1;
   !the_goal_counter);;

let reset_goal_counter () =
  (the_goal_counter := 0;
   !the_goal_counter);;

(* ------------------------------------------------------------------------- *)
(* An xgoal extends a goal with an identity.                                 *)
(* ------------------------------------------------------------------------- *)

type xgoal = goal * goal_id;;

let dest_xgoal (gx : xgoal) = gx;;

(* ------------------------------------------------------------------------- *)
(* The xgoalstate is like goalstate but for xgoals instead of goals.         *)
(* ------------------------------------------------------------------------- *)

type xgoalstate = (term list * instantiation) * xgoal list * justification;;

(* ------------------------------------------------------------------------- *)
(* A goalstack but for xgoals.                                               *)
(* ------------------------------------------------------------------------- *)

type xgoalstack = xgoalstate list;;

(* ------------------------------------------------------------------------- *)
(* A refinement but for xgoals.                                              *)
(* ------------------------------------------------------------------------- *)

type xrefinement = xgoalstate -> xgoalstate;;

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

let (inst_xgoal:instantiation->xgoal->xgoal) =
  fun p ((thms,w),id) ->
    (map (I F_F INSTANTIATE_ALL p) thms,instantiate p w),id;;

(* ------------------------------------------------------------------------- *)
(* A printer for xgoals etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let the_new_goal_ids = ref ([] : goal_id list);;

let the_tactic_flag = ref false;;

let print_xgoal ((g,id) : xgoal) : unit =
  (print_string ("[Goal ID " ^ string_of_goal_id id ^ "]");
   print_newline ();
   print_goal g);;

let (print_xgoalstack:xgoalstack->unit) =
  let print_xgoalstate k gs =
    let (_,gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    print_string s; print_newline();
    if gl = [] then () else
    (do_list (print_xgoal o C el gl) (rev(1--(k-1)));
     print_string "[*]";
     print_xgoal (el 0 gl)) in
  fun l ->
   (print_string ("[State Counter " ^ string_of_int (length l) ^ "]");
    (if (!the_tactic_flag)
       then let xs = map string_of_int (!the_new_goal_ids) in
            the_tactic_flag := false;
            if (length xs > 0) then
              print_string
                ("[New Goal IDs: " ^
                 end_itlist (fun x1 x2 -> x1 ^ " " ^ x2) xs ^ "]"));
    print_newline ();
    if l = [] then print_string "Empty goalstack"
    else if tl l = [] then
      let (_,gl,_ as gs) = hd l in
      print_xgoalstate 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_xgoalstate p' gs);;

(* ------------------------------------------------------------------------- *)
(* Goal labelling, for fresh xgoals.                                         *)
(* ------------------------------------------------------------------------- *)

let label_goals (gs : goal list) : xgoal list =
  let gxs = map (fun g -> (g, inc_goal_counter ())) gs in
  (the_new_goal_ids := map snd gxs;
   gxs);;

(* ------------------------------------------------------------------------- *)
(* Version of 'by' for xrefinements.                                         *)
(* ------------------------------------------------------------------------- *)

let (xby:tactic->xrefinement) =
  fun tac ((mvs,inst),glsx,just) ->
    let gx = hd glsx
    and oglsx = tl glsx in
    let (g,id) = dest_xgoal gx in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let subglsx = label_goals subgls in
    let n = length subglsx in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and glsx' = subglsx @ map (inst_xgoal newinst) oglsx in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),glsx',just';;

(* ------------------------------------------------------------------------- *)
(* Rotate but for xgoalstate.  Completely trivial redefinition.              *)
(* ------------------------------------------------------------------------- *)

let (xrotate:int->xrefinement) =
  let rotate_p (meta,sgs,just) =
    let sgs' = (tl sgs)@[hd sgs] in
    let just' i ths =
      let ths' = (last ths)::(butlast ths) in
      just i ths' in
    (meta,sgs',just')
  and rotate_n (meta,sgs,just) =
    let sgs' = (last sgs)::(butlast sgs) in
    let just' i ths =
      let ths' = (tl ths)@[hd ths] in
      just i ths' in
    (meta,sgs',just') in
  fun n -> if n > 0 then funpow n rotate_p
           else funpow (-n) rotate_n;;

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_xgoalstate:goal->xgoalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[((asl,w), reset_goal_counter ())],
      (fun inst [th] -> INSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal";;

(* ------------------------------------------------------------------------- *)
(* Subgoal package but for xgoals.                                           *)
(* ------------------------------------------------------------------------- *)

let current_xgoalstack = ref ([] :xgoalstack);;

let (xrefine:xrefinement->xgoalstack) =
  fun r ->
    let l = !current_xgoalstack in
    let h = hd l in
    let res = r h :: l in
    current_xgoalstack := res;
    !current_xgoalstack;;

let flush_xgoalstack() =
  let l = !current_xgoalstack in
  current_xgoalstack := [hd l];;

let xe tac =
  the_tactic_flag := true;
  xrefine(xby(VALID tac));;

let xr n = xrefine(xrotate n);;

let set_xgoal(asl,w) =
  current_xgoalstack :=
    [mk_xgoalstate(map (fun t -> "",ASSUME t) asl,w)];
  !current_xgoalstack;;

let xg t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   set_xgoal([],t);;

let xb() =
  let l = !current_xgoalstack in
  if length l = 1 then failwith "Can't back up any more" else
  current_xgoalstack := tl l;
  !current_xgoalstack;;

let xp() =
  !current_xgoalstack;;

let xtop_realgoal() =
  let (_,(((asl,w),id)::_),_)::_ = !current_xgoalstack in
  asl,w;;

let xtop_goal() =
  let asl,w = xtop_realgoal() in
  map (concl o snd) asl,w;;

let xtop_thm() =
  let (_,[],f)::_ = !current_xgoalstack in
  f null_inst [];;

(* ------------------------------------------------------------------------- *)
(* Goal id to goal lookup function.                                          *)
(* ------------------------------------------------------------------------- *)

let print_xgoal_of_id (id:goal_id) : unit =
  let gsts = !current_xgoalstack in
  let find_goal (_,xgs,_) = find (fun (g,id0) -> id0 = id) xgs in
  let xg = tryfind find_goal gsts in
  print_xgoal xg;;

(* ------------------------------------------------------------------------- *)
(* Jumping back to a previous state.                                         *)
(* ------------------------------------------------------------------------- *)

let jump_back_to_state n : xgoalstack =
  let l = length !current_xgoalstack in
  if (0 <= n) & (n <= l)
    then (current_xgoalstack := snd (chop_list (l-n) !current_xgoalstack);
          !current_xgoalstack)
    else failwith "Not a valid state number";;

(* ------------------------------------------------------------------------- *)
(* Install the goal-related printers.                                        *)
(* ------------------------------------------------------------------------- *)

#install_printer print_xgoal;;
#install_printer print_xgoalstack;;
