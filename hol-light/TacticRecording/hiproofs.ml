(* ========================================================================== *)
(* HIPROOFS (HOL LIGHT)                                                       *)
(* - Hiproofs and refactoring operations                                      *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


(* This file defines a hiproof [1] datatype and various operations on it.     *)
(* The datatype closely resembles that proposed in [2], with the notable      *)
(* difference that atomic steps carry their arity.                            *)

(* [1] "Hiproofs: A Hierarchical Notion of Proof Tree", Denney, Power &       *)
(*    Tourlas, 2006.                                                          *)
(* [2] "A Tactic Language for Hiproofs", Aspinall, Denney & Luth, 2008.       *)



(* ** DATATYPE ** *)


(* Hiproof datatype *)

(* Note that atomic tactics are labelled with their arity, corresponding to   *)
(* how many subgoals they result in.  An arity of -1 indicates unknown, and 0 *)
(* indicates a tactic that completes its goal.                                *)

type hiproof =
    Hactive                             (* Active subgoal *)
  | Hatomic of (finfo * int)            (* Atomic tactic + arity *)
  | Hidentity                           (* Null, for wiring *)
  | Hlabelled of (finfo * hiproof)      (* Box *)
  | Hsequence of (hiproof * hiproof)    (* Serial application *)
  | Htensor of hiproof list             (* Parallel application *)
  | Hempty;;                            (* Completed goal *)


(* Constructors and destructors *)

let hsequence (h1,h2) = Hsequence (h1,h2);;

let dest_hsequence h =
  match h with
    Hsequence hh -> hh
  | _   -> failwith "Not a sequence hiproof";;

let is_hsequence h = can dest_hsequence h;;

let dest_atomic_hiproof h =
  match h with
    Hatomic (info,n) -> (info,n)
  | _ -> failwith "dest_atomic_hiproof: Not an atomic hiproof";;


(* Arity *)

let rec hiproof_arity h =
  match h with
    Hactive           -> 1
  | Hatomic (_,n)     -> n
  | Hidentity         -> 1
  | Hlabelled (_,h0)  -> hiproof_arity h0
  | Hsequence (h1,h2) -> hiproof_arity h2
  | Htensor hs        -> sum (map hiproof_arity hs)
  | Hempty            -> 0;;


(* Hitrace *)

type hitrace =
   Hicomment of int list
 | Hiproof of hiproof;;



(* ** REFACTORING OPERATIONS ** *)


(* Generic refactoring operation *)

(* Applies a refactoring function 'foo' at every level of hiproof 'h', from   *)
(* bottom up.  If the 'r' flag is set then refactoring is repeated bottom up  *)
(* whenever 'foo' makes a change.  Note that if 'foo' makes no change then it *)
(* should just return its input hiproof (rather than raise an exception).     *)

let rec refactor_hiproof r foo h =
  let h' =
     match h with
       Hlabelled (info,h0)
          -> let h0' = refactor_hiproof r foo h0 in
             Hlabelled (info,h0')
     | Hsequence (h1,h2)
          -> let h1' = refactor_hiproof r foo h1 in
             let h2' = refactor_hiproof r foo h2 in
             Hsequence (h1',h2')
     | Htensor hs
          -> let hs' = map (refactor_hiproof r foo) hs in 
             Htensor hs'
     | _  -> h in
  let h'' = if (h' = h) then h else h' in
  let h''' = foo h'' in
  if r & not (h''' = h'')
    then refactor_hiproof r foo h'''
    else h''';;


(* Trivial simplification *)

(* Removes basic algebraic identities/zeros.                                  *)

let collapse_tensor h hs =
  match h with
    Hempty      -> hs
  | Htensor hs0 -> hs0 @ hs
  | _           -> h :: hs;;

let trivsimp_hiproof h =
  let trivsimp h =
     match h with
       Hatomic ((Some"ALL_TAC",[]), _) -> Hidentity
     | Hsequence (h1, Hempty)    -> h1
     | Hsequence (h1, Hidentity) -> h1
     | Hsequence (Hidentity, h2) -> h2
     | Htensor []    -> Hempty
     | Htensor [h0]  -> h0
     | Htensor hs0   -> if (forall (fun h0 -> h0 = Hidentity) hs0)
                          then Hidentity
                          else Htensor (foldr collapse_tensor hs0 [])
     | _   -> h in
  refactor_hiproof true trivsimp h;;


(* Matching up lists of hiproofs *)

let rec matchup_hiproofs hs1 hs2 =
  match hs1 with
    [] -> []
  | h1::hs01
       -> let n1 = hiproof_arity h1 in
          let (hs2a,hs2b) = try chop_list n1 hs2
                with Failure _ ->
                     if (n1 = -1)
                       then failwith "matchup_hiproofs: unknown arity"
                       else failwith "matchup_hiproofs: Internal error - \
                                                      inconsistent arities" in
          Hsequence (h1, Htensor hs2a) :: (matchup_hiproofs hs01 hs2b);;


(* Separating out lists of hiproofs *)

let separate_hiproofs0 h (hs01,hs02) =
  match h with
    Hsequence (h1,h2)
       -> (h1::hs01, h2::hs02)
  | _  -> let n = hiproof_arity h in
          let h2 = Htensor (copy n Hidentity) in
          (h::hs01, h2::hs02);;

let separate_hiproofs hs = foldr separate_hiproofs0 hs ([],[]);;


(* Delabelling *)

(* Strips out any boxes from the proof.  Note that some boxes, such as        *)
(* 'SUBGOAL_THEN', cannot be stripped out without spoiling the proof, and so  *)
(* are left alone.                                                            *)

let delabel_hiproof h =
  let delabel h =
     match h with
       Hlabelled ((Some "SUBGOAL_THEN",_),h0)
          -> h
     | Hlabelled (_,h0)
          -> h0
     | _  -> h in
  refactor_hiproof true delabel h;;


(* Right-grouping *)

(* Expands the proof into a right-associative sequence, with tensor           *)
(* compounding on the right.  Leaves all boxes unchanged.                     *)

let rightgroup_hiproof h =
  let rightgroup h =
     match h with
       Hsequence (Hsequence (h1, Htensor hs2), Htensor hs3)
          -> Hsequence (h1, Htensor (matchup_hiproofs hs2 hs3))
     | Hsequence (Hsequence (h1, Htensor hs2), h3)
          -> Hsequence (h1, Htensor (matchup_hiproofs hs2 [h3]))
     | _  -> h in
  refactor_hiproof true rightgroup h;;


(* Left-grouping *)

(* Expands the proof into a left-associative sequence.                        *)

let leftgroup_hiproof h =
  let leftgroup h =
     match h with
       Hsequence (h1, Hsequence (h2, h3))
          -> Hsequence (Hsequence (h1,h2), h3)
(*     | Hsequence (h1, Htensor hs2)
          -> if (exists is_hsequence hs2)
               then let (hs2a,hs2b) = separate_hiproofs hs2 in
                    Hsequence (Hsequence (h1, Htensor hs2a), Htensor hs2b)
               else h  *)
     | _  -> h in
  refactor_hiproof true leftgroup h;;


(* THEN insertion *)

(* Looks for opportunities to use 'THEN' tacticals.  Note that this disrupts  *)
(* arity consistency.                                                         *)

let thenise_hiproof h =
  let thenise h =
     match h with
       Hsequence (h1, Htensor (h2::h2s))
          -> if (forall (fun h0 -> h0 = h2) h2s)
               then Hlabelled ((Some "THEN", []), h)
               else h
     | Hsequence (h1, Hsequence (Htensor (h2::h2s), h3))
          -> if (forall (fun h0 -> h0 = h2) h2s)
               then Hsequence
                     (Hlabelled ((Some "THEN", []),
                                 Hsequence (h1, Htensor (h2::h2s))), h3)
               else h
     | _  -> h in
  refactor_hiproof false thenise h;;



(* ** OTHER OPERATIONS ** *)


(* Tactic trace *)

(* Gives a trace of the basic tactics used in the proof, ignoring how they    *)
(* were combined by tacticals.                                                *)

let rec hiproof_tactic_trace0 h =
  match h with
    Hactive
       -> [active_info]
  | Hatomic (info, _)
       -> [info]
  | Hidentity
       -> []
  | Hlabelled (info,h0)
       -> hiproof_tactic_trace0 h0
  | Hsequence (h1,h2)
       -> (hiproof_tactic_trace0 h1) @ (hiproof_tactic_trace0 h2)
  | Htensor hs
       -> flat (map hiproof_tactic_trace0 hs)
  | Hempty
       -> [];;

let hiproof_tactic_trace h = (hiproof_tactic_trace0 o delabel_hiproof) h;;


(* Block trace *)

(* Gives a trace of the hiproofs used in the proof, stopping at boxes.        *)

let rec hiproof_block_trace0 ns0 h =
  match h with
  | Hsequence (h1,h2)
       -> (hiproof_block_trace0 ns0 h1) @ (hiproof_block_trace0 ns0 h2)
  | Htensor hs
       -> let nss = map (fun n -> ns0 @ [n]) (1 -- length hs) in
          flat (map (fun (ns,h) -> (Hicomment ns) :: hiproof_block_trace0 ns h)
                    (zip nss hs))
  | _  -> [Hiproof h];;

let hiproof_block_trace h = hiproof_block_trace0 [] h;;
