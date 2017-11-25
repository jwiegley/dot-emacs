Ltac bar k := k tt.

(* The next tactic definition seems to get stuck when processing in PG.
   It works fine typed into coqtop and also works if a couple of the
   match lines are removed.  

   It does seem to be something to do with the line length, as if
   the lines are commented out the same problem happens.  

   See http://proofgeneral.inf.ed.ac.uk/trac/ticket/447 
*)
Ltac foo x := 
  bar ltac:(fun a => 
  bar ltac:(fun b => 
  bar ltac:(fun c => 
  bar ltac:(fun d => 
  bar ltac:(fun e => 
  bar ltac:(fun f => 
  bar ltac:(fun g => 
  bar ltac:(fun h =>  
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in  
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in 
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  let x := match tt with | tt => constr:(1) end in
  idtac)))))))).

Ltac wim x := foo x.
