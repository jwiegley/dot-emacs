(* In order to test the latest thm deps setup, consider this example: *)

theory Depends imports Main begin

  lemma I: "A ==> A" and K: "A ==> B ==> A" .

(*
This reports I, K depending on several things; for your internal
dependency graph you may interpret this as each member of {I, K} depending
on all the deps.
*)

end

