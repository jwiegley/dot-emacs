theory Trac189 imports Main begin


(* Undoing of a diagnostic: exercises proof-no-command *)

lemma "True"
  apply (rule TrueI)
  thm TrueI
