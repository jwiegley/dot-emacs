(* This is a test of tracing output for Isabelle. *)

theory trace_simp imports Main begin

text {*
  this produces massive amount of simplifier trace, but terminates
  eventually: *}

declare [[simp_trace]]
ML {* quick_and_dirty := false *}

datatype ord = Zero | Succ ord | Limit "nat => ord"

(* testing comment here *)

text {* this one loops forever *}

lemma "ALL x. f x = g(f(g(x))) ==> f [] = f [] @ []"
  apply simp

