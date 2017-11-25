(* Trac #114:  identifiers starting with "fun" are wrongly coloured *)

forall (funA B: Prop)     (* funA should be all magenta *)
fun (forallA B: Prop)     (* forallA should be all magenta *)

(* Fixed in coq-syntax.el, 8.41 *)

