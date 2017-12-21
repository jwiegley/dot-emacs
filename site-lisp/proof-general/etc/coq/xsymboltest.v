(* Grammar for symbols:
  a symbol is encoded only if 
   - preceded by _ or some space or some symbol
  **and**
   - followed by _ or some space or some symbol

  Grammar for sub/superscript: 

   - a double _ introduces a subscript that ends at the first space
   - a double ^ introduces a superscript that ends at the first space
  
   - a _ followed by { introduces a subscript
     expression that ends at the first }
   - a ^ followed by { introduces a superscript
     expression that ends at the first }
 *)



foo_alpha_1_beta_3  (* this should appear like foo_a_1_B_3 where a and B are greek *)
delta__1 delta^^1          (* greek delta with a sub 1 and the same with super 1 *)
x_{a+b} x^{a+b}         (* x with a+b subscripted and then superscripted *)
philosophi   (* no greek letter should appear on this line *)
aalpha alphaa (* no greek letter *)
_alpha           (* _a where a is greek *)
alpha_           (* a_ where a is greek *)



Fixpoint toto (x:nat) {struct x} : nat := (* nat should appear as |N *)
  match x with
    | O => O        (* double arrow here *)
    | S y => toto y (* double arrow here *)
  end.

Lemma titi : forall x:nat,x=x. (* symbolique for-all and nat *)
 