(*
    Example uses of X-Symbol symbols in Coq.
    See end for syntax summary.

    Pierre Courtieu

    $Id$
*)

Fixpoint toto (x:nat) {struct x} : nat := (* nat should appear as |N *)
  match x with
    | O => O        (* double arrow here *)
    | S y => toto y (* double arrow here *)
  end.

Lemma titi : forall x:nat,x=x. (* symbolique for-all and nat *)
 

(* this should appear like foo'a'1_B_3 where a and B are greek *)
Variable foo'alpha'1_beta_3 : Set.  

(* greek delta with a sub 1 and the same with super 1 *)
Variable delta__1 delta^^1 : Set. 

(* x with a+b subscripted and then superscripted *)
Variable x_{a+b} x^{a+b} : Set. 

(* no greek letter should appear on this next line! *)
Variable philosophi   : Set.

(* same here *)
Variable aalpha alphaa : Set.


(* _a where a is greek *)
Variable _alpha : Set.

(* a_ where a is greek *)
Variable alpha_ : Set.


alpha lhd rhd lambda forall exists exists exist 

(* 
Grammar for X-Symbols:

  Symbols include sequences naming Greek letters ("Lambda", "lambda", etc),
  connectives /\, \/, etc.  See the X-Symbol char table for details,
  C-= C-=  (control with equals twice).

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


