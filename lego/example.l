(*
    Example proof script for Lego Proof General.
 
    $Id$
*)

Module example Import lib_logic;

Goal and_commutes: {A,B:Prop}(and A B) -> (and B A);
intros; andI;
Refine H; intros; Immed; Refine H; intros; Immed;
Save and_commutes;


