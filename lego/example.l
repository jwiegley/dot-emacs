(*
    Example proof script for Lego Proof General.
 
    $Id$
*)

Module example Import lib_logic;

Goal {A,B:Prop}(and A B) -> (and B A);
intros;
Refine H;
intros;
andI;
Immed;
Save and_comms;
