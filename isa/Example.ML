(*  -*- isa -*-

    Example proof script for Isabelle Proof General.

    $Id$

    The line at the top of this comment forces 
    Proof General's classic Isabelle mode
    (instead of Isar: you can't use both at once).
*)

Goal "A & B --> B & A";
  by (rtac impI 1);
  by (etac conjE 1);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (assume_tac 1);
qed "and_comms";
