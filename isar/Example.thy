(*  -*- isar -*-

    Example proof document for Isabelle/Isar Proof General.
 
    $Id$

    The first line forces Isabelle/Isar Proof General, otherwise
    you may get the theory mode of ordinary Isabelle Proof General
*)

theory Example = Main:

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"
    thus "B & A"
    proof
      assume A B
	show ?thesis 
	..
    qed
qed
end
