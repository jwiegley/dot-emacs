(*
    Example proof document for Isabelle/Isar Proof General.
 
    $Id$
*)


theory Example = Main:;

theorem and_comms: "A & B --> B & A";
proof;
  assume "A & B";
  thus "B & A";
  proof;
    assume A B;
    show ?thesis; ..;
  qed;
qed;

end;
