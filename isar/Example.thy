(*  -*- isar -*-

      Example proof document for Isabelle/Isar Proof General.
   
      $Id$

      The first line forces Isabelle/Isar Proof General, otherwise
      you may get the theory mode of ordinary Isabelle Proof General
      See the manual for other ways to select Isabelle/Isar PG.
*)

theory Example = Main:

text {* Proper proof text -- naive version. *}

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"
  then show "B & A"
  proof
    assume B and A
    then show ?thesis ..
  qed
qed


text {* Proper proof text -- advanced version. *}

theorem "A & B --> B & A"
proof
  assume "A & B"
  then obtain B and A ..
  then show "B & A" ..
qed


text {* Unstructured proof script. *}

theorem "A & B --> B & A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

end
