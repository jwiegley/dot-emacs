(*
      Example proof document for Isabelle/Isar Proof General.
   
      $Id$
*)


theory Example imports Main begin

text {* Proper proof text -- \textit{naive version}. *}

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"
  then show "B & A"
  proof
    assume B and A
    then show ?thesis ..
 qed
qed

(* quite nice I think but what if I type here? *)

text {* Unstructured proof script. *}

theorem  "A & B --> B & A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply assumption
done


end
