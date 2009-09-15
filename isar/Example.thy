(*
      Example proof document for Isabelle/Isar Proof General.
   
      $Id$
*)


theory Example imports Main begin

text {* Proper proof text -- \textit{naive version}. *}

theorem and_comms: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then show "B \<and> A"
  proof
    assume B and A
    then show ?thesis ..
 qed
qed

text {* Unstructured proof script. *}

theorem  "A & B --> B & A"
by and_comms


  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply assumption
done


end
