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

(* but on the other hand, who knows? *)

text {* Proper proof text -- \textit{advanced ve"rs"ion}. What do you think?  Who knows. *}
theorem "B & A --> A & B"
proof
  assume "B & A"  -- "one of those kinds"
  then obtain A and B ..
  then show "A & B" ..
qed 


(* foo bar wiggle *)

theorem "A & B --> B & A"
proof
  assume "A & B"
  then obtain B and A ..
  then show "B & A" .. 
qed


theorem "A & B --> B & A"
proof
  assume "A & B"
  then obtain B and A ..
  then show "B & A" .. 
qed


text {* Unstructured proof script. *}

theorem  "A & B --> B & A" -- {* foo bar *}
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply assumption
done

end
