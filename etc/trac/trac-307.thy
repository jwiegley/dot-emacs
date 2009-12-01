
theory trac307 imports Main begin

lemma foo: "Suc x = Suc x" ..

(* 2. Go to the simp-command that does not terminate
   3. Perform the following actions:
      Undo, Interrupt, Undo, Next
   Sync is lost.
*)

lemma "P (Suc x)" apply (simp add: foo)

end

