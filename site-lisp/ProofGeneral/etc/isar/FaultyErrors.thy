theory FaultyErrors imports Main
begin

lemma foo: "P --> P" by auto

ML {* Output.error_msg "Fake error"; *} (* now *not* an error *)
ML {* error "Real error" :unit; *}      (* a true error, command fails *)

(* After an error message, the system wrongly thinks the
   command has succeeded, currently 03.01.07.
   This means that undo>redo fails.  
   
   This happens immediately after processing to the error and undoing
   all the way back: redoing "theory" in Eclipse fails, because <undostep> is
   used each time, and it doesn't get far enough.  Repeating theory gives
   the error "can't use theory in theory mode".
     
   The lemma helps exercise the case that <abortheory> is used
   to undo the theory quickly (as it should be, and as it is in
   Emacs, by looking at the buffer), which fixes the "theory" redo.  
   
    1. Do until error
    2. Undo to before lemma
    3. Redo should not give warning message "foo is already defined".
    
   Now fixed for Eclipse and Emacs in Isabelle >=03.01.07.
*)   
end
