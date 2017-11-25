theory "Names In Strings" imports Main begin   (* NB: must also check case without quotes! *)

lemma foo: "B --> B" by auto

lemma "foo bar": "B --> B" by auto

lemma "foo-wiggle-bar": "B --> B" by auto

theorem "x b": "B --> B" by auto

(* NB: various other regexps and settings based on them are sensitive
   to grouping in isar-name-regexp: should check function menu, imenu,
   as well as undo behaviour. *)

end


(*

I noticed the following minor problem with Isabelle and 
ProofGeneral:


>>   theory "a" = Main:
>>   Proof General -> Use -> Retract:
>>   *** Outer syntax error: end of input expected,
>>   *** but identifier "a" was found

Regards,
Tjark

*)


