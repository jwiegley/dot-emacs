(* See http://proofgeneral.inf.ed.ac.uk/trac/ticket/166 *)

theory IllegalEscape imports Main begin

    lemma X: "a=b ==> b=a" by simp -- "Text with \illegal escape sequence"
      oops
end 
