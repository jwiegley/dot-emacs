(* See http://proofgeneral.inf.ed.ac.uk/trac/ticket/274 *)

theory BigErrors imports Pure 
begin

consts foo :: 'a
consts bar :: 'a

ML {* warning (cat_lines (replicate 300 "This is a big warning message")); *}

(* Attempt to get a big error with "error" fails, but we can use printing function
   (see FaultyErrors.thy) *)

ML {* Output.error_msg (cat_lines (replicate 10000 "This is a big error message")); *}

(* Note about FaultyErrors: the above generates an error
   interactively but does *not* generate an error when 
   required by another theory, see, BigErrorsNested *)

end
