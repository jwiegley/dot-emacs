(* see trac #206 *)

theory Trac206 imports Main begin

(* The special markup (for terms etc.) is not processed in minibuffer
messages. For example: *)

ML_command {* warning (Syntax.string_of_typ @{context} @{typ 'a}) *}

term "\<lambda> x. x"

(* Here the decoration for 'a shows up as funny control characters,
instead of proper font-lock colouring.  *)

end

