(* Demonstrates a bug with XEmacs 21.1: after procesing, between
   two terms, buffer-syntactic-context returns "string".  
   But _before_ processing, it correctly returns "nil".
   Even when regions are removed, still get "string" returned
   after processing started. 

   Bug doesn't occur in GNU Emacs (using imp of buffer-syntactic context
   provided in proof-compat.el), nor in XEmacs 21.4

   Workaround added Fri Aug 10 13:55:28 BST 2001
*)

theory XEmacsSyntacticContextProb imports Main begin

term "
(f x)" 

term "(f x)"

end
