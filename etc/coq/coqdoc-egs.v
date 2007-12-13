(* Some tests/examples of coqdoc regions in Coq files, 
   used with MMM configuration (ProofGeneral -> Options -> Multiple Modes. *)


(** This is a coqdoc plain text region.

    After editing/changing regions in mmm mode, use C-x % C-b to reparse
*)


(** %This is a special case of a \LaTeX{} region recognised by MMM.
\begin{quote}
Emacs will be in \texttt{LaTeX} mode when editing this region.
\end{quote}
 % *)


(** #Similarly, this is an HTML region, edited in HTML mode # *)


(* Finally, here is some *)
<<
verbatim text
>>
(* in text mode *)

