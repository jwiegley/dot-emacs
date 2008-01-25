(* Pierre: could you add some real test cases to this file, please?
   e.g. a file that can be processed, and indented how you want ---
   so TAB makes no difference to indentation  (bad examples in comments)
*)


(* First problem: matching compound reserved words *)

  Syntactic Definition foo := bar.

(* Neither of these are good enough: the backwards search simply finds "Definition" first *)
(* (re-search-backward "\\(\\<Syntactic\\>\\s-+\\)?Definition") *)
(* (posix-search-backward "\\(\\<Syntactic\\>\\s-+\\)?Definition") *)

(* I suppose Java has this issue too, so the syntax designers of Coq are not
   really to blame...  However, if you take a look at the Emacs code used for
   calculating Java indentation you will get a shock!!   

   Proof General's is much simpler.  I sugest introducing another function
   (and regexp)

      proof-within-compound-reserved-word

   which we can use as a guard for repeating the regexp search backwards, as
   an extra condition in proof-indent-goto-prev (similarly to 
   proof-looking-at-syntactic-context which resumes the search in case we
   landed in a string or comment).

   Pierre, do you want to try that?

   - da
*)



(* Second problem: hanging indentation of cases *)

(* Desirable indent  (Pierre: not quite what you said: you had different
indent between Cases and next line in nested case)

Definition f := 
 Cases i with   
  x => Cases x with
	z => #
        | # => #
        | # => #       
       end 
 end
*)

(* currently: *)

Definition f := 
 Cases i with 
  x => Cases x with
	z => # 
       | a => b
       | # => #       
       end
     end

(* Nasty example from Trac http://proofgeneral.inf.ed.ac.uk/trac/ticket/173 *)    
Theorem p : forall (P : Prop), P -> P.
Proof.
  try (simpl 
    in *). 
    intros P H. apply H.  (* da: shouldn't we outdent again here? *)
Qed.
