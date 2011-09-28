(* Not really a theory of parsing, but a test of Proof General's
   parsing for Isabelle/Isar.... *)

(* First, start with successive comments before a real command *)

theory Parsing imports Main begin

(* Then a comment *after* a command.  Also one which mentions
   the names of commands, such as theory or theorem or proof itself,
   never mind thus assume end qed. *)

(* At the moment, successive comments are amalgamated, and comments
   following commands are wrapped into the command (so cannot be
   hidden). *)

text {* Isar theories can have arbitrary literal text,
          so the text must be ignored as well; thus. *}

(* Those pieces of literal text are treated as another kind
   of comment. What gets slight risky is when they're
   text {* nested one inside the other. *}.
   If Emacs confuses the two kinds of sequence, then
   this can go wrong.
*)

text {* nesting (* may be the other way around *) *}

(* The main type of comment (* may be nested *)
   just like in SML. GNU Emacs [21.1] supports this now, nicely,
   but XEmacs [21.4.8] doesn't, so colouration goes wrong.  
   If there are any command names inside this comment
   (e.g. theorem), it breaks the parser in XEmacs. 
   [ To process this in XEmacs, delete "thxxrem" above, C-c C-n, C-x u ]
*)

(* Let's do my favourite proof. *)

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"  (* it's "important" that we test "strings" I guess *)
  then show "B & A"
  proof
    assume B A (* blah boo bah *)
    then show ?thesis (* bah boo bah *)
      ..
  qed
qed

(* Another thing: nesting with { and } can be tricky. *)

theorem and_comms_again: "A & B --> B & A"
proof
  assume "A & B" 
  then show "B & A"
  proof
    {
      assume B A
      then show ?thesis
	..
    }
  qed
qed

(* Now the end of file is coming up.  Funny things happen
   because PG only knows how commands start, not how they end.
*)

end
(* That's the final command and it includes any text which follows it.
   An oddity is that if there is a syntax error - unclosed comment
   or whatever, after the last end, PG will say that it can't find
   a complete command! 

   Another oddity with comments at the end: these are left as "commands". *)

