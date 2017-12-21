(* 

We now support persistent Isabelle sessions with Proof General, preserving
the state of loaded theories (before I used to have a few explicit
``bombs'' to prevent this).  When saying ``Exit Isabelle/Isar'' the image
is committed back.  It's not possible to go continue partially processed
theory buffer, but users could expect to have a fully processed theory
stored properly.  The latter requires scripting to be disabled first, in
order to inform the process to store the finished theory.

To spare users to think about this, the ``Exit Isabelle/Isar''
operation disables scripting automatically.

Produce a writable Isabelle session like this:

  isabelle -q HOL Foo

Now start PG and start a process with the Foo logic image.

Tests:

  Process this file, exit, start.  
  Unprocess, exit, start.		[FAILS with Isabelle2002]

*)


theory Persistent imports Main begin

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"
  then show "B & A"
  proof
    assume B and A
    then show ?thesis ..
  qed
qed

end
