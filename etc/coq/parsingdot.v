(*
	From: 	Pierre Courtieu <Pierre.Courtieu@sophia.inria.fr>
To: 	David Aspinall <da@dcs.ed.ac.uk>
Subject: 	little annoying bug - don't know how to solve it clean
Date: 	Tue, 4 Feb 2003 21:06:55 +0100	
Hi David, I am trying to remove a little bug of coq/pg. It happens when
the user types by mistake two dots, instead of one. It happens quite often
and it should be refused (i.e. not sent to Coq) by pg.

Example *)

Goal (A,B:Prop)(A /\ B) -> (B /\ A).

Intros x y z..

(* Test 1: (setq proof-script-command-end-regexp "[.][\\. \t\n\r]" ) *)

(* Test 2: (setq proof-script-command-end-regexp "[.]\\([\\. \t\n\r]\\)") *)

(*
What happens now is that "Intros x y z.." is sent to Coq, Coq reads the
first part of the command "Intros x y z.", executes it, and then throws an
error because of the second part "." is not correct. So pg stays before
"Intros x y z..", which is incorrect since "Intros x y z." has been
acceted by Coq.

Remember that the current config of Coq is the following:

(setq proof-script-command-end-regexp "[.]\\([ \t\n\r]\\)" )

this is due to the fact that foo.bar is a valid identifier (Module/Section).

Problem is that:

 - I cannot use "[.]\\([^a-Z.]\\)" because if we have:

   Intros x y z..
   Auto.

   then the command sent to Coq would be "Intros x y z..  Auto.", which is
   worse.

 - I cannot use "[.]" because it would cut qualified names ("foo.bar").

Actually what I would like to use is a proof-not-allowed-command-end
variable, or more generally a hook for the function
proof-script-parse-function.

I have defined (not commited) a coq-script-parse-function below to do
the check by hand, it is a copy of proof-script-generic-parse-cmdend,
with a check for ".." at the end (error if yes).

The behavior we want is really an error here: It must not be sent to
coq at all!
*)