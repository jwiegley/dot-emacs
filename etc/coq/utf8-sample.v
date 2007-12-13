(* -*- coding: utf-8; -*- *)

Add LoadPath "/usr/lib/coq/ide". 
Require Import utf8.

(* Printing of unicode notation, in *goals* *)
Lemma test : forall A:Prop, A -> A.
auto.
Qed.

(* Parsing of unicode notation, in *goals* *) 
Lemma test2 : ∀ A:Prop, A → A.
intro.
intro.
auto.
Qed.

(* Printing of unicode notation, in *response* *)
Check (fun (X:Set)(x:X) => x).

(* Parsing of unicode notation, in *response* *)
Check (∀A, A→A).