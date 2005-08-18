(********** This file is from the Isabelle distribution **********)

(*  Title:      HOL/Isar_examples/KnasterTarski.thy
    ID:         Id: KnasterTarski.thy,v 1.19 2000/09/17 20:19:02 wenzelm Exp 
    Author:     Markus Wenzel, TU Muenchen

Typical textbook proof example.
*)

header {* Textbook-style reasoning: the Knaster-Tarski Theorem *}

theory KnasterTarski imports Main begin


subsection {* Prose version *}

text {*
 According to the textbook \cite[pages 93--94]{davey-priestley}, the
 Knaster-Tarski fixpoint theorem is as follows.\footnote{We have
 dualized the argument, and tuned the notation a little bit.}

 \medskip \textbf{The Knaster-Tarski Fixpoint Theorem.}  Let $L$ be a
 complete lattice and $f \colon L \to L$ an order-preserving map.
 Then $\bigwedge \{ x \in L \mid f(x) \le x \}$ is a fixpoint of $f$.

 \textbf{Proof.} Let $H = \{x \in L \mid f(x) \le x\}$ and $a =
 \bigwedge H$.  For all $x \in H$ we have $a \le x$, so $f(a) \le f(x)
 \le x$.  Thus $f(a)$ is a lower bound of $H$, whence $f(a) \le a$.
 We now use this inequality to prove the reverse one (!) and thereby
 complete the proof that $a$ is a fixpoint.  Since $f$ is
 order-preserving, $f(f(a)) \le f(a)$.  This says $f(a) \in H$, so $a
 \le f(a)$.
*}


subsection {* Formal versions *}

text {*
 The Isar proof below closely follows the original presentation.
 Virtually all of the prose narration has been rephrased in terms of
 formal Isar language elements.  Just as many textbook-style proofs,
 there is a strong bias towards forward proof, and several bends
 in the course of reasoning.
*}

theorem KnasterTarski: "mono f ==> EX a::'a set. f a = a"
proof
  let ?H = "{u. f u <= u}"
  let ?a = "Inter ?H"

  assume mono: "mono f"
  show "f ?a = ?a"
  proof -
    {
      fix x
      assume H: "x : ?H"
      hence "?a <= x" by (rule Inter_lower)
      with mono have "f ?a <= f x" ..
      also from H have "... <= x" ..
      finally have "f ?a <= x" .
    }
    hence ge: "f ?a <= ?a" by (rule Inter_greatest)
    {
      also presume "... <= f ?a"
      finally (order_antisym) show ?thesis .
    }
    from mono ge have "f (f ?a) <= f ?a" ..
    hence "f ?a : ?H" ..
    thus "?a <= f ?a" by (rule Inter_lower)
  qed
qed

text {*
 Above we have used several advanced Isar language elements, such as
 explicit block structure and weak assumptions.  Thus we have mimicked
 the particular way of reasoning of the original text.

 In the subsequent version the order of reasoning is changed to
 achieve structured top-down decomposition of the problem at the outer
 level, while only the inner steps of reasoning are done in a forward
 manner.  We are certainly more at ease here, requiring only the most
 basic features of the Isar language.
*}

theorem KnasterTarski': "mono f ==> EX a::'a set. f a = a"
proof
  let ?H = "{u. f u <= u}"
  let ?a = "Inter ?H"

  assume mono: "mono f"
  show "f ?a = ?a"
  proof (rule order_antisym)
    show ge: "f ?a <= ?a"
    proof (rule Inter_greatest)
      fix x
      assume H: "x : ?H"
      hence "?a <= x" by (rule Inter_lower)
      with mono have "f ?a <= f x" ..
      also from H have "... <= x" ..
      finally show "f ?a <= x" .
    qed
    show "?a <= f ?a"
    proof (rule Inter_lower)
      from mono ge have "f (f ?a) <= f ?a" ..
      thus "f ?a : ?H" ..
    qed
  qed
qed

end
