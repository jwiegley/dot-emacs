(* $Id$ *)

header {* Demonstrate the use of literal command markup *}

theory Sendback imports Main begin

ML {*
fun sendback cmd = ProofGeneral.sendback "Try this:" [Pretty.str cmd]
*}

theorem and_comms: "A & B --> B & A"
proof
  ML {* sendback "assume \"A & B\"" *}
  ML {* sendback "then; show \"B & A\"" *}
  ML {* sendback "proof; assume B and A; then" *}
  ML {* sendback "show ?thesis; ..; qed" *}
  ML {* sendback "qed" *}
qed
