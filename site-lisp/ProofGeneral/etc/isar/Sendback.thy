(* $Id$ *)

header {* Demonstrate the use of literal command markup *}

theory Sendback imports Main begin

ML {*
fun sendback cmd = ProofGeneral.sendback "Try this:" [Pretty.str cmd]
fun sendback2 cmd1 cmd2 =
  writeln ("Try: " ^ (Markup.markup Markup.sendback cmd1) ^ " or " ^
	             (Markup.markup Markup.sendback cmd2))
*}

theorem and_comms: "A & B --> B & A"
proof
  ML_command {* sendback "assume \"A & B\"" *}
  ML_command {* sendback "show \"B & A\"" *}
  ML_command {* sendback2 "proof assume B and A then" 
			  "proof assume A and B then" *}
  ML_command {* sendback "show ?thesis .. qed" *}
  ML_command {* sendback "qed" *}
qed

