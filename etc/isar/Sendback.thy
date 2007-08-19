(* Demonstrate the use of literal command markup *)

theory Sendback imports Main begin

ML {* val pgasciiN = "PGASCII";
fun special oct =
  if print_mode_active pgasciiN then chr 1 ^ chr (ord (oct_char oct) - 167)
  else oct_char oct; 
fun sendback cmd = writeln ("Try this: \n   " ^ (special "376") ^ cmd ^ (special "377") ^ "\n\n")
*}

ML {*
fun sendback2 cmd = (writeln "Try this: "; 
		    ProofGeneral.sendback cmd [])
*}

theorem and_comms: "A & B --> B & A"
proof
  ML {* sendback "assume \"A & B\"" *}
  ML {* sendback "then; show \"B & A\"" *}
  ML {* sendback "proof; assume B and A; then" *}
  ML {* sendback "show ?thesis; ..; qed" *}
  ML {* sendback "qed" *}
qed
