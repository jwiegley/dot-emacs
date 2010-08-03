header {* Some tests for \textbf{multiple modes!!} *}

theory MultipleModes imports Main begin

text {* Proper proof text -- \textit{naive version}. *}

theorem and_comms: "A & B --> B & A"
proof
  assume "A & B"
  then show "B & A"
  proof
    assume B and A
    then
   show ?thesis ..
 qed
qed

ML {*
  fun fact 0 = 1 
    | fact n = n * (fact (n-1))

  val x = 7; 
*}

end


