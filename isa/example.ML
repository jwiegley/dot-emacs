goal HOL.thy "(A & B)-->(B & A)";
br impI 1;
br conjI 1;
be conjE 1;
ba 1;
be conjE 1;
ba 1;
qed "and_comms";
