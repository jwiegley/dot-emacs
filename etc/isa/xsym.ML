(* a few token characters to exercise X-Symbol *)

Goal "A \\<and> B  \\<longrightarrow> B \\<and> A";
by (rtac impI 1);
by (etac conjE 1);
by (rtac conjI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "and_comms";

3;

4;

print "hello";

writeln "hello";
error "hello";
