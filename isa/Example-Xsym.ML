(*
    Example proof script for Isabelle Proof General.

    $Id$

    Just a version of Example.ML using XSymbol.

    Also subscripts/superscripts/bold:  A\<^sup>1 \\<or> A\<^sub>2 \\<or> A\<^bold>3 
    [NB: these can't be used in identifiers or otherwise
     parsed by Isabelle unless declared as part of a theory's 
     concrete syntax, see docs or examples in HOL/IMP.]
*)    

Goal "A \\<and> B \\<longrightarrow> B \\<and> A";
by (rtac impI 1);
by (etac conjE 1);
by (rtac conjI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "and_comms";
