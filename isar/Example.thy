
theory Example = Main:;

text {*
 Just a few tiny examples to get an idea of how Isabelle/Isar proof documents
 may look like.
 *};

lemma I: "A --> A";
proof;
  assume A;
  show A; .;
qed;

lemma K: "A --> B --> A";
proof;
  assume A;
  show "B --> A";
  proof;
    show A; .;
  qed;
qed;

text {*
 This one is a good test for ProofGeneral to cope with block-structured
 proof texts.  Have fun with automatic indentation!
 *};

lemma S: "(A --> B --> C) --> (A --> B) --> A --> C";
proof;
  assume "A --> B --> C";
  show "(A --> B) --> A --> C";
  proof;
    assume "A --> B";
    show "A --> C";
    proof;
      assume A;
      show C;
      proof (rule mp);
	show "B --> C"; by (rule mp);
        show B; by (rule mp);
      qed;
    qed;
  qed;
qed;


end;
