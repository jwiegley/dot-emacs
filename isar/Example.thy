
theory Example = Main:;

lemma "A --> B --> A";
proof;
  assume A;
  show "B --> A";
  proof;
  qed;
qed;

end;
