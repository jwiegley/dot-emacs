
theory Example = Main:;

lemma and_comms: "A & B --> B & A";
proof;
  assume "A & B";
  show "B & A";
  proof;
    from prems; show B; ..;
    from prems; show A; ..;
  qed;
qed;

end;
