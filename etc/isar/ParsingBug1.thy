(* 
  This is a small test case for parsing the { nested proof } phrase.

  This case causes problems with the new parsing mechanism, see
  comments in isar/isar-syntax.el and generic/proof-script.el
*)
  

theory ParsingBug1 imports Main begin

theorem "P"
proof -
  assume a: "Q"
  {fix i have "Q" sorry}
qed
