
theory trace_simp = Main:

text {*
  this produces massive amount of simplifier trace, but terminates
  eventually: *}

ML {* set trace_simp *}
ML {* reset quick_and_dirty *}

datatype ord = Zero | Succ ord | Limit "nat => ord"


text {* this one loops forever *}

lemma "ALL x. f x = g(f(g(x))) ==> f [] = f [] @ []"
  apply simp

