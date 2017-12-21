(* See: http://proofgeneral.inf.ed.ac.uk/trac/ticket/266 *)

theory HighlightSize imports Main
begin

lemmas rules = sym refl trans sym refl trans sym refl trans sym refl trans sym refl trans

ML_command {* Pretty.writeln (Pretty.markup Markup.hilite
  [Proof_Context.pretty_fact @{context} ("foo", @{thms rules(1-14)})]) *}

end


