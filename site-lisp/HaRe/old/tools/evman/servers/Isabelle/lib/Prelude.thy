theory Prelude
imports PLogic
begin

subsection {* Ints *}

types HInt = "int lift"

instance lift :: (zero) zero ..
instance lift :: (one) one ..
instance lift :: (number) number ..

defs (overloaded)
  zero_lift_def: "0 \<equiv> Def 0"
  one_lift_def: "1 \<equiv> Def 1"
  number_of_lift_def: "number_of w \<equiv> Def (number_of w)"

consts
  even :: "HInt \<rightarrow> tr"
  odd :: "HInt \<rightarrow> tr"
  less' :: "'a::ord lift \<rightarrow> 'a lift \<rightarrow> tr" (infixl "`<" 50)
  plus' :: "'a::plus lift \<rightarrow> 'a lift \<rightarrow> 'a lift" (infixl "`+" 65)

defs
  even_def: "even \<equiv> flift2 Parity.even"
  odd_def: "odd \<equiv> flift2 (\<lambda>x. \<not> Parity.even x)"
  less'_def: "less' \<equiv> FLIFT x y. Def (x < y)"
  plus'_def: "plus' \<equiv> FLIFT x y. Def (x + y)"


subsection {* Tuples *}
nonterminals typs

syntax
  "_typs" :: "[type,typs] \<Rightarrow> typs" ("_,/ _")
  "" :: "type \<Rightarrow> typs" ("_")
  "_tupletype" :: "[type, typs] \<Rightarrow> type" ("<_,/ _>")

translations
  (type) "<a, b, c>" == (type) "<a, <b, c>>"
  (type) "<a, b>" == (type) "a * b"

constdefs
  fst :: "<'a,'b> \<rightarrow> 'a"
  "fst \<equiv> cfst"
  snd :: "<'a,'b> \<rightarrow> 'b"
  "snd \<equiv> csnd"

lemma fst_tuple [simp]: "fst\<cdot><x, y> = x"
by (simp add: fst_def)

lemma snd_tuple [simp]: "snd\<cdot><x, y> = y"
by (simp add: snd_def)

translations
"case s of <x,y> => t" == "csplit$(LAM x y. t)$s"

(*
domain ('a,'b) T2 = T2 (lazy fst :: "'a") (lazy snd :: "'b") ("\<guillemotleft>_,/ _\<guillemotright>")
syntax T2 :: "type \<Rightarrow> type \<Rightarrow> type" ("\<guillemotleft>_,/ _\<guillemotright>")

domain ('a,'b,'c) T3 = T3 (lazy "'a") (lazy "'b") (lazy "'c")
syntax T3 :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type" ("\<guillemotleft>_,/ _,/ _\<guillemotright>")
*)

subsection {* Lists *}

domain 'a L0
  = Nil0 ("[:]")
  | Cons0 (lazy head :: "'a") (lazy tail :: "'a L0") (infixr "`:" 65)

syntax
  "L0" :: "type \<Rightarrow> type" ("[_]")
  "_L0" :: "args \<Rightarrow> 'a L0" ("[:(_):]")

translations
  "[:x, xs:]" == "x `: [:xs:]"
  "[:x:]" == "x `: [:]"

consts length_c :: "['a] \<rightarrow> HInt"
fixrec
  "length_c\<cdot>[:] = 0"
  "length_c\<cdot>(x `: xs) = 1 `+ length_c\<cdot>xs"

consts zip :: "['a] \<rightarrow> ['b] \<rightarrow> ['a * 'b]"
fixrec
  "zip\<cdot>[:]\<cdot>ys = [:]"
  "zip\<cdot>(x `: xs)\<cdot>[:] = [:]"
  "zip\<cdot>(x `: xs)\<cdot>(y `: ys) = <x, y> `: zip\<cdot>xs\<cdot>ys"

fixpat zip_stricts [simp]: "zip\<cdot>\<bottom>\<cdot>ys" "zip\<cdot>(x `: xs)\<cdot>\<bottom>"

subsection {* Either type *}

domain ('a,'b) Either = Left (lazy "'a") | Right (lazy "'b")

end
