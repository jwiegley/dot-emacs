theory PLogic
imports HOLCF
begin

constdefs
  set_bind :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set" (binder "SET " 10)
  "set_bind f \<equiv> {(x,y). y \<in> f x}"

  strong :: "'a::pcpo set \<Rightarrow> 'a set"
  "strong A \<equiv> A - {\<bottom>}"

  arrow :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<rightarrow> 'b) set"
  "arrow A B \<equiv> {f. \<forall>x\<in>A. f\<cdot>x \<in> B}"

  arrow2 :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<rightarrow> 'b) u set"
  "arrow2 A B \<equiv> insert \<bottom> {up\<cdot>f |f. \<forall>x\<in>A. f\<cdot>x \<in> B}"

  lifted :: "('a \<rightarrow> tr) \<Rightarrow> 'a set"
  "lifted p \<equiv> {x. p\<cdot>x \<sqsubseteq> TT}"

  cong1 :: "('a \<rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"
  "cong1 x A \<equiv> \<Union>a\<in>A. {x\<cdot>a}"

  cong2 :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set"
  "cong2 x A B \<equiv> \<Union>a\<in>A. \<Union>b\<in>B. {x\<cdot>a\<cdot>b}"

  cong3 :: "('a \<rightarrow> 'b \<rightarrow> 'c \<rightarrow> 'd) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set \<Rightarrow> 'd set"
  "cong3 x A B C \<equiv> \<Union>a\<in>A. \<Union>b\<in>B. \<Union>c\<in>C. {x\<cdot>a\<cdot>b\<cdot>c}"

lemma set_bind: "((x,y) \<in> set_bind f) = (y \<in> f x)"
by (simp add: set_bind_def)

lemma strong: "(x \<in> strong A) = (x \<in> A \<and> x \<noteq> \<bottom>)"
by (simp add: strong_def)

lemma arrow: "(f \<in> arrow A B) = (\<forall>x\<in>A. f\<cdot>x \<in> B)"
by (simp add: arrow_def)

lemma arrowI: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> f\<cdot>x \<in> B\<rbrakk> \<Longrightarrow> f \<in> arrow A B"
by (simp add: arrow_def)

lemma arrowD: "\<lbrakk>f \<in> arrow A B; x \<in> A\<rbrakk> \<Longrightarrow> f\<cdot>x \<in> B"
by (simp add: arrow_def)

lemma lifted: "(x \<in> lifted p) = (p\<cdot>x \<sqsubseteq> TT)"
by (simp add: lifted_def)

end
