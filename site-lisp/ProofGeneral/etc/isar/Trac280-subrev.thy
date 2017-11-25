theory "Trac280-subrev" imports Main begin

lemma 
 assumes asm: "P\<^isub>i \<and> Q\<^isub>i"
 shows "Q\<^isub>i \<and> P\<^isub>i"
proof - 
  from asm obtain "P\<^isub>i" and "Q\<^isub>i"
    by blast
  then show "Q\<^isub>i \<and> P\<^isub>i"
    by simp
qed

end

