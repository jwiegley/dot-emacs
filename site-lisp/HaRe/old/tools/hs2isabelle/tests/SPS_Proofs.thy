theory SPS_Proofs
imports SPS
begin

fixpat runS_strict [simp]: "runS\<cdot>x\<cdot>\<bottom>"

lemma Separation1:
  "ALL is1 is2 sps1 sps2.
    runS$(sps1 `>*< sps2)$(zip$is1$is2) =
    zip$(runS$sps1$is1)$(runS$sps2$is2)"
 apply (rule allI)
 apply (rule_tac x=is1 in L0.ind)
    apply (simp_all)
 apply (rule allI)
 apply (rule_tac x=is2 in L0.casedist)
   apply (simp_all)
 apply (rule allI)
 apply (rule_tac p="feed\<cdot>sps1\<cdot>a" in cprodE)
 apply (rule allI)
 apply (rule_tac p="feed\<cdot>sps2\<cdot>aa" in cprodE)
 apply simp
done

end
