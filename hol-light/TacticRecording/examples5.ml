from Library/binomial.ml

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Binomial coefficients.                                                    *)
(* ------------------------------------------------------------------------- *)

let binom = define
  `(!n. binom(n,0) = 1) /\
   (!k. binom(0,SUC(k)) = 0) /\
   (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let binom = theorem_wrap "binom" binom;;

let BINOM_LT = prove
 (`!n k. n < k ==> (binom(n,k) = 0)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC[binom; ARITH; LT_SUC; LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < k ==> n < SUC(k)`; ARITH]);;
let BINOM_LT = theorem_wrap "BINOM_LT" BINOM_LT;;

print_flat_proof true;;

let BINOM_REFL = prove
 (`!n. binom(n,n) = 1`,
  INDUCT_TAC THEN ASM_SIMP_TAC[binom; BINOM_LT; LT; ARITH]);;
let BINOM_REFL = theorem_wrap "BINOM_REFL" BINOM_REFL;;

let BINOM_1 = prove                
 (`!n. binom(n,1) = n`,
  REWRITE_TAC[num_CONV `1`] THEN                                         
  INDUCT_TAC THEN ASM_REWRITE_TAC[binom] THEN ARITH_TAC);;
let BINOM_1 = theorem_wrap "BINOM_1" BINOM_1;;

let BINOM_FACT = prove
 (`!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES; binom] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; FACT; binom] THEN CONV_TAC NUM_RING);;
let BINOM_FACT = theorem_wrap "BINOM_FACT" BINOM_FACT;;

let BINOM_EQ_0 = prove
 (`!n k. binom(n,k) = 0 <=> n < k`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[BINOM_LT]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT; LE_EXISTS] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  DISCH_TAC THEN MP_TAC(SYM(SPECL [`d:num`; `k:num`] BINOM_FACT)) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ; MULT_CLAUSES; FACT_LT]);;
let BINOM_EQ_0 = theorem_wrap "BINOM_EQ_0" BINOM_EQ_0;;

let BINOM_PENULT = prove
 (`!n. binom(SUC n,n) = SUC n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC [binom; ONE; BINOM_REFL] THEN
  SUBGOAL_THEN `binom(n,SUC n)=0` SUBST1_TAC THENL
   [REWRITE_TAC [BINOM_EQ_0; LT]; REWRITE_TAC [ADD; ADD_0; ADD_SUC; SUC_INJ]]);;
let BINOM_PENULT = theorem_wrap "BINOM_PENULT" BINOM_PENULT;;

(* ------------------------------------------------------------------------- *)
(* More potentially useful lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

let BINOM_TOP_STEP = prove
 (`!n k. ((n + 1) - k) * binom(n + 1,k) = (n + 1) * binom(n,k)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n < k:num` THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
     (ARITH_RULE `n < k ==> n + 1 = k \/ n + 1 < k`)) THEN
    ASM_SIMP_TAC[BINOM_LT; SUB_REFL; MULT_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_LT; LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ADD_SUB; ADD_SUB2] THEN
  MP_TAC(SPECL [`d + 1`; `k:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`d:num`; `k:num`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; FACT; ADD_AC] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t FACT_LT)) [`d:num`; `k:num`] THEN
  REWRITE_TAC[LT_NZ] THEN CONV_TAC NUM_RING);;
let BINOM_TOP_STEP = theorem_wrap "BINOM_TOP_STEP" BINOM_TOP_STEP;;
