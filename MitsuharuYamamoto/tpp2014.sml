load "dividesTheory";

open prim_recTheory arithmeticTheory dividesTheory;

val lemma1 = prove (``!a. a**2 MOD 3 = if (a MOD 3 = 0) then 0 else 1``,
    GEN_TAC
    THEN `a**2 MOD 3 = ((a MOD 3) * (a MOD 3)) MOD 3`
         by RW_TAC arith_ss [MOD_TIMES2]
    THEN `a MOD 3 < 3` by RW_TAC arith_ss []
    THEN `(a MOD 3 = 0) \/ (a MOD 3 = 1) \/ (a MOD 3 = 2)` by RW_TAC arith_ss []
    THEN RW_TAC arith_ss []);

val TPPMark2014Q1 = store_thm ("TPPMark2014Q1",
    ``!a. (a**2 MOD 3 = 0) \/ (a**2 MOD 3 = 1)``,
    RW_TAC arith_ss [lemma1]);

val EXP2_SQR = prove (``!a. a ** 2 = a * a``, RW_TAC arith_ss []);

val MULT3_SQR = prove (``!a. (a * 3)**2 = a**2 * 3 * 3``,
    METIS_TAC [EXP2_SQR, MULT_COMM, MULT_ASSOC]);

val lemma2 = prove (``!c. 3 * (c * 3)**2 = (3 * c**2) * 3 * 3``,
    REWRITE_TAC [MULT3_SQR, MULT_ASSOC]);

val lemma3 = prove (``!a b c. (a * 3)**2 + (b * 3)**2 = (a**2 + b**2) * 3 * 3``,
    REWRITE_TAC [MULT3_SQR, RIGHT_ADD_DISTRIB]);

val TPPMark2014Q2 = store_thm ("TPPMark2014Q2",
    ``!a b c. (a**2 + b**2 = 3 * c**2) ==>
    	      divides 3 a /\ divides 3 b /\ divides 3 c``,
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN `(c**2 * 3) MOD 3 = 0` by RW_TAC arith_ss [MOD_EQ_0]
    THEN POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [MULT_COMM])
    THEN `(a**2 + b**2) MOD 3 = 0` by RW_TAC arith_ss []
    THEN `(a**2 MOD 3 + b**2 MOD 3) MOD 3 = 0` by RW_TAC arith_ss [MOD_PLUS]
    THEN Q.SUBGOAL_THEN `(a MOD 3 = 0) /\ (b MOD 3 = 0)` STRIP_ASSUME_TAC
    THENL [Q.UNDISCH_TAC `(a**2 MOD 3 + b**2 MOD 3) MOD 3 = 0`
           THEN RW_TAC arith_ss [lemma1]
	   ,
	   `(?a'. a = a' * 3) /\ (?b'. b = b' * 3)`
	   	by RW_TAC arith_ss [GSYM MOD_EQ_0_DIVISOR]
	   THEN Q.UNDISCH_TAC `a**2 + b**2 = 3 * c**2`
	   THEN ASM_REWRITE_TAC [lemma3]
	   THEN DISCH_TAC
	   THEN `(a'**2 + b'**2) * 3 = c**2` by RW_TAC arith_ss []
	   THEN `((a'**2 + b'**2) * 3) MOD 3 = 0` by RW_TAC arith_ss [MOD_EQ_0]
	   THEN `c**2 MOD 3 = 0` by METIS_TAC []
	   THEN Q.UNDISCH_TAC `c**2 MOD 3 = 0`
	   THEN RW_TAC arith_ss [lemma1, compute_divides]]);

val TPPMark2014Q3 = store_thm ("TPPMark2014Q3",
    ``!a b c. (a**2 + b**2 = 3 * c**2) ==> (a = 0) /\ (b = 0) /\ (c = 0)``,
    REPEAT GEN_TAC
    THEN completeInduct_on `a + b + c`
    THEN Cases_on `v`
    THENL [DECIDE_TAC
    	   ,
	   POP_ASSUM (ASSUME_TAC o REWRITE_RULE [AND_IMP_INTRO]
	   	      o CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))
	   THEN REPEAT GEN_TAC
	   THEN REPEAT DISCH_TAC
	   THEN `(?a'. a = a' * 3) /\ (?b'. b = b' * 3) /\ (?c'. c = c' * 3)`
	   	by METIS_TAC [TPPMark2014Q2, divides_def]
	   THEN Q.UNDISCH_TAC `a**2 + b**2 = 3 * c**2`
	   THEN ASM_REWRITE_TAC [lemma2, lemma3, MULT_EQ_0, DECIDE ``~(3 = 0)``]
	   THEN DISCH_TAC
	   THEN FIRST_ASSUM MATCH_MP_TAC
	   THEN Q.EXISTS_TAC `a' + b' + c'`
	   THEN DECIDE_TAC]);
