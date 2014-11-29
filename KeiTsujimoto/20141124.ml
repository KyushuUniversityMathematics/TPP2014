(* ========================================================================= *)
(* Alternative proofs.                                                       *)
(* ========================================================================= *)

needs "100/reciprocity.ml";;

(* ------------------------------------------------------------------------- *)
(* (i) by induction.                                                         *)
(* ------------------------------------------------------------------------- *)

let prop1 = (GEN_ALL o CONJUNCT1 o SPEC_ALL o prove)
 (`!a. (a EXP 2 MOD 3 = 0 \/ a EXP 2 MOD 3 = 1) /\
       (SUC a EXP 2 MOD 3 = 0 \/ SUC a EXP 2 MOD 3 = 1) /\
       (SUC (SUC a) EXP 2 MOD 3 = 0 \/ SUC (SUC a) EXP 2 MOD 3 = 1)`,
  INDUCT_TAC THENL
   [ARITH_TAC;
    ASM_MESON_TAC
     [MOD_MULT_ADD;
      NUM_RING `SUC (SUC (SUC a)) EXP 2 = (2 * a + 3) * 3 + a EXP 2`]]);;

(* ------------------------------------------------------------------------- *)
(* (i) by QUADRATIC_RESIDUE_FACT.                                            *)
(* |- !a p.                                                                  *)
(*        prime p /\ ODD p /\ coprime (a,p) /\ a is_quadratic_residue mod p  *)
(*        ==> (a EXP ((p - 1) DIV 2) == FACT (p - 2)) (mod p)                *)
(* ------------------------------------------------------------------------- *)

let prop1 = CONV_RULE
 (NUM_REDUCE_CONV THENC
  DEPTH_CONV (PRIME_CONV ORELSEC COPRIME_CONV ORELSEC CONG_CONV) THENC
  PRESIMP_CONV)
 (SPECL [`2`; `3`] QUADRATIC_RESIDUE_FACT);;

(* ------------------------------------------------------------------------- *)
(* (i) by EXPAND_CASES_CONV.                                                 *)
(* |- (!i. i < n ==> P[i]) <=> P[0] /\ ... /\ P[n-1]                         *)
(* ------------------------------------------------------------------------- *)

let prop1 = GEN_ALL
 (SIMP_RULE [MATCH_MP MOD_EXP_MOD (ARITH_RULE `~(3 = 0)`)]
   (MATCH_MP
     (CONV_RULE NUM_REDUCE_CONV (EXPAND_CASES_CONV `!i. i < 3
                                 ==> i EXP 2 MOD 3 = 0 \/ i EXP 2 MOD 3 = 1`))
     (ARITH_RULE `a MOD 3 < 3`)));;

(* ------------------------------------------------------------------------- *)
(* (i) by Prover9.                                                           *)
(* ------------------------------------------------------------------------- *)

(***
let prop1 = PV9 [MOD_EXP_MOD; ARITH_RULE `(!a. a MOD 3 = 0 \/ a MOD 3 = 1 \/
                 a MOD 3 = 2) /\ 0 EXP 2 MOD 3 = 0 /\ 1 EXP 2 MOD 3 = 1 /\
                 2 EXP 2 MOD 3 = 1 /\ ~(3 = 0)`]
                `a EXP 2 MOD 3 = 0 \/ a EXP 2 MOD 3 = 1`;;
-------- Proof 1 --------

THEOREM PROVED

------ process 5896 exit (max_proofs) ------
CPU time (user): 40.657
val prop1 : thm = |- a EXP 2 MOD 3 = 0 \/ a EXP 2 MOD 3 = 1
 ***)

(* ------------------------------------------------------------------------- *)
(* (i) by 3|(n^2)*(n+1)*(n+2) i.e. 3|n^2 or 3|(n^2+3*(n+1)-1).               *)
(* ------------------------------------------------------------------------- *)

let lem1 = prove
 (`3 divides n EXP 2 * (n + 1) * (n + 2)`,
  SIMP_TAC [EXP_2; GSYM MULT_ASSOC] THEN MATCH_MP_TAC DIVIDES_LMUL THEN
  SPEC_TAC (`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [SIMP_TAC [MULT; DIVIDES_0];
    REWRITE_TAC [NUM_RING `SUC n * (SUC n + 1) * (SUC n + 2)
                 = n * (n + 1) * (n + 2) + 3 * ((n + 1) * (n + 2))`] THEN
    ASM_MESON_TAC [DIVIDES_ADD; DIVIDES_RMUL; DIVIDES_REFL]]);;

let lem2 = ONCE_REWRITE_RULE
 [MATCH_MP PRIME_DIVPROD_EQ (EQT_ELIM (PRIME_CONV `prime 3`))] lem1;;

let prop1 = prove
 (`!a. a EXP 2 MOD 3 = 0 \/ a EXP 2 MOD 3 = 1`,
  GEN_TAC THEN MP_TAC (INST [`a:num`,`n:num`] lem2) THEN
  SIMP_TAC [DIVIDES_MOD; ARITH] THEN STRIP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC [SPEC `a + 1` (GSYM MOD_MULT_ADD)] THEN
    SIMP_TAC [NUM_RING `(a + 1) * 3 + a EXP 2 = (a + 1) * (a + 2) + 1`] THEN
    ONCE_SIMP_TAC [GSYM (MATCH_MP  MOD_ADD_MOD (ARITH_RULE`~(3 = 0)`))]] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* (ii) by mod 9.                                                            *)
(* lem1 : n^2 mod 9=0,1,4,7.                                                 *)
(* lem2 : A,B,C mod 9=0,1,4,7 and A+B=3*C then A,B,C mod 9=0 i.e. 9|A,B,C.   *)
(* lem3 : 9|n^2 then 3|n.                                                    *)
(* ------------------------------------------------------------------------- *)

let prop2 = prove
 (`!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2
     ==> 3 divides a /\ 3 divides b /\ 3 divides c`,
  let M9 th = MATCH_MP th (ARITH_RULE `~(9 = 0)`) in
  let lem1 = SIMP_RULE [M9 MOD_EXP_MOD]
   (MATCH_MP
     (CONV_RULE NUM_REDUCE_CONV
       (EXPAND_CASES_CONV `!i. i < 9 ==> i EXP 2 MOD 9 = 0 \/ i EXP 2 MOD 9 = 1
                                   \/ i EXP 2 MOD 9 = 4 \/ i EXP 2 MOD 9 = 7`))
     (ARITH_RULE `n MOD 9 < 9`)) in
  let G9 th = GSYM (M9 th) in
  let lem2 = prove
   (`!A B C.
       (A MOD 9 = 0 \/ A MOD 9 = 1 \/ A MOD 9 = 4 \/ A MOD 9 = 7) /\
       (B MOD 9 = 0 \/ B MOD 9 = 1 \/ B MOD 9 = 4 \/ B MOD 9 = 7) /\
       (C MOD 9 = 0 \/ C MOD 9 = 1 \/ C MOD 9 = 4 \/ C MOD 9 = 7)
       ==> A + B = 3 * C + 0 * 9
       ==> 9 divides A /\ 9 divides B /\ 9 divides C`,
    end_itlist (THEN)
     [REPEAT GEN_TAC; DISCH_THEN (MP_TAC o (CONV_RULE DNF_CONV));
      STRIP_TAC; DISCH_THEN (MP_TAC o (MATCH_MP MOD_EQ));
      ONCE_REWRITE_TAC [G9 MOD_ADD_MOD; G9 MOD_MULT_MOD2; M9 DIVIDES_MOD];
      ASM_SIMP_TAC []; ARITH_TAC]) in
  let lem3 = MESON
   [ARITH_RULE `9 = 3 * 3`; DIVIDES_LMUL2; PRIME_DIVEXP; PRIME_CONV `prime 3`]
   `!n. 9 divides n EXP 2 ==> 3 divides n` in
  MESON_TAC [SIMP_RULE [lem1; ARITH_RULE `x + 0 * y = x`]
                       (SPECL [`a EXP 2`; `b EXP 2`; `c EXP 2`] lem2); lem3]);;

(* ------------------------------------------------------------------------- *)
(* (iii) by induction.                                                       *)
(* lem1 : a^2+b^2=3*c^2 then !n.3^n|a,b,c.                                   *)
(* lem2 : !n.3^n|x then x=0 using x<3^x.                                     *)
(* DIVIDES_LE : |- !m n. m divides n ==> m <= n \/ n = 0                     *)
(* ------------------------------------------------------------------------- *)

let prop3 = prove
 (`!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> a = 0 /\ b = 0 /\ c = 0`,
  let lem1 = prove
   (`!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2
       ==> (!n. 3 EXP n divides a /\ 3 EXP n divides b /\ 3 EXP n divides c)`,
    let lem = SIMP_RULE [ARITH] (SPECL [`n:num`; `2`] NOT_EXP_0) in
    REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
     [MESON_TAC [DIVIDES_1; EXP];
      end_itlist (THEN)
       [POP_ASSUM
          (REPEAT_TCL CONJUNCTS_THEN (CHOOSE_THEN SUBST_ALL_TAC) o
           REWRITE_RULE [divides]);
        SIMP_TAC [ONCE_REWRITE_RULE [MULT_SYM] EXP];
        REWRITE_TAC [MATCH_MP DIVIDES_LMUL2_EQ lem]; MATCH_MP_TAC prop2;
        POP_ASSUM MP_TAC; MP_TAC lem; CONV_TAC NUM_RING]])
  and lem2 = prove
   (`!x. (!n. 3 EXP n divides x) ==> x = 0`,
    let lem = prove
     (`!x. x < 3 EXP x`,INDUCT_TAC THEN SIMP_TAC [EXP] THEN ASM_ARITH_TAC) in
    GEN_TAC THEN DISCH_THEN (MP_TAC o SPEC `x:num`) THEN
    MESON_TAC [DIVIDES_LE; NOT_LE; lem]) in
  MESON_TAC [lem1; lem2]);;

(* ------------------------------------------------------------------------- *)
(* (iii) by GCD.                                                             *)
(* ------------------------------------------------------------------------- *)

let prop3 = prove
 (`!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> a = 0 /\ b = 0 /\ c = 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0 /\ b = 0` THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC NUM_RING; ALL_TAC] THEN
  FIRST_ASSUM
    (MP_TAC o MATCH_MP GCD_COPRIME_EXISTS o REWRITE_RULE [GSYM GCD_ZERO]) THEN
  STRIP_TAC THEN ABBREV_TAC `g = gcd (a,b)` THEN
  SUBGOAL_TAC "" `~(gcd (g,c) = 0)` [ASM_MESON_TAC [GCD_ZERO]] THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP GCD_COPRIME_EXISTS) THEN STRIP_TAC THEN
  ABBREV_TAC `G = gcd (g,c)` THEN REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(a' * a'') EXP 2 + (b' * a'') EXP 2 = 3 * b'' EXP 2`
    (MP_TAC o MATCH_MP prop2) THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUM_RING;
    ASM_MESON_TAC
      [PRIME_TEST `3`; PRIME_DIVPROD; coprime; ARITH_RULE `~(3 = 1)`]]);;

