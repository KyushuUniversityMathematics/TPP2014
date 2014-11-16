let lem0 = ARITH_RULE`~(3 = 0)`;;
let lem1 = MATCH_MP MOD_EXP_MOD lem0;;
let lem2 = prove
 (`(a MOD 3 = 0 ==> a EXP 2 MOD 3 = 0) /\
   (a MOD 3 = 1 ==> a EXP 2 MOD 3 = 1) /\
   (a MOD 3 = 2 ==> a EXP 2 MOD 3 = 1)`,
  REPEAT CONJ_TAC THEN
  ONCE_REWRITE_TAC[GSYM lem1] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;
let lem3 = ARITH_RULE`a MOD 3 = 0 \/ a MOD 3 = 1 \/ a MOD 3 = 2`;;

let prop1 = MESON[lem2; lem3]`!a. a EXP 2 MOD 3 = 0 \/ a EXP 2 MOD 3 = 1`;;

let lem4 = MESON[lem2; lem3; NOT_SUC; ONE]`!a. a MOD 3 = 0 <=> a EXP 2 MOD 3 = 0`;;
let lem5 = prove
 (`!n m. ~(n = 0) ==> (m MOD n = 0 <=> m = m DIV n * n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MP_TAC(SPEC_ALL DIVISION) THEN ASM_ARITH_TAC);;

g `!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> a MOD 3 = 0 /\ b MOD 3 = 0` ;;
e( ASSUME_TAC lem0 THEN REPEAT GEN_TAC THEN DISCH_TAC );;
e( SUBGOAL_TAC"" `(a EXP 2 MOD 3 + b EXP 2 MOD 3) MOD 3 = 0` [ASM_MESON_TAC[MATCH_MP(MOD_ADD_MOD)lem0; MATCH_MP(MOD_MULT)lem0]] );;
(*
e( SUBGOAL_TAC"" `(a EXP 2 MOD 3 + b EXP 2 MOD 3) MOD 3 = 0` [ASM_PV9_TAC[MOD_MULT; MOD_ADD_MOD]] );;
*)
e( ASSUME_TAC (CONJ (SPEC`a:num`prop1) (SPEC`b:num`prop1)) );;
e( ASSUME_TAC (ARITH_RULE`~((1 + 1) MOD 3 = 0 \/ (0 + 1) MOD 3 = 0 \/ (1 + 0) MOD 3 = 0)`) );;
e( ASM_MESON_TAC[lem4] );;
let prop2_1 = top_thm () ;;

g `!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> c MOD 3 = 0` ;;
e( ASSUME_TAC lem0 THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[lem4] );;
e( MAP_EVERY (fun t -> SUBGOAL_THEN t SUBST_ALL_TAC THENL [ASM_MESON_TAC[prop2_1; lem5]; ALL_TAC]) [`a = a DIV 3 * 3`; `b = b DIV 3 * 3`] );;
e( SUBGOAL_THEN `c EXP 2 = 3 * ((a DIV 3) EXP 2 + (b DIV 3) EXP 2)` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[MOD_MULT]] );;
let prop2_2 = top_thm () ;;

g `!c a b. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> c = 0` ;;
e( ASSUME_TAC lem0 THEN MATCH_MP_TAC num_WF );;
e( REPEAT STRIP_TAC );;
e( MAP_EVERY (fun t -> SUBGOAL_THEN t SUBST_ALL_TAC THENL [ASM_MESON_TAC[prop2_1; prop2_2; lem5]; ALL_TAC]) [`a = a DIV 3 * 3`; `b = b DIV 3 * 3`; `c = c DIV 3 * 3`] );;
e( SUBGOAL_TAC"" `(a DIV 3) EXP 2 + (b DIV 3) EXP 2 = 3 * (c DIV 3) EXP 2` [ASM_ARITH_TAC] );;
e( ASM_CASES_TAC `c DIV 3 = 0` THENL [ASM_ARITH_TAC; ASM_MESON_TAC[ARITH_RULE `~(x = 0) ==> x < x * 3`; MULT_0]]  );;
let lem6 = top_thm () ;;

let lem6 = prove
 (`!c a b. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> c = 0`,
  ASSUME_TAC lem0 THEN MATCH_MP_TAC num_WF THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY
    (fun x -> SUBGOAL_THEN x SUBST_ALL_TAC THENL
              [ASM_MESON_TAC [prop2_1; prop2_2; lem5];
               ALL_TAC])
    [`a = a DIV 3 * 3`; `b = b DIV 3 * 3`; `c = c DIV 3 * 3`] THEN
  SUBGOAL_TAC "" `(a DIV 3) EXP 2 + (b DIV 3) EXP 2 = 3 * (c DIV 3) EXP 2`
    [ASM_ARITH_TAC] THEN
  ASM_CASES_TAC `c DIV 3 = 0` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC [ARITH_RULE `~(x = 0) ==> x < x * 3`; MULT_0]);;

let prop3 = MESON[lem6; NUM_RING `x = 0 <=> x EXP 2 = 0`; ARITH_RULE `x + y = 3 * 0 ==> x = 0 /\ y = 0`] `!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> a = 0 /\ b = 0 /\ c = 0`;;
