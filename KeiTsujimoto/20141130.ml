(* ========================================================================= *)
(* Proofs of TTPmark2014 by HOL Light with Prover9.                          *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;
Sys.command("wget 'https://github.com/macsyma/HOL-Light/blob/master/pv9.ml'");;
needs "pv9.ml";;

(* ------------------------------------------------------------------------- *)

let M3 th = MATCH_MP th (ARITH_RULE`~(3 = 0)`);;

let prop1 = PV9
 [M3 MOD_EXP_MOD;
  ARITH_RULE
   `~(3 = 0) /\ (a MOD 3 = 0 \/ a MOD 3 = 1 \/ a MOD 3 = 2)
    /\ 0 EXP 2 MOD 3 = 0 /\ 1 EXP 2 MOD 3 = 1 /\ 2 EXP 2 MOD 3 = 1`]
 `!a. a EXP 2 MOD 3 = 0 \/ a EXP 2 MOD 3 = 1`;;

let prop2 = PV9
 [prop1; M3 MOD_ADD_MOD; M3 MOD_MULT; M3 DIVIDES_MOD; PRIME_DIVEXP;
  PRIME_TEST `3`; EXP_2; DIVIDES_MUL2; DIVIDES_ADD; DIVIDES_CMUL2;
  ARITH_RULE
   `~(3 = 0 \/ (1 + 1) MOD 3 = 0 \/ (0 + 1) MOD 3 = 0 \/ (1 + 0) MOD 3 = 0)`]
 `!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2
    ==> 3 divides a /\ 3 divides b /\ 3 divides c`;;

let prop3s = PV9
 [prop2; divides;
  SPEC `\d. !a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2
              ==> d = a + b + c ==> d = 0` num_WF;
  ARITH_RULE
   `((3 * x) EXP 2 + (3 * y) EXP 2 = 3 * (3 * z) EXP 2
    ==> x EXP 2 + y EXP 2 = 3 * z EXP 2)
    /\ (x + y + z = 0 \/ x + y + z < 3 * x + 3 * y + 3 * z)
    /\ (x + y + z = 0 ==> 3 * x + 3 * y + 3 * z = 0)`]
    `!a b c. a EXP 2 + b EXP 2 = 3 * c EXP 2 ==> a + b + c = 0`;;

let prop3 = REWRITE_RULE [ADD_EQ_0] prop3s;;

