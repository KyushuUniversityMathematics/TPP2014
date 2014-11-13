Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import div.

CoInductive sqrmod3_spec (a : nat) : bool -> nat -> Prop :=
 | SqrMod3Zero : sqrmod3_spec a true 0
 | SqrMod3One :  sqrmod3_spec a false 1.

Lemma sqrmod3P a: sqrmod3_spec a (3 %| a) (a^2 %% 3).
Proof.
 have: a %% 3 < 3 by exact: ltn_mod.
 do !rewrite ltnS leq_eqVlt.  rewrite ltn0 orbF -modnXm -mulnn /dvdn.
 by case/orP => [|/orP []] /eqP ->; constructor.
Qed.  

Lemma q1 a: (a^2 %% 3 == 0) || (a^2 %% 3 == 1).
Proof. by case: sqrmod3P. Qed.

Lemma eqn1 a b: (a * 3)^2 + (b * 3)^2 = (a^2 + b^2) * 3 * 3.
Proof. by rewrite -!mulnn ![_ * 3 * (_ * 3)]mulnAC -mulnDl !mulnA -mulnDl. Qed.

Lemma q2 a b c: a^2 + b^2 == 3 * c^2 -> (3 %| a) && (3 %| b) && (3 %| c).
Proof.
 move/eqP => abc.
 have eqmod: (a ^ 2 %% 3 + b ^ 2 %% 3) %% 3 = 0 by rewrite modnDm abc modnMr.
 have [Ha Hb]: 3 %| a /\ 3 %| b by case: sqrmod3P eqmod; case: sqrmod3P.
 rewrite Ha Hb /=.  move/dvdnP: Ha => [a' eqa].  move/dvdnP: Hb => [b' eqb].
 suff: c^2 %% 3 = 0 by case: sqrmod3P.
 move/eqP: abc.  rewrite eqa eqb [3 * _]mulnC eqn1 eqn_mul2r /= => /eqP => <-.
 exact: modnMl.
Qed.

Lemma q3 a b c: a^2 + b^2 == 3 * c^2 -> (a == 0) && (b == 0) && (c == 0).
Proof.
 elim: {a b c}(a + b + c) {-2}a {-2}b {-2}c (leqnn (a + b + c))
         => [a b c | n IHn a b c]; first by rewrite leqn0 !addn_eq0.
 rewrite leq_eqVlt => /orP [abcn1 |]; last by exact: IHn.
 move => abc.  move/q2: (abc) => /andP [] /andP [].
 move => /dvdnP [a' eqa] /dvdnP [b' eqb] /dvdnP [c' eqc].
 move: abc.  rewrite eqa eqb eqc eqn1.
 rewrite -[(_ * _)^2]mulnn [_ * 3 * (_ * 3)]mulnAC !mulnA !eqn_mul2r /=.
 rewrite -mulnA mulnn ![_ * 3]mulnC !muln_eq0 /=.
 apply: IHn.  move/eqP: abcn1.  rewrite eqa eqb eqc -!mulnDl -ltnS.
 case: (posnP (a' + b' + c')) => [-> // | posa'b'c' <-].  exact: ltn_Pmulr.
Qed.

