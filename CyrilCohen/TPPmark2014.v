Require Import ssreflect ssrfun ssrbool eqtype ssrnat div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TPPMark2014.

Implicit Types a b c : nat.

Local Open Scope nat_scope.

Lemma lemma1 a : (a ^ 2 == 0 %[mod 3]) || (a ^ 2 == 1 %[mod 3]).
Proof. by rewrite -modnXm; case: modn (ltn_mod a 3) => [|[|[|]]]. Qed.

Lemma lemma2 a b c : a ^ 2 + b ^ 2 = 3 * c ^ 2 -> [&& 3 %| a, 3 %| b & 3 %| c].
Proof.
move=> a2b2_eq_3c2; suff /andP [dvd3a dvd3b] : (3 %| a) && (3 %| b).
  rewrite dvd3a dvd3b /= -[_ %| _]andbT -(Euclid_dvdX _ 2) //.
  by rewrite -(@dvdn_pmul2l 3) // -a2b2_eq_3c2 dvdn_add // (@dvdn_exp2r 3 _ 2).
have /(congr1 (modn^~ 3)) := a2b2_eq_3c2.
rewrite -modnDm modnMr -modnXm -[X in _ + X]modnXm /dvdn.
by move: (a %% 3) (b %% 3) (ltn_mod a 3) (ltn_mod b 3) => [|[|[|?]]] [|[|[|]]].
Qed.

Lemma lemma3 a b c : a ^ 2 + b ^ 2 = 3 * c ^ 2 -> [&& a == 0, b == 0 & c == 0].
Proof.
move/eqP; elim: c {-2}c (leqnn c) => [|n ihn] c leqcn in a b *.
  by rewrite leqn0 in leqcn; rewrite (eqP leqcn) addn_eq0 !expn_eq0 andbT.
move=> /(fun p => (p, p)) [/eqP /lemma2 /and3P [/divnK<- /divnK<- /divnK<-]].
rewrite !muln_eq0 !orbF !expnMn mulnA -mulnDl eqn_mul2r; apply: ihn.
by rewrite (leq_trans (leq_div2r _ leqcn)) // -ltnS ltn_Pdiv.
Qed.

End TPPMark2014.
