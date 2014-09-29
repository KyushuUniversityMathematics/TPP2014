Require Import ssreflect eqtype ssrbool ssrnat div.

Let three n P : P 0 -> P 1 -> P 2 -> P (n %% 3).
move => ? ? ?; move: (@ltn_pmod n 3).
set m := n %% 3.
by repeat (case: m; [by [] | ] => m); compute; intuition.
Qed.

Let i a : a*a%%3 = 0 \/ a*a%%3 = 1.
by rewrite -modnMm; eapply (three a); compute; intuition. Qed.

Let nine n P : P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 ->
  P (n %% 9).
move => ? ? ? ? ? ? ? ? ?; move: (@ltn_pmod n 9).
set m := n %% 9.
by repeat (case: m; [by [] | ] => m); compute; intuition.
Qed.

Let ii' a b c:
  (a %% 9)^2 + (b %% 9) ^ 2 = 3 * (c %% 9) ^2 %[mod 9]->
  (a %% 9)%% 3 = 0 /\ (b %% 9)%%3 = 0 /\ (c %% 9) %% 3 = 0.
by eapply (nine a); eapply (nine b); eapply (nine c). Qed.

Let dup a : (a %% 9) %% 3 = a %% 3.
exact: modn_dvdm. Qed.

Let ii a b c:
  a ^ 2 + b ^ 2 = 3 * c ^ 2 ->
  a%% 3 = 0 /\ b%%3 = 0 /\ c %% 3 = 0.
rewrite -(dup a) - (dup b) -(dup c)=>H.
apply: ii'.
rewrite -!mulnn -modnDm !modnMm modnDm mulnA modnMmr mulnAC modnMmr.
rewrite -!mulnn in H.
by rewrite H mulnA.
Qed.

Let ind n (P : nat -> Prop): (forall m, P (m %/3) -> P m) -> P 0 -> P n.
move => H I.
elim: n {-2}n (leqnn n); [ by case | ] => n J m.
rewrite leq_eqVlt.
case/orP; [ | move => K; exact: J].
by move/eqP => ?; subst; apply: H; apply: J; rewrite -ltnS; apply: ltn_Pdiv.
Qed.

Let iii c a b: a ^ 2 + b ^ 2 = 3 * c ^ 2 -> a = 0 /\ b = 0 /\ c = 0.
move => M.
assert (c = 0).
move: a b M.
eapply (ind c); [ | done] => m H a b K.
move: (ii _ _ _ K) => [A [B C]].
move: K.
rewrite (divn_eq m 3) (divn_eq a 3) (divn_eq b 3) => K.
cut (m %/3 = 0) => [ -> | ]; [by rewrite C | ].
apply: (H (a %/ 3) (b %/ 3)).
rewrite A B C !addn0 !expnMn -mulnDl mulnA in K.
move/eqP: K => K.
rewrite eqn_mul2r in K.
simpl in K.
by move/eqP: K.
subst.
split; [move: M; by case: a | split; [ | done] ].
move:M; case: b => // b.
by rewrite -!mulnn mulnSr addnA !muln0 addnS.
Qed.
