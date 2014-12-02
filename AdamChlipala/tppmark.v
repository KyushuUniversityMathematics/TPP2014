(* TPPmark 2014 solution by Adam Chlipala <http://adam.chlipala.net/>.
 * I decided, somewhat arbitrarily, to only use those modules of Coq's standard
 * library that I'm already familiar with, which turned out to encompass only
 * facts that the tactics [omega] or [ring] could prove.
 * I also specialized modular arithmeic to modulus 3.
 * Finally, I'm going for high automation, especially in the proofs that
 * are specified to the challenge problems and go beyond basic
 * modular-arithmetic facts. *)

Require Import Arith Omega Ring.


(** * Basic theory of mod-3 *)

Fixpoint mod3 (n : nat) : nat :=
  match n with
    | S (S (S n')) => mod3 n'
    | _ => n
  end.

Theorem decompose_mod3 : forall n, exists k r, n = k * 3 + r /\ r < 3.
Proof.
  induction n; simpl; firstorder.
  do 2 exists 0; intuition.
  destruct (eq_nat_dec x0 2); subst.
  exists (S x); exists 0; intuition.
  exists x; exists (S x0); intuition.
Qed.

Theorem mod3_times3 : forall n, mod3 (n * 3) = 0.
Proof.
  induction n; auto.
Qed.

Theorem mod3_times3_plus : forall n m, mod3 (n * 3 + m) = mod3 m.
Proof.
  induction n; auto.
Qed.

Hint Rewrite mod3_times3 mod3_times3_plus.

Ltac exhaustive_nat :=
  repeat match goal with
           | [ H : _ < _ |- _ ] => inversion_clear H
           | [ H : _ <= _ |- _ ] => inversion_clear H
         end; tauto.

Theorem mod3_cases : forall n, mod3 n = 0 \/ mod3 n = 1 \/ mod3 n = 2.
Proof.
  intros.
  pose (decompose_mod3 n); firstorder; subst.
  autorewrite with core; exhaustive_nat.
Qed.

Lemma mod3_plus' : forall nk nr mk mr,
  nr < 3
  -> mr < 3                     
  -> mod3 ((nk * 3 + nr) + (mk * 3 + mr))
     = mod3 (mod3 (nk * 3 + nr) + mod3 (mk * 3 + mr)).
Proof.
  intros; replace ((nk * 3 + nr) + (mk * 3 + mr))
          with (nk * 3 + (mk * 3 + (nr + mr))) by ring.
  autorewrite with core; exhaustive_nat.
Qed.

Theorem mod3_plus : forall n m, mod3 (n + m) = mod3 (mod3 n + mod3 m).
Proof.
  intros.
  pose (decompose_mod3 n).
  pose (decompose_mod3 m).

  firstorder; subst.
  auto using mod3_plus'.
Qed.

Lemma mod3_times' : forall nk nr mk mr,
  nr < 3
  -> mr < 3                     
  -> mod3 ((nk * 3 + nr) * (mk * 3 + mr))
     = mod3 (mod3 (nk * 3 + nr) * mod3 (mk * 3 + mr)).
Proof.
  intros; replace ((nk * 3 + nr) * (mk * 3 + mr))
          with ((3 * nk * mk + nk * mr + mk * nr) * 3 + mr * nr) by ring.
  autorewrite with core; exhaustive_nat.
Qed.

Theorem mod3_times : forall n m, mod3 (n * m) = mod3 (mod3 n * mod3 m).
Proof.
  intros.
  pose (decompose_mod3 n).
  pose (decompose_mod3 m).
  firstorder; subst.
  auto using mod3_times'.
Qed.


(** * Part (i) *)

Ltac mod_cases n :=
  generalize (mod3_cases n); generalize dependent (mod3 n);
  intuition (subst; auto; try discriminate).

Theorem part_i : forall a, mod3 (a * a) = 0 \/ mod3 (a * a) = 1.
Proof.
  intros.
  rewrite mod3_times.
  mod_cases a.
Qed.


(** * Part (iii) *)

Fixpoint pow3 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => pow3 n' * 3
  end.

Lemma pow3_times : forall n m, pow3 n * pow3 m = pow3 (n + m).
Proof.
  induction n; simpl; intuition.
  rewrite <- IHn; ring.
Qed.

Lemma decompose_pow3' : forall n' n, n <= n'
  -> n > 0
  -> exists k r, n = pow3 k * r /\ mod3 r <> O.
Proof.
  induction n'; intros.
  omega.
  pose (decompose_mod3 n); firstorder; subst.
  destruct (eq_nat_dec x0 0); subst.
  
  specialize (IHn' x).
  assert (x <= n') by omega.
  assert (x > 0) by omega.
  firstorder; subst.
  exists (S x0); exists x1; intuition.
  simpl; ring.

  exists 0; exists (x * 3 + x0); simpl; intuition.
  autorewrite with core in *.
  assert (x0 = 0 \/ x0 = 1 \/ x0 = 2) by omega.
  intuition (subst; auto).
Qed.

Lemma decompose_pow3 : forall n, n > 0
  -> exists k r, n = pow3 k * r /\ mod3 r <> O.
Proof.
  eauto using decompose_pow3'.
Qed.

Theorem part_i' : forall a, mod3 a <> 0 -> mod3 (a * a) = 1.
Proof.
  intros.
  generalize (part_i a); intuition.
  rewrite mod3_times in H1.
  mod_cases a.
Qed.

Hint Immediate part_i'.

Lemma decompose_pow3_squared : forall n, n > 0
  -> exists k r, n * n = pow3 (k * 2) * r /\ mod3 r = 1.
Proof.
  intros.
  apply decompose_pow3 in H; firstorder; subst.
  replace ((pow3 x * x0) * (pow3 x * x0))
    with ((pow3 x * pow3 x) * (x0 * x0)) by ring.
  rewrite pow3_times.
  exists x; exists (x0 * x0); intuition.
Qed.

Hint Rewrite mult_0_r plus_O_n plus_0_r.

Lemma pow3_times3_extra : forall n m, pow3 n * m * 3 = pow3 (S n) * m.
Proof.
  simpl; intros; ring.
Qed.

Lemma distr_fancy1 : forall a b c d, a * b + a * c * d = a * (b + c * d).
Proof.
  intros; ring.
Qed.

Lemma distr_fancy2 : forall a b c d, a * b * c + a * d = a * (b * c + d).
Proof.
  intros; ring.
Qed.

Lemma mod3_mod3 : forall n, mod3 (mod3 n) = mod3 n.
Proof.
  intros; mod_cases n.
Qed.

Lemma expose_pow3 : forall n m, 
  n > m
  -> pow3 ((n - m) * 2) = pow3 ((n - 1 - m) * 2) * 3 * 3.
Proof.
  intros; replace ((n - m) * 2) with (S (S ((n - 1 - m) * 2))); simpl; omega.
Qed.

Lemma mod3_times3_extra : forall n m, mod3 (n * 3 * m) = 0.
Proof.
  intros; replace (n * 3 * m) with (n * m * 3) by ring; autorewrite with core; auto.
Qed.

Hint Rewrite pow3_times3_extra minus_diag Min.min_r Min.min_l distr_fancy1 distr_fancy2
     mod3_mod3 expose_pow3 mod3_times3_extra using omega.
Hint Rewrite <- mult_plus_distr_l pow3_times.

Lemma pow3_unique : forall r1 r2 k1 k2,
  pow3 k1 * r1 = pow3 k2 * r2
  -> mod3 r1 <> 0
  -> mod3 r2 <> 0
  -> k1 = k2 /\ r1 = r2.
Proof.
  induction k1; destruct k2; simpl; intros; autorewrite with core in *;
  match goal with
    | [ H : _ |- _ ] => 
      apply (f_equal mod3) in H; autorewrite with core in *; congruence
    | [ IH : forall k : nat, _ |- _ ] =>
      replace (pow3 k1 * 3 * r1) with ((pow3 k1 * r1) * 3) in * by ring;
        replace (pow3 k2 * 3 * r2) with ((pow3 k2 * r2) * 3) in * by ring;
        let H := fresh in assert (H : pow3 k1 * r1 = pow3 k2 * r2) by omega;
          apply IH in H; intuition
    | _ => intuition
  end.
Qed.

Lemma pow3_times_plus : forall k1 r1 k2 r2,
  mod3 r1 = 1
  -> mod3 r2 = 1
  -> pow3 (k1 * 2) * r1 + pow3 (k2 * 2) * r2
     = pow3 (min k1 k2 * 2) * (pow3 ((k1 - min k1 k2) * 2) * r1
                               + pow3 ((k2 - min k1 k2) * 2) * r2).
Proof.
  intros.
  destruct (eq_nat_dec k1 k2); [ subst |
                                 destruct (le_lt_dec k1 k2); [
                                     replace (k2 * 2) with (k1 * 2 + (k2 - k1) * 2) by omega
                                   | replace (k1 * 2) with (k2 * 2 + (k1 - k2) * 2) by omega ] ];
  repeat (autorewrite with core; simpl); ring.
Qed.

Lemma part_iii' : forall k k0 r r0,
  mod3 (pow3 ((k - min k k0) * 2) * r + pow3 ((k0 - min k k0) * 2) * r0) = 0
  -> mod3 r = 1
  -> mod3 r0 = 1
  -> False.
Proof.
  intros.
  rewrite mod3_plus in *.
  destruct (eq_nat_dec k k0); [ subst | destruct (le_lt_dec k k0) ];
  repeat (autorewrite with core in *; simpl in *); try omega;
  repeat match goal with
           | [ H : mod3 _ = _ |- _ ] => rewrite H in *
         end; discriminate.
Qed.

Hint Resolve part_iii'.

Theorem part_iii : forall a b c, a * a + b * b = 3 * c * c
  -> a = 0 /\ b = 0 /\ c = 0.
Proof.
  intros.
  replace (3 * c * c) with ((c * c) * 3) in * by ring.
  destruct a, b, c; autorewrite with core in *; tauto || discriminate || exfalso;
    repeat match goal with
             | [ _ : context[?n * ?n] |- _ ] =>
               let H := fresh in assert (H : n > 0) by omega;
               let k := fresh "k" in let r := fresh "r" in
               let Hr := fresh "Hr" in
               destruct (decompose_pow3_squared n H) as [k [ r [ Hr ] ] ];
                 rewrite Hr in *; clear Hr
           end; try rewrite pow3_times_plus in * by assumption; autorewrite with core in *;
    match goal with
      | [ H : _ = _ |- _ ] => apply pow3_unique in H; intuition
    end; eauto.
Qed.


(** * Part (ii) *)

Theorem part_ii : forall a b c, a * a + b * b = 3 * c * c
  -> mod3 a = 0 /\ mod3 b = 0 /\ mod3 c = 0.
Proof.
  intros.
  apply part_iii in H; intuition (subst; auto).
Qed.
