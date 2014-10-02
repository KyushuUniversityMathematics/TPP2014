Require Import Arith Euclid Omega.

Definition is_mod (a b r : nat) :=
  exists q, r < b /\ q * b + r = a.

Theorem a2mod3_cases : forall a, is_mod (a*a) 3 0 \/ is_mod (a*a) 3 1.
Proof.
  intros.
  assert (3 > 0) by auto with arith.
  destruct (modulo _ H a) as [r [q [Hq Hr]]].
  destruct r.
    left.
    exists (q * 3 * q).
    rewrite Hq.
    repeat rewrite <- plus_n_O.
    rewrite mult_assoc.
    now auto.
  destruct r.
    right.
    rewrite Hq.
    exists (2 * q + 3 * q * q).
    repeat rewrite <- (mult_comm 3).
    simpl.
    repeat rewrite <- plus_n_O.
    repeat rewrite mult_plus_distr_l.
    repeat rewrite mult_plus_distr_r.
    omega.
  destruct r.
    right.
    exists (1 + 4 * q + 3 * q * q).
    rewrite Hq.
    repeat rewrite <- (mult_comm 3).
    simpl.
    repeat rewrite <- plus_n_O.
    repeat rewrite mult_plus_distr_l.
    repeat rewrite mult_plus_distr_r.
    omega.
  repeat apply lt_S_n in Hr.
  elim (lt_n_O _ Hr).
Qed.

Definition div3 n := exists q, 3 * q = n.

Lemma div3_square : forall a, div3 (a * a) -> div3 a.
Proof.
  intros.
  assert (3 > 0) by auto with arith.
  destruct (modulo _ H0 a) as [r [q [Hq Hr]]].
  destruct r.
    exists q.
    omega.
  destruct r.
    destruct H as [q' Hq'].
    rewrite Hq in Hq'.
    repeat rewrite mult_plus_distr_l in *.
    repeat rewrite mult_plus_distr_r in *.
    rewrite <- (mult_comm 1) in Hq'.
    rewrite (mult_comm 3) in Hq'.
    simpl in Hq'.
    repeat rewrite <- plus_n_O in Hq'.
    rewrite plus_assoc in Hq'.
    repeat rewrite mult_assoc in Hq'.
    repeat rewrite <- mult_plus_distr_r in Hq'.
    apply plus_minus in Hq'.
    rewrite <- mult_minus_distr_r in Hq'.
    destruct (q' - (q * 3 * q + q + q)).
      discriminate.
    simpl in Hq'.
    inversion Hq'.
  destruct r.
    destruct H as [q' Hq'].
    rewrite Hq in Hq'.
    repeat rewrite mult_plus_distr_l in *.
    repeat rewrite mult_plus_distr_r in *.
    rewrite (mult_assoc 2), (mult_comm 2) in Hq'.
    rewrite <- (mult_assoc q 3 2) in Hq'.
    repeat rewrite (mult_comm 3) in Hq'.
    repeat rewrite mult_assoc in Hq'.
    simpl in Hq'.
    change 4 with (1*3 + 1) in Hq'.
    repeat rewrite plus_assoc in Hq'.
    repeat rewrite <- mult_plus_distr_r in Hq'.
    apply plus_minus in Hq'.
    rewrite <- mult_minus_distr_r in Hq'.
    destruct (q' - (q * 3 * q + q * 2 + q * 2 + 1)).
      discriminate.
    simpl in Hq'.
    inversion Hq'.
  repeat apply lt_S_n in Hr.
  elim (lt_n_O _ Hr).
Qed.
    
Theorem a_b_c_div3 : forall a b c,
  a * a + b * b = 3 * c * c -> div3 a /\ div3 b /\ div3 c.
Proof.
  intros.
  destruct (a2mod3_cases a), (a2mod3_cases b).
  + assert (div3 a).
      destruct H0 as [q [Hr Hq]].
      rewrite <- plus_n_O in Hq.
      apply div3_square.
      exists q.
      now rewrite mult_comm.
    assert (div3 b).
      destruct H1 as [q [Hr Hq]].
      rewrite <- plus_n_O in Hq.
      apply div3_square.
      exists q.
      now rewrite mult_comm.
    assert (div3 c).
      apply div3_square.
      destruct H2 as [qa Ha].
      destruct H3 as [qb Hb].
      rewrite <-Ha, <-Hb in H.
      repeat rewrite mult_assoc in H.
      repeat rewrite <- (mult_comm 3) in H.
      repeat rewrite <- mult_assoc in H.
      rewrite <- mult_plus_distr_l in H.
      assert (3 * (qa * qa) + 3 * (qb * qb) = c * c) by omega.
      rewrite <- mult_plus_distr_l in H2.
      esplit; eauto.
    now auto.
  + destruct H0 as [qa [Hra Hqa]].
    destruct H1 as [qb [Hrb Hqb]].
    rewrite <- Hqa, <- Hqb in H.
    rewrite <- mult_assoc, (mult_comm 3) in H.
    rewrite <- (plus_comm 0) in H.
    simpl in H.
    rewrite plus_assoc in H.
    apply eq_sym in H.
    apply plus_minus in H.
    rewrite <- mult_plus_distr_r, <- mult_minus_distr_r in H.
    destruct (c * c - (qa + qb)).
      discriminate.
    simpl in H.
    inversion H.
  + destruct H0 as [qa [Hra Hqa]].
    destruct H1 as [qb [Hrb Hqb]].
    rewrite <- Hqa, <- Hqb in H.
    rewrite <- mult_assoc, (mult_comm 3) in H.
    rewrite <- (plus_comm 0) in H.
    simpl in H.
    rewrite <- plus_assoc, (plus_comm 1 (qb * 3)), plus_assoc in H.
    apply eq_sym, plus_minus in H.
    rewrite <- mult_plus_distr_r, <- mult_minus_distr_r in H.
    destruct (c * c - (qa + qb)).
      discriminate.
    simpl in H.
    inversion H.
  + destruct H0 as [qa [Hra Hqa]].
    destruct H1 as [qb [Hrb Hqb]].
    rewrite <- Hqa, <- Hqb in H.
    rewrite <- mult_assoc, (mult_comm 3) in H.
    rewrite <- plus_assoc, (plus_comm 1 (qb * 3 + 1)) in H.
    repeat rewrite plus_assoc in H.
    rewrite <- plus_assoc in H.
    apply eq_sym, plus_minus in H.
    rewrite <- mult_plus_distr_r, <- mult_minus_distr_r in H.
    destruct (c * c - (qa + qb)).
      discriminate.
    simpl in H.
    inversion H.
Qed.

Require Import Wf_nat.

Theorem a_b_c_0 : forall a b c,
  a * a + b * b = 3 * c * c -> a = 0 /\ b = 0 /\ c = 0.
Proof.
  intros a b c; revert a b.
  induction c using lt_wf_ind.
  intros a b Habc.
  destruct c.
    destruct a; try discriminate.
    destruct b; try discriminate.
    now auto.
  destruct (a_b_c_div3 _ _ _ Habc) as [[qa Ha] [[qb Hb] [qc Hc]]].
  rewrite <- Ha, <- Hb, <- Hc in Habc |- *.
  assert (qc < S c) by omega.
  destruct (H qc H0 qa qb) as [Hqa [Hqb Hqc]].
    repeat rewrite <- mult_assoc in Habc.
    rewrite (mult_comm qa), (mult_comm qb), (mult_comm qc) in Habc.
    repeat rewrite mult_assoc in Habc.
    simpl (3*3) in Habc.
    repeat rewrite <- mult_assoc in Habc.
    rewrite (mult_assoc 3 qc qc) in Habc.
    omega.
  subst.
  now auto.
Qed.
