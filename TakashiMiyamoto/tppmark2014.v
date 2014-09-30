(* Solution of TPPmark2014.
   Problem : http://coop-math.ism.ac.jp/files/143/tppmark2014-2.pdf
   Environment : Coq 8.4
   By Takashi Miyamoto (tmiya@bu.iij4u.or.jp)
*)

Require Import Arith Ring Omega Wf_nat.

(* induction principle for mod 3 *)
Theorem nat_ind_3 : forall P: nat -> Prop,
  P 0 -> P 1 -> P 2 -> (forall n, P n -> P (S(S(S n)))) ->
  forall n, P n.
Proof.
intros P p0 p1 p2 H.
assert(H': forall n, P n /\ P (S n) /\ P (S(S n))).
* induction n; auto.
  destruct IHn as [pn [psn pssn]]. auto.
* eapply H'.
Qed.

(* define div by 3 *)
Fixpoint div3(n:nat):nat :=
match n with
| S(S(S n')) => S (div3 n')
| _ => 0
end.

Lemma div3_SSS : forall n, div3 (S(S(S n))) = S (div3 n).
Proof.
intro n; unfold div3; simpl; fold div3; auto.
Qed. 

(* define mod 3 *)
Fixpoint mod3(n:nat):nat :=
match n with
| S(S(S n')) => mod3 n'
| _ => n
end.

Lemma mod3_SSS : forall n, mod3 (S(S(S n))) = mod3 n.
Proof.
intro n; unfold mod3; simpl; fold mod3; auto.
Qed. 

Hint Rewrite div3_SSS mod3_SSS : TPP.

Lemma div3_mod3 : forall n, (div3 n)*3 + (mod3 n) = n.
Proof.
induction n using nat_ind_3; auto. 
autorewrite with TPP. omega.
Qed.

(* mod 3 case analysis *)
Lemma mod3_012 : forall n,
  (mod3 n = 0) \/ (mod3 n = 1) \/ (mod3 n = 2).
Proof.
induction n using nat_ind_3; auto.
Qed.

Lemma mod3_3n_0 : forall n, mod3 (3*n) = 0.
Proof.
induction n using nat_ind_3; auto.
replace (3 * S (S (S n))) with (S(S(S(S(S(S(S(S(S (3*n)))))))))) by omega.
repeat rewrite mod3_SSS; auto.
Qed.

Lemma mod3_idem : forall n, mod3 (mod3 n) = mod3 n.
Proof.
intro n; destruct (mod3_012 n) as [H|[H|H]]; rewrite H; auto.
Qed.

Hint Rewrite <- plus_n_O mult_n_O : TPP.
Hint Rewrite mod3_idem mult_0_r mult_0_l mult_1_l mult_1_r : TPP.

Lemma mod3_add_hom: forall p q, mod3 (mod3 p + mod3 q) = mod3 (p + q).
Proof.
induction p using nat_ind_3; induction q using nat_ind_3; 
autorewrite with TPP; auto.
* erewrite IHp; auto.
* erewrite IHp; auto.
* simpl. 
  replace (p + S (S (S q))) with (S(S(S (p+q)))) by omega.
  autorewrite with TPP. auto.
Qed.

Lemma mod3_mul_hom: forall p q, mod3 (mod3 p * mod3 q) = mod3 (p * q).
Proof.
induction p using nat_ind_3; induction q using nat_ind_3; 
autorewrite with TPP; auto.
* replace (2 * S (S (S q))) with (S(S(S(S(S(S(2*q))))))) by omega.
  autorewrite with TPP. auto.
* replace (mod3 (S (S (S p)) * 2)) with (mod3 (p * 2)) by auto. 
  eapply IHp. 
* replace (S (S (S p)) * S (S (S q))) with (3*(3+p+q) + p*q) by ring. 
  erewrite <- (mod3_add_hom (3*(3+p+q)) (p*q)).
  erewrite (mod3_3n_0 (3+p+q)). simpl.
  erewrite mod3_idem. auto.
Qed. 

Lemma mod3_sq_0_0 : forall n, mod3 (n * n) = 0 -> mod3 n = 0.
Proof.
intros n Hsq. destruct (mod3_012 n) as [H|[H|H]]; auto.
* rewrite <- mod3_mul_hom in Hsq. rewrite H in Hsq.
  simpl in Hsq. discriminate Hsq.
* rewrite <- mod3_mul_hom in Hsq. rewrite H in Hsq.
  simpl in Hsq. discriminate Hsq.
Qed.

Lemma mod3_0_q : forall n, mod3 n = 0 -> exists q, n = 3*q.
Proof.
intros n Hn. exists (div3 n). specialize(div3_mod3 n); intro H.
omega.
Qed.

(* Problem (i) *)
Theorem mod3_square_01 : forall a, (mod3 (a*a) = 0) \/ (mod3 (a*a) = 1).
Proof.
intro n. destruct (mod3_012 n) as [H|[H|H]].
* left. erewrite <- (mod3_mul_hom n n). rewrite H. auto.
* right. erewrite <- (mod3_mul_hom n n). rewrite H. auto.
* right. erewrite <- (mod3_mul_hom n n). rewrite H. auto.
Qed.

(* Problem (ii) *)
Theorem all_mod3_0 : forall a b c, a*a + b*b = 3*c*c ->
  (mod3 a = 0) /\ (mod3 b = 0) /\ (mod3 c = 0).
Proof.
intros a b c Heq.
assert ((mod3 a = 0) /\ (mod3 b = 0)) as [Ha0 Hb0].
(*assert(Hab0: (mod3 a = 0) /\ (mod3 b = 0)) as [Ha0 Hb0].*)
* assert(H: mod3 ((mod3 (a*a)) + (mod3 (b*b))) = mod3 (3*c*c))
    by (erewrite mod3_add_hom; erewrite Heq; auto).
  replace (3*c*c) with (3*(c*c)) in H by ring. 
  erewrite mod3_3n_0 in H.
  rewrite <- (mod3_mul_hom a a) in H.
  rewrite <- (mod3_mul_hom b b) in H.
  rewrite <- mod3_add_hom in H.
  autorewrite with TPP in H.
  destruct (mod3_012 a) as [Ha|[Ha|Ha]];
  destruct (mod3_012 b) as [Hb|[Hb|Hb]];
  rewrite Ha in H; rewrite Hb in H; simpl in H; try discriminate H.
  auto.
* assert(Hc0: mod3 c = 0).
  + destruct (mod3_0_q a Ha0) as [qa Hqa].
    destruct (mod3_0_q b Hb0) as [qb Hqb].
    rewrite Hqa in Heq; rewrite Hqb in Heq.
    replace (3*qa*(3*qa)+3*qb*(3*qb)) with (3*(3*(qa*qa+qb*qb))) in Heq by ring.
    replace (3*c*c) with (3*(c*c)) in Heq by ring.
    assert(Heq': 3*(qa * qa + qb * qb) = c*c) by omega.
    assert(mod3 (3 * (qa * qa + qb * qb)) = mod3 (c*c)) 
    by (rewrite Heq'; auto).
    replace (mod3 (3 * (qa * qa + qb * qb))) with 0 in H.
    - symmetry in H; eapply mod3_sq_0_0; auto.
    - symmetry; eapply mod3_3n_0.
  + auto.
Qed.

Lemma shrink_by_3 : forall a b c, a*a + b*b = 3*c*c ->
  (exists a' b' c', a = 3*a' /\ b = 3*b' /\ c = 3*c' /\ 
   a'*a' + b'*b' = 3*c'*c').
Proof.
intros a b c Heq. 
destruct (all_mod3_0 a b c Heq) as [Ha [Hb Hc]].
destruct(mod3_0_q a Ha) as [qa Hqa].
destruct(mod3_0_q b Hb) as [qb Hqb].
destruct(mod3_0_q c Hc) as [qc Hqc].
exists qa; exists qb; exists qc. subst. repeat (split; auto). 
replace (3 * qa * (3 * qa) + 3 * qb * (3 * qb)) with
  (9 * (qa*qa + qb*qb)) in Heq by ring.
replace (3 * (3 * qc) * (3 * qc)) with
  (9 * (3*qc*qc)) in Heq by ring.
omega.
Qed.

Lemma lt_wf_ind' : forall P: nat -> Prop,
  (forall n: nat, (forall m: nat, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
intros P H n.
eapply lt_wf_ind. auto.
Qed.

Theorem infinite_descent :
  forall P : nat -> Prop,
  (forall n : nat, P n -> exists2 m : nat, m < n & P m) ->
  forall n : nat, ~ P n.
Proof.
intros P H.
apply lt_wf_ind'. intros n IH pn.
destruct (H n pn) as [m Hmn pm].
apply (IH m Hmn). auto.
Qed.

Lemma cond_of_a: forall a, ~( ~(a=0) /\ (exists b c:nat, a*a+b*b = 3*c*c)). 
eapply infinite_descent.
intros a [Hn0 Hbc]. destruct Hbc as [b [c Hbc]].
destruct(shrink_by_3 a b c Hbc) as [a' [b' [c' [Ha' [Hb' [Hc' Heq]]]]]].
exists a'.
* omega.
* split. 
  + omega. 
  + exists b'; exists c'; auto.
Qed.
Lemma cond_of_b: forall b, ~( ~(b=0) /\ (exists a c:nat, a*a+b*b = 3*c*c)). 
eapply infinite_descent.
intros b [Hn0 Hac]. destruct Hac as [a [c Hac]].
destruct(shrink_by_3 a b c Hac) as [a' [b' [c' [Ha' [Hb' [Hc' Heq]]]]]].
exists b'.
* omega.
* split. 
  + omega. 
  + exists a'; exists c'; auto.
Qed.
Lemma cond_of_c: forall c, ~( ~(c=0) /\ (exists a b:nat, a*a+b*b = 3*c*c)). 
eapply infinite_descent.
intros c [Hn0 Hab]. destruct Hab as [a [b Hab]].
destruct(shrink_by_3 a b c Hab) as [a' [b' [c' [Ha' [Hb' [Hc' Heq]]]]]].
exists c'.
* omega.
* split. 
  + omega. 
  + exists a'; exists b'; auto.
Qed.

(* Problem (iii) *)
Theorem abc_are_0 : forall a b c:nat, a*a+b*b = 3*c*c -> 
  (a = 0 /\ b = 0 /\ c = 0).
Proof.
intros a b c Heq.
destruct (eq_nat_dec a 0) as [Ha0 | Han0].
* split; auto.
  destruct (eq_nat_dec b 0) as [Hb0 | Hbn0].
  + split; auto.
    destruct (eq_nat_dec c 0) as [Hc0 | Hcn0].
    - auto.
    - elim (cond_of_c c). split; [|exists a; exists b]; auto.
  + elim (cond_of_b b). split; [|exists a; exists c]; auto.
* elim (cond_of_a a). split; [|exists b; exists c]; auto.
Qed.
