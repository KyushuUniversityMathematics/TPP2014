B77;10103;0cRequire Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.Wf_nat.


Lemma plus_red_l : forall a b p, a = b -> p + a = p + b.
auto.
Qed.

Lemma plus_red_r : forall a b p, a = b -> a + p = b + p.
auto.
Qed.

Lemma mult_red_l : forall a b p, a = b -> p * a = p * b.
auto.
Qed.

Lemma mult_red_r : forall a b p, a = b -> a * p = b * p.
auto.
Qed.




Proposition div_n0 : forall n, n / 0 = 0.
Proof.
  auto.
Qed.

Lemma div_0 : forall n, 0 / n = 0.
Proof.
destruct n; auto.
Qed.

Proposition div_S : forall n m, m <> 0 -> (n + m) / m = S (n / m).
Proof.
  intros n m.
  case m.
  now tauto.
  intros m' NeqH.
  unfold div.
  assert (lem : forall x y z, divmod (x + (S z)) y 0 z = divmod (S x) y 0 0).
  {
    intros x y.
    induction z.
    + rewrite plus_comm. now auto.
    +
      transitivity (divmod (S (x + S z)) y 0 (S z)).
      assert(EqS : (x + S (S z)) = S (x + S z)).
      {
        transitivity (S (S z) + x).
        now apply plus_comm.
        transitivity (S (S z + x)).
        now auto.
        rewrite plus_comm.
        now auto.
      }
      rewrite EqS.
      now reflexivity.
      transitivity (divmod (x + S z) y 0 z).
      now auto.
      rewrite IHz.
      now auto.
  }
  rewrite lem.
  simpl.
  assert(lem2 : forall a b c d, fst (divmod a b (S c) d) = S (fst (divmod a b c d))).
  {
    induction a.
    now auto.
    intros b c.
    destruct d.
    +
      simpl.
      apply IHa.
    +
      simpl.
      apply IHa.
  }
  apply lem2.
Qed.

Proposition div_le : forall n m, n < m -> n / m = 0.
Proof.
assert(forall a b c, a < c -> fst (divmod a b 0 c) = 0).
{
  induction a.
  now auto.
  intros b c leac.
  destruct c.
  + 
    apply lt_n_0 in leac.
    destruct leac.
  +
    simpl.
    apply IHa.
    apply lt_S_n.
    auto.
}
intros n m lenm.
unfold div.
destruct m.
now auto.
unfold lt in lenm.
apply le_S_n in lenm.
apply le_lt_or_eq in lenm.
destruct lenm as [lenm | eqnm].
+
  apply H.
  apply lenm.
+
  rewrite eqnm.
  cut (forall a b, fst (divmod a b 0 a) = 0).
  now auto.
  induction a.
  now auto.
  simpl.
  apply IHa.
Qed.

Proposition mod_plus : forall a b, b <> 0 -> modulo (a + b) b = modulo a b.
Proof.
intros a b neb0.
generalize (div_mod (a + b) b neb0); intro divapb.
rewrite (div_S _ _ neb0) in divapb.
rewrite mult_comm in divapb.
simpl in divapb.
rewrite <- plus_assoc in divapb.
rewrite (plus_comm a b) in divapb.
apply plus_reg_l in divapb.
rewrite (div_mod a _ neb0) in divapb at 1.
rewrite mult_comm in divapb.
apply plus_reg_l in divapb.
symmetry.
rewrite (plus_comm a b).
auto.
Qed.

Lemma mult_div_mod : forall a b r, b <> 0 -> r < b -> (a * b + r) / b = a.
Proof.
induction a.
+
  simpl.
  intros b r neb0 lerb.
  apply div_le.
  apply lerb.
+
  intros b r neqb lerb.
  simpl.
  rewrite plus_assoc_reverse. 
  rewrite plus_comm.
  rewrite (div_S _ _ neqb).
  rewrite (IHa _ _ neqb lerb).
  auto.
Qed.

Lemma mult_div : forall a b, b <> 0 -> a * b / b = a.
Proof.
intros a b neb0.
transitivity ((a*b+0) / b).
{
  rewrite plus_comm.
  simpl.
  auto.
}
apply (mult_div_mod _ _ _ neb0).
unfold lt.
destruct b.
elimtype False.
apply neb0.
reflexivity.
apply le_n_S.
apply le_0_n.
Qed.

Lemma mult_div' : forall a b, b <> 0 -> b * a / b = a.
Proof.
intros a b neb.
rewrite mult_comm.
apply mult_div.
auto.
Qed.


Lemma mult_rem_div : forall a b r q, b <> 0 -> (a = q*b + r /\ r < b) -> q = a / b.
Proof.
  intros a b r.
  induction q.
  +
    intros neqb0 [Eqa lerb].
    simpl in Eqa.
    rewrite Eqa.
    rewrite (div_le _ _ lerb).
    auto.
  +
    intros neqb0 [Eqa lerb].
    simpl in Eqa.
    rewrite Eqa.
    rewrite plus_assoc_reverse.
    rewrite plus_comm.
    rewrite (div_S _ _ neqb0).
    rewrite (mult_div_mod _ _ _ neqb0 lerb).
    auto.
Qed.

Lemma mult_rem_mod : forall a b r q, b <> 0 -> (a = q*b + r /\ r < b) -> modulo a b = r.
Proof.
intros a b r q neb0 [Eqa lerb].
assert(Eqq : q = a / b).
{
  apply (mult_rem_div a b r q neb0).
  split; assumption.
}
rewrite Eqq in Eqa.
generalize (div_mod a _ neb0); intro Eqa'.
rewrite mult_comm in Eqa'.
rewrite Eqa' in Eqa at 1.
apply plus_reg_l in Eqa.
apply Eqa.
Qed.

Proposition mod_le : forall a b, a < b -> modulo a b = a.
Proof.
intros a b leab.
destruct b.
now auto.
assert(neb : S b <> 0).
 intro eqb0.
 inversion eqb0.
symmetry.
rewrite (div_mod a _ neb) at 1.
rewrite (div_le _ _ leab).
cut (S b * 0 = 0).
 intros EqH.
 rewrite EqH.
 now auto.
auto.
Qed.

Lemma mod_bound : forall a b, b <> 0 -> modulo a b < b.
Proof.
intros a b neb0.
apply mod_bound_pos.
apply le_0_n.
apply neq_0_lt.
intro eq0b.
apply neb0.
rewrite eq0b.
auto.
Qed.

Lemma mod_exists : forall a b c, b <> 0 -> modulo a b = c -> exists n, a = n * b + c.
Proof.
intros a b c beq Eqc.
generalize (div_mod a _ beq); intro eqa.
rewrite Eqc in eqa.
exists (a / b).
rewrite mult_comm.
apply eqa.
Qed.

Section pow3.
  
  Definition pow2 m := m * m.
  Definition mod3 n := modulo n 3.

  Lemma ne03 : 3 <> 0.
  Proof.
  auto.
  Qed.

  Lemma mod3_le : forall n, mod3 n <= 2.
  Proof.
    intro n.
    unfold mod3.
    apply lt_n_Sm_le.
    apply mod_bound.
    apply ne03.
  Qed.

  Lemma mod3_dest : forall n, mod3 n = 0 \/ mod3 n = 1 \/ mod3 n = 2.
  Proof.
    intro n.
    set (mod3 n) as m.
    assert(lem3 : m <= 2).
     apply mod3_le.
    destruct m.
    now auto.
    destruct m.
    now auto.
    destruct m.
    now auto.
    repeat apply le_S_n in lem3.
    apply le_Sn_0 in lem3.
    destruct lem3.
  Qed.

  Lemma mod3_0 : forall n, mod3 n = 0 -> exists p, n = 3*p.
  Proof.
    intros n modH.
    generalize (mod_exists _ _ _ ne03 modH); intro HH. 
    destruct HH as [p Eqn].
    exists p.
    rewrite Eqn.
    transitivity (p*3).
    now rewrite plus_comm; auto.
    apply mult_comm.
  Qed.

  Lemma mod3_1 : forall n, mod3 n = 1 -> exists p, n = 3*p + 1.
  Proof.
    intros n modH.
    generalize (mod_exists _ _ _ ne03 modH); intro HH. 
    destruct HH as [p Eqn].
    exists p.
    rewrite Eqn.
    rewrite mult_comm.
    auto.
  Qed.

  Lemma mod3_2 : forall n, mod3 n = 2 -> exists p, n = 3*p + 2.
  Proof.
    intros n modH.
    generalize (mod_exists _ _ _ ne03 modH); intro HH. 
    destruct HH as [p Eqn].
    exists p.
    rewrite Eqn.
    rewrite mult_comm.
    auto.
  Qed.

  Lemma To_mod3_0 : forall n, mod3 (3 * n) = 0.
  Proof.
    intro n.
    apply (mult_rem_mod _ _ _ n).
    apply ne03.
    split.
    transitivity (n*3).
    now apply mult_comm.
    rewrite plus_comm.
    auto.
    unfold lt.
    apply le_n_S.
    apply le_0_n.
  Qed.

  Lemma To_mod3_1 : forall n, mod3 (3 * n + 1) = 1.
  Proof.
    intro n.
    apply (mult_rem_mod _ _ _ n).
    apply ne03.
    split.
    rewrite mult_comm.
    auto.
    unfold lt.
    apply le_n_S.
    apply le_n_S.
    apply le_0_n.
  Qed.

  Lemma To_mod3_2 : forall n, mod3 (3 * n + 2) = 2.
  Proof.
    intro n.
    apply (mult_rem_mod _ _ _ n).
    apply ne03.
    split.
    rewrite mult_comm.
    auto.
    unfold lt.
    apply le_n_S.
    apply le_n_S.
    apply le_n_S.
    apply le_0_n.
  Qed.

  Lemma plus_reg_r : forall n m p : nat, n + p = m + p -> n = m.
  Proof.
    intros n m p eq.
    rewrite (plus_comm n p) in eq.
    rewrite (plus_comm m p) in eq.
    apply plus_reg_l in eq.
    auto.
  Qed.
    
  Lemma mult_plus_distr : forall a b c d, (a + b) * (c + d) = a * c + b * c + a * d + b * d.
  Proof.
    intros a b c d.
    transitivity ((a+b) * c + (a+b) * d).
    now apply mult_plus_distr_l.
    transitivity ((a*c + b*c) + ((a+b) * d)).
    {
      apply plus_red_r.
      apply mult_plus_distr_r.
    }
    transitivity ((a*c + b*c) + (a*d + b*d)).
    {
      apply plus_red_l.
      apply mult_plus_distr_r.
    }
    rewrite plus_assoc.
    auto.
  Qed.

  Lemma pow2_distr : forall a b, pow2 (a + b) = pow2 a + 2 * (a*b) + pow2 b.
  Proof.
    intros a b.
    unfold pow2 at 1.
    rewrite mult_plus_distr.
    transitivity (pow2 a + b * a + a * b + pow2 b).
    {
      unfold pow2.
      auto.
    }
    apply plus_red_r.
    rewrite plus_assoc_reverse.
    apply plus_red_l.
    transitivity (a * b + a * b).
    {
      rewrite (mult_comm b a).
      auto.
    }
    simpl.
    apply plus_red_l.
    rewrite plus_comm.
    auto.
  Qed.

  Lemma pow23p0 : forall p, pow2 (3 * p) = 3 * (3 * pow2 p).
  Proof.
    intro p.
    unfold pow2.
    transitivity (3 * (p * (3 * p))).
    now apply mult_assoc_reverse.
    apply mult_red_l.
    transitivity (p * 3 * p).
    now apply mult_assoc.
    transitivity (3 * p * p).
    {
      apply mult_red_r.
      apply mult_comm.
    }
    apply mult_assoc_reverse.
  Qed.

  Lemma pow23p1 : forall p, pow2 (3*p+1) = 3 * (3 * pow2 p + 2 * p) + 1.
  Proof.
    intro p.
    rewrite pow2_distr.
    transitivity (pow2 (3 * p) + (2 * (3* p * 1)) + 1).
    {
      cut (pow2 1 = 1).
      intro relH.
      rewrite relH.
      auto.
      reflexivity.
    }
    apply plus_red_r.
    transitivity (pow2 (3 * p) + 3 * (2 * p)).
    {
      apply plus_red_l.
      rewrite mult_1_r.
      transitivity (2 * 3 * p).
      now apply mult_assoc.
      transitivity (3 * 2 * p).
      {
        apply mult_red_r.
        apply mult_comm.
      }
      apply mult_assoc_reverse.
    }
    rewrite pow23p0.
    symmetry.
    apply mult_plus_distr_l.
  Qed.

  Lemma pow23p2 : forall p, pow2 (3*p+2) = 3 * (3 * pow2 p + 4 * p + 1) + 1.
  Proof.
    intro p.
    rewrite pow2_distr.
    transitivity (pow2 (3 * p) + 2 * (3 * p * 2) + 3 * 1 + 1).
    {
      transitivity (pow2 (3 * p) + (2 * (3 * p * 2) + pow2 2)).
      now apply plus_assoc_reverse.
      transitivity (pow2 (3 * p) + (2 * (3 * p * 2) + (3 * 1 + 1))).
      {
        apply plus_red_l.
        apply plus_red_l.
        reflexivity.
      }
      rewrite (plus_assoc _ _ 1).
      rewrite plus_assoc.
      apply plus_red_r.
      apply plus_assoc.
    }
    apply plus_red_r.
    transitivity (pow2 (3 * p) + 3 * (4 * p) + 3 * 1).
    {
      apply plus_red_r.
      apply plus_red_l.
      transitivity (2 * (3 * 2 * p)).
      {
        apply mult_red_l.
        transitivity (3 * (p * 2)).
        now apply mult_assoc_reverse.
        rewrite (mult_comm p 2).
        apply mult_assoc.
      }
      transitivity (2 * (6 * p)).
      {
        apply mult_red_l.
        apply mult_red_r.
        reflexivity.
      }
      transitivity (2 * 6 * p).
      now apply mult_assoc.
      transitivity (12 * p).
      {
        apply mult_red_r.
        reflexivity.
      }
      transitivity (3 * 4 * p).
      {
        apply mult_red_r.
        reflexivity.
      }
      apply mult_assoc_reverse.
    }
    rewrite pow23p0.
    rewrite <- (mult_plus_distr_l 3).
    rewrite <- (mult_plus_distr_l 3).
    reflexivity.
  Qed.



  Theorem Problem1 : forall n, mod3 (pow2 n) = 0 \/ mod3 (pow2 n) = 1.
  Proof.
    intro n.
    destruct (mod3_dest n) as [case1 | [case2 | case3]].
    +
      left.
      apply mod3_0 in case1.
      destruct case1 as [p eqn].
      rewrite eqn.
      rewrite pow23p0.
      apply To_mod3_0.
    +
      right.
      apply mod3_1 in case2.
      destruct case2 as [p eqn].
      rewrite eqn.
      rewrite pow23p1.
      apply To_mod3_1.
    +
      right.
      apply mod3_2 in case3.
      destruct case3 as [p eqn].
      rewrite eqn.
      rewrite pow23p2.
      apply To_mod3_1.
  Qed.

  Lemma mod3pow20_mod30 : forall a, mod3 (pow2 a) = 0 -> mod3 a = 0.
  Proof.
    intros a modH.
    destruct (mod3_dest a) as [case1 | [case2 | case3]].
    + auto.
    +
      apply mod3_1 in case2.
      destruct case2 as [p eqa].
      rewrite eqa in modH.
      rewrite pow23p1 in modH.
      rewrite To_mod3_1 in modH.
      discriminate.
    +
      apply mod3_2 in case3.
      destruct case3 as [p eqa].
      rewrite eqa in modH.
      rewrite pow23p2 in modH.
      rewrite To_mod3_1 in modH.
      discriminate.
  Qed.


  Theorem Problem2 : forall a b c, pow2 a + pow2 b = 3 * pow2 c -> mod3 a = 0 /\ mod3 b = 0 /\ mod3 c = 0.
  Proof.
    intros a b c eq.
    assert(Lemma1 : mod3 a = 0 /\ mod3 b = 0).
    {
      assert(pow2_lem : mod3 (pow2 a) = 0 /\ mod3 (pow2 b) = 0).
      {
        destruct (Problem1 a) as [eq00 | eq01] ; destruct (Problem1 b) as [eq10 | eq11].
        +
          split; auto.
        +
          apply mod3_0 in eq00.
          destruct eq00 as [a' eqa].
          apply mod3_1 in eq11.
          destruct eq11 as [b' eqb].
          rewrite eqa in eq.
          rewrite eqb in eq.
          rewrite plus_assoc in eq.
          rewrite <- (mult_plus_distr_l 3) in eq.
          assert(P1 : mod3 (3 * pow2 c) = 1).
          {
            rewrite <- eq.
            apply To_mod3_1.
          }
          rewrite To_mod3_0 in P1.
          discriminate P1.
        +
          apply mod3_1 in eq01.
          destruct eq01 as [a' eqa].
          apply mod3_0 in eq10.
          destruct eq10 as [b' eqb].
          rewrite eqa in eq.
          rewrite eqb in eq.
          rewrite plus_assoc_reverse in eq.
          rewrite (plus_comm 1 (3 * b')) in eq.
          rewrite (plus_assoc) in eq.
          rewrite <- (mult_plus_distr_l 3) in eq.
          assert(P1 : mod3 (3 * pow2 c) = 1).
          {
            rewrite <- eq.
            apply To_mod3_1.
          }
          rewrite To_mod3_0 in P1.
          discriminate P1.
        +
          apply mod3_1 in eq01.
          destruct eq01 as [a' eqa].
          apply mod3_1 in eq11.
          destruct eq11 as [b' eqb].
          rewrite eqa in eq.
          rewrite eqb in eq.
          assert(P1 : mod3 (3 * pow2 c) = 2).
          {
            rewrite <- eq.
            cut (3 * a' + 1 + (3 * b' + 1) = 3 * (a' + b') + 2).
            {
              intro relH.
              rewrite relH.
              apply To_mod3_2.
            }
            rewrite plus_assoc.
            transitivity (3 * a' + 3 * b' + 1 + 1).
            {
              apply plus_red_r.
              transitivity (3 * a' + (1 + 3 * b')).
              now apply plus_assoc_reverse.
              rewrite (plus_comm 1 (3*b')).
              apply plus_assoc.
            }
            rewrite <- (mult_plus_distr_l 3).
            rewrite plus_assoc_reverse.
            apply plus_red_l.
            reflexivity.
          }
          rewrite To_mod3_0 in P1.
          discriminate.
      }
      destruct pow2_lem as [mpa0 mpb0].
      split; apply mod3pow20_mod30; assumption.
    }
    destruct Lemma1 as [mda0 mdb0].
    assert(mdc0 : mod3 c = 0).
    {
      apply mod3_0 in mda0.
      destruct mda0 as [a' eqa].
      apply mod3_0 in mdb0.
      destruct mdb0 as [b' eqb].
      apply mod3pow20_mod30.
      cut (pow2 c = 3 * (pow2 a' + pow2 b')).
      {
        intro relH.
        rewrite relH.
        apply To_mod3_0.
      }
      cut (3 * pow2 c = 3 * (3 * (pow2 a' + pow2 b'))).
      {
        intro relH.
        transitivity (3 * pow2 c / 3).
        {
          symmetry.
          apply mult_div'.
          intro reH.
          discriminate.
        }
        rewrite relH.
        apply mult_div'.
        intro neq.
        discriminate.
      }
      rewrite <- eq.
      rewrite eqa.
      rewrite eqb.
      rewrite pow23p0.
      rewrite pow23p0.
      rewrite <- mult_plus_distr_l.
      apply mult_red_l.
      symmetry.
      apply mult_plus_distr_l.
    }
    split.
    assumption.
    split.
    assumption.
    assumption.
  Qed.

(*
  Lemma mod3_0_dest : forall n, mod3 n = 0 -> (n = 0 \/ (exists p r, n = 3 ^ p * r /\ mod3 r <> 0)).
  Proof.
*)
  Lemma mod3_0_dest : forall n, n = 0 \/ (exists p r, 3 * n = 3 ^ p * r /\ (mod3 r = 1 \/ mod3 r = 2)).
  Proof.
    apply (well_founded_induction lt_wf (fun n => n = 0 \/ (exists p r, 3 * n = 3^p*r /\ (mod3 r = 1 \/ mod3 r = 2)))).
    intros n IndH.
    destruct n.
    now auto.
    destruct (IndH _ (lt_n_Sn n)) as [Eqy0 | [p [r [Eqn [Eqr1 | Eqr2]]]]].
    {
      rewrite Eqy0.
      right.
      exists 1.
      exists 1.
      split.
      now reflexivity.
      left.
      now reflexivity.
    } {
      right.
      destruct p.
      -
        rewrite pow_0_r in Eqn.
        rewrite mult_1_l in Eqn.
        rewrite <- Eqn in Eqr1.
        rewrite To_mod3_0 in Eqr1.
        discriminate.
      -
        exists 1.
        exists (3^p*r+1).
        split.
        +
          rewrite mult_succ_r.
          rewrite Eqn.
          transitivity(3*(3^p*r)+3).
          {
            apply plus_red_r.
            rewrite mult_assoc.
            apply mult_red_r.
            reflexivity.
          }
          transitivity(3*(3^p*r) + 3*1).
          {
            apply plus_red_l.
            reflexivity.
          }
          rewrite <- mult_plus_distr_l.
          apply mult_red_r.
          reflexivity.
        +
          destruct p.
          *
            right.
            rewrite pow_0_r.
            rewrite mult_1_l.
            apply mod3_1 in Eqr1.
            destruct Eqr1 as [q Eqr].
            rewrite Eqr.
            rewrite plus_assoc_reverse.
            assert(H112 : 1+1=2).
            now reflexivity.
            rewrite H112.
            apply To_mod3_2.
          *
            cut(3^(S p) * r + 1 = 3*(3^p*r)+1).
            {
              intro relH.
              rewrite relH.
              left.
              apply To_mod3_1.
            }
            apply plus_red_r.
            rewrite mult_assoc.
            apply mult_red_r.
            reflexivity.
    } {
      right.
      destruct p.
      -
        rewrite pow_0_r in Eqn.
        rewrite mult_1_l in Eqn.
        rewrite <- Eqn in Eqr2.
        rewrite To_mod3_0 in Eqr2.
        discriminate.
      -
        destruct p.
        {
          assert(Eqnr : n = r).
          {
            cut(3*n = 3*r).
            {
              intro Eq3n.
              transitivity (3*n / 3).
              {
                rewrite (mult_div' _ _ ne03).
                reflexivity.
              }
              rewrite Eq3n.
              apply (mult_div' _ _ ne03).
            }
            rewrite Eqn.
            apply mult_red_r.
            reflexivity.
          }
          rewrite <- Eqnr in Eqr2.
          clear Eqn.
          clear Eqnr.
          clear r.
          assert(mod3nS : mod3 (S n) = 0).
          {
            apply mod3_2 in Eqr2.
            destruct Eqr2 as [p Eqr2].
            rewrite Eqr2.
            cut(S(3*p+2) = 3*(p+1)).
            {
              intro relH.
              rewrite relH.
              apply To_mod3_0.
            }
            transitivity(3*p+2+1).
            {
              rewrite (plus_comm _ 1).
              reflexivity.
            }
            rewrite mult_plus_distr_l.
            rewrite plus_assoc_reverse.
            reflexivity.
          }
          apply mod3_0 in mod3nS.
          destruct mod3nS as [p EqSn].
          assert(lepSn : p < S n).
          {
            rewrite EqSn.
            rewrite <- mult_1_l at 1.
            apply mult_lt_compat_r.
            unfold lt.
            apply le_n_S.
            apply le_n_S.
            now apply le_0_n.
            cut (p <> 0).
            {
              intro nep0.
              destruct p.
              now discriminate.
              unfold lt.
              apply le_n_S.
              apply le_0_n.
            }
            intro Eqp0.
            rewrite Eqp0 in EqSn.
            simpl in EqSn.
            discriminate EqSn.
          }
          rewrite EqSn.
          destruct (IndH _ lepSn) as [Eqp0 | [t [u [Eq3p [Equ1 | Equ2]]]]].
          {
            rewrite Eqp0 in EqSn.
            simpl in EqSn.
            discriminate EqSn.
          } {
            rewrite Eq3p.
            exists (S t).
            exists u.
            split.
            -
              rewrite mult_assoc.
              reflexivity.
            -
              auto.
          } {
            rewrite Eq3p.
            exists (S t).
            exists u.
            split.
            -
              rewrite mult_assoc.
              reflexivity.
            -
              auto.
          }
        }
        {
          exists 1.
          exists (3^(S p) * r + 1).
          split.
          -
            transitivity (3 * (n+1)).
            {
              apply mult_red_l.
              rewrite plus_comm.
              reflexivity.
            }
            rewrite mult_plus_distr_l.
            rewrite Eqn.
            transitivity(3*3^(S p) * r + 3*1).
            {
              apply plus_red_r.
              apply mult_red_r.
              reflexivity.
            }
            transitivity(3*(3^(S p)*r + 1)).
            {
              rewrite mult_plus_distr_l.
              apply plus_red_r.
              apply mult_assoc_reverse.
            }
            apply mult_red_r.
            reflexivity.
          -
            left.
            cut(3^(S p) * r + 1 = 3*(3^p*r)+1).
            {
              intro relH.
              rewrite relH.
              apply To_mod3_1.
            }
            apply plus_red_r.
            rewrite mult_assoc.
            apply mult_red_r.
            reflexivity.
        }
      }
  Qed.

  Lemma IndLemma : forall (P : nat -> Prop), (forall n, P n -> exists n', n = 3 * n' /\ P n') -> forall n, P n -> n = 0.
  Proof.
    intros P IndH n Pn.
    assert(eq3n : exists n', n = 3*n').
    {
      destruct(IndH _ Pn) as [n' [Eqn Pn']].
      exists n'.
      auto.
    }
    destruct eq3n as [n' Eqn].
    destruct (mod3_0_dest n') as [Eqn0 | HH].
    {
      rewrite Eqn0 in Eqn.
      simpl in Eqn.
      auto.
    }
    destruct HH as [p [r [Eq3n' modr]]].
    assert(PInd : forall b t, P(3^t*b) -> P b).
    {
      intro b.
      induction t.
      {
        assert(relH : 3^0*b=b).
        {
          rewrite pow_0_r.
          rewrite mult_1_l.
          auto.
        }
        rewrite relH.
        tauto.
      } {
        intro PH'.
        apply IHt.
        destruct (IndH _ PH') as [t' [Eqt' Pt']].
        cut(t' = 3^t*b).
        {
          intro relH.
          rewrite <- relH.
          auto.
        }
        transitivity(3*t'/3).
        {
          rewrite mult_div'.
          auto.
          apply ne03.
        }
        rewrite <- Eqt'.
        assert(Eq3t : 3^(S t) * b = 3*(3^t * b)).
        {
          rewrite mult_assoc.
          apply mult_red_r.
          reflexivity.
        }
        rewrite Eq3t.
        apply mult_div'.
        apply ne03.
      }
    }
    rewrite Eqn in Pn.
    rewrite Eq3n' in Pn.
    apply PInd in Pn.
    assert(modr0 : mod3 r = 0).
    {
      apply IndH in Pn.
      destruct Pn as [r' [Eqr' Pr']].
      rewrite Eqr'.
      apply To_mod3_0.
    }
    rewrite modr0 in modr.
    destruct modr; discriminate.
  Qed.




  Theorem Problem3 : forall a b c, pow2 a + pow2 b = 3 * pow2 c -> a = 0 /\ b = 0 /\ c = 0.
  Proof.
    set (fun a b c => pow2 a + pow2 b = 3 * pow2 c) as P.
    cut(forall a b c, P a b c -> a=0 /\ b=0 /\ c=0).
    {
      tauto.
    }
    assert(Lem : forall x y z, P x y z -> exists x' y' z', (x = 3 * x' /\ y = 3 * y' /\ z = 3 * z') /\ P x' y' z').
(*    assert(Lemma : forall x y z, pow2 x + pow2 y = 3 * pow2 z -> exists x' y' z', (x = 3 * x' /\ y= 3 * y' /\ z = 3 * z') /\ pow2 x' + pow2 y' = 3 * pow2 z').*)
    {
      unfold P.
      intros x y z eq.
      generalize (Problem2 _ _ _ eq); intro eq'.
      destruct eq' as [mx [my mz]].
      apply mod3_0 in mx.
      apply mod3_0 in my.
      apply mod3_0 in mz.
      destruct mx as [x' eqx].
      destruct my as [y' eqy].
      destruct mz as [z' eqz].
      exists x'.
      exists y'.
      exists z'.
      split.
      {
        split.
        assumption.
        split.
        assumption.
        assumption.
      }
      rewrite eqx in eq.
      rewrite eqy in eq.
      rewrite eqz in eq.
      rewrite pow23p0 in eq.
      rewrite pow23p0 in eq.
      rewrite pow23p0 in eq.
      symmetry.
      transitivity ((9 * (3 * pow2 z')) / 9).
      {
        symmetry.
        apply mult_div'.
        intro dis.
        discriminate.
      }
      transitivity ((3 * (3 * (3 * pow2 z'))) / 9).
      {
        cut (9 * (3 * pow2 z') = 3 * (3 * (3 * pow2 z'))).
        intro relH; rewrite relH; auto.
        transitivity ((3 * 3) * (3 * pow2 z')).
        {
          apply mult_red_r.
          reflexivity.
        }
        apply mult_assoc_reverse.
      }
      rewrite <- eq.
      rewrite <- mult_plus_distr_l.
      rewrite <- mult_plus_distr_l.
      rewrite mult_assoc.
      transitivity ((9 * (pow2 x' + pow2 y')) / 9).
      {
        cut (3*3=9).
        intro relH; rewrite relH; auto.
        reflexivity.
      }
      apply mult_div'.
      intro dis.
      discriminate.
    }
    set (fun a => exists b c, P a b c) as P1.
    set (fun b => exists a c, P a b c) as P2.
    set (fun c => exists a b, P a b c) as P3.
    intros a b c Pabc.
    assert(P1H : P1 a).
    {
      unfold P1.
      exists b.
      exists c.
      now assumption.
    }
    assert(P2H : P2 b).
    {
      unfold P2.
      exists a.
      exists c.
      now assumption.
    }
    assert(P3H : P3 c).
    {
      unfold P3.
      exists a.
      exists b.
      now assumption.
    }
    split; try split.
    +
      generalize P1H.
      apply IndLemma.
      intros x P1x.
      unfold P1 in P1x.
      destruct P1x as [y [z Pxyz]].
      apply Lem in Pxyz.
      destruct Pxyz as [x' [y' [z' [[Eqx [Eqy Eqz]] Pxyz']]]].
      exists x'.
      split.
      now apply Eqx.
      exists y'.
      exists z'.
      now assumption.
    +
      generalize P2H.
      apply IndLemma.
      intros y P2y.
      unfold P2 in P2y.
      destruct P2y as [x [z Pxyz]].
      apply Lem in Pxyz.
      destruct Pxyz as [x' [y' [z' [[Eqx [Eqy Eqz]] Pxyz']]]].
      exists y'.
      split.
      now apply Eqy.
      exists x'.
      exists z'.
      now assumption.
    +
      generalize P3H.
      apply IndLemma.
      intros z P3z.
      unfold P3 in P3z.
      destruct P3z as [x [y Pxyz]].
      apply Lem in Pxyz.
      destruct Pxyz as [x' [y' [z' [[Eqx [Eqy Eqz]] Pxyz']]]].
      exists z'.
      split.
      now apply Eqz.
      exists x'.
      exists y'.
      now assumption.
  Qed.

End pow3.


