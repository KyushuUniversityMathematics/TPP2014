(**
 Written by Sosuke Moriguchi (@chiguri on Twitter)
             Kwansei Gakuin University
**)


(* 全体において、well-founded inductionを使わないことを目標とした *)
Section tpp2014.

Require Import Arith.

(********************************** (1)の準備 **************************************)
Fixpoint mod3 n :=
match n with
| S (S (S m)) => mod3 m
| S (S O) => 2
| S O => 1
| O => 0
end.



(* mod3の動きに基づく帰納法 *)
Lemma mod3_ind : forall P : nat -> Prop,
 P 0 ->
 P 1 ->
 P 2 ->
 (forall n, P n -> P (S (S (S n)))) ->
  forall n, P n.
intros P H0 H1 H2 H.
 fix f 1.
  intro.
   destruct n as [ | [ | [ | n]]].
    apply H0.
    apply H1.
    apply H2.
    apply H; apply f.
Qed.



Lemma tripleadd_mult3 : forall n, n + n + n = n * 3.
intro; rewrite mult_comm; simpl.
 rewrite plus_comm; f_equal.
  f_equal.
   rewrite plus_comm; auto.
Qed.



Lemma mod3_case : forall n, mod3 n = 0 \/ mod3 n = 1 \/ mod3 n = 2.
apply mod3_ind; auto.
Qed.



Lemma mult3_mod3 : forall n, mod3 (n * 3) = 0.
intro n; induction n; auto.
Qed.

Lemma mult3_add_mod3 : forall m n, mod3 (n * 3 + m) = mod3 m.
induction n; auto.
Qed.


Lemma mod3_add_mod3 : forall m n, mod3 (m + n) = mod3 (mod3 m + mod3 n).
intro n; apply mod3_ind with (n:=n); clear n; intros.
 simpl.
  case mod3_case with n; intro.
   rewrite H; auto.
   destruct H as [H | H]; rewrite H; auto.
 simpl (mod3 1).
  revert n; apply mod3_ind; auto.
 revert n; apply mod3_ind; auto.
 simpl; rewrite H; auto.
Qed.





(*  (1): a^2 mod 3 = 0 or 1 *)
Theorem Prob1 : forall a, mod3 (a * a) = 0 \/ mod3 (a * a) = 1.
apply mod3_ind; intros; auto; destruct H.
 left; simpl.
  rewrite plus_comm; simpl.
   rewrite plus_comm; simpl.
    rewrite plus_assoc; rewrite plus_comm; simpl.
     rewrite plus_comm; rewrite plus_assoc.
      rewrite tripleadd_mult3.
       rewrite mult3_add_mod3.
        rewrite mult_comm; simpl.
         repeat (rewrite plus_assoc).
          rewrite tripleadd_mult3.
           rewrite mult3_add_mod3.
            auto.
 right; simpl.
  rewrite plus_comm; simpl.
   rewrite plus_comm; simpl.
    rewrite plus_assoc; rewrite plus_comm; simpl.
     rewrite plus_comm; rewrite plus_assoc.
      rewrite tripleadd_mult3.
       rewrite mult3_add_mod3.
        rewrite mult_comm; simpl.
         repeat (rewrite plus_assoc).
          rewrite tripleadd_mult3.
           rewrite mult3_add_mod3.
            auto.
Qed.

(* 全く同じやり方なのでLtacにすればもっと簡単に終わる *)





(********************************** (2)の準備 **************************************)

Lemma square_mod3_0 : forall x, mod3 (x * x) = 0 -> mod3 x = 0.
intro x; apply mod3_ind with (n := x); intros; auto.
 simpl in H; discriminate.
 simpl in H0.
  rewrite plus_comm in H0; simpl in H0.
   rewrite plus_comm in H0; simpl in H0.
    rewrite plus_assoc in H0; rewrite plus_comm in H0; simpl in H0.
     rewrite plus_comm in H0; rewrite plus_assoc in H0.
      rewrite tripleadd_mult3 in H0.
       rewrite mult3_add_mod3 in H0.
        rewrite mult_comm in H0; simpl in *.
         repeat (rewrite plus_assoc in H0).
          rewrite tripleadd_mult3 in H0.
           rewrite mult3_add_mod3 in H0.
            auto.
Qed.



Lemma mod3_0_mult3 : forall n, mod3 n = 0 -> exists m, n = 3 * m.
intro n; apply mod3_ind with (n := n); intuition.
 exists 0; auto.
 simpl in H; discriminate.
 simpl in H; discriminate.
 destruct H1.
  exists (S x).
   rewrite H; simpl.
    f_equal.
     rewrite (plus_comm _ (S _)); simpl; f_equal.
      rewrite (plus_comm _ (S _)); simpl; f_equal.
       rewrite (plus_comm _ 0); simpl; apply plus_assoc.
Qed.


Lemma mult3_eq : forall m n, 3 * m = 3 * n -> m = n.
 (* もちろん3でなくても0でなければ成り立つ。使わないからこれだけ *)
intros m n; repeat (rewrite (mult_comm 3)); revert n; induction m; intros.
 destruct n.
  auto.
   simpl in H; inversion H.
 destruct n; simpl in H; inversion H.
  f_equal; auto.
Qed.






(*  (2)の一部： a^2 + b^2 = 3c^2ならば 3|a^2 かつ 3|b^2   めんどくさいのでNotationはなし *)
Lemma Prob2_ab : forall a b c, a * a + b * b = 3 * c * c -> mod3 (a * a) = 0 /\ mod3 (b * b) = 0.
intros.
 rewrite <- mult_assoc in H; rewrite (mult_comm 3) in H.
  assert (mod3 (a * a + b * b) = 0).
   rewrite H; apply mult3_mod3.
   rewrite mod3_add_mod3 in H0.
    case Prob1 with a; case Prob1 with b; intros; auto;
     rewrite H1 in H0; rewrite H2 in H0; simpl in H0; discriminate.
Qed.


(*  (2)の一部： a^2 + b^2 = 3c^2ならば 3|c^2 *)
Lemma Prob2_c : forall a b c, a * a + b * b = 3 * c * c -> mod3 (c * c) = 0.
intros.
 destruct (Prob2_ab a b c H).
  apply square_mod3_0 in H0.
   apply square_mod3_0 in H1.
    apply mod3_0_mult3 in H0.
      apply mod3_0_mult3 in H1.
       destruct H0; destruct H1; subst.
        repeat (rewrite <- mult_assoc in H).
         rewrite <- mult_plus_distr_l in H.
          apply mult3_eq in H.
           rewrite <- H.
            repeat (rewrite (mult_comm 3)).
             repeat (rewrite mult_assoc).
              repeat (rewrite <- (mult_comm 3)).
               rewrite <- mult_plus_distr_l.
                rewrite mult_comm.
                 apply mult3_mod3.
Qed.


(*  (2)  *)
Theorem Prob2 : forall a b c, a * a + b * b = 3 * c * c -> mod3 (a * a) = 0 /\ mod3 (b * b) = 0 /\ mod3 (c * c) = 0.
intros.
 destruct Prob2_ab with a b c as [H0 H1]; assert (H2 := Prob2_c _ _ _ H); auto.
Qed.







(********************************** (3)の準備 **************************************)


Fixpoint div3 n :=
match n with
| S (S (S m)) => S (div3 m)
| _ => 0
end.



Lemma div3_mod3 : forall n, n = (div3 n) * 3 + mod3 n.
apply mod3_ind; intros; auto.
 simpl.
  repeat f_equal; auto.
Qed.




(* div3に基づく帰納法の準備：なお、well-founded inductionを使うならば0<nでdiv3 n < nを示せば十分 *)
Fixpoint exp3 n :=
match n with
| O => 1
| S n' => 3 * exp3 n'
end.


(* 3で割って0になるまでの回数：この第二引数で帰納法を行う *)
Inductive div3num : nat -> nat -> Prop :=
| div3_O : div3num 0 0
| div3_n : forall m n, exp3 n <= m -> m < exp3 (S n) -> div3num m (S n).



Lemma exp3_not0 : forall n, exp3 n <> 0.
induction n.
 simpl; intro; inversion H.
 simpl.
  intro H; apply IHn.
   destruct (plus_is_O _ _ H); auto.
Qed.


Lemma exp3_lt : forall n, exp3 n < exp3 (S n).
intro; simpl.
 case_eq (exp3 n); intros.
  elim (exp3_not0 _ H).
  unfold lt.
   simpl.
    rewrite plus_comm; simpl.
     repeat (apply le_n_S).
      rewrite <- plus_assoc; apply le_plus_l.
Qed.



Lemma div3num_ex : forall n, exists m, div3num n m.
induction n.
 exists 0.
  constructor.
 destruct IHn.
  inversion H.
   exists 1.
    constructor; simpl; auto.
   unfold lt in H1.
    apply le_lt_or_eq in H1.
     subst; destruct H1.
      exists (S n0); constructor.
       apply le_trans with n; auto.
       auto.
      exists (S (S n0)).
       constructor.
        rewrite H1; auto.
        rewrite H1; apply exp3_lt.
Qed.





Lemma mult3_div3 : forall n, div3 (3 * n) = n.
apply mod3_ind; intros; auto.
 simpl.
  f_equal.
   rewrite plus_comm; simpl; f_equal.
    rewrite (plus_comm n); simpl; f_equal.
     rewrite (plus_comm n); simpl; rewrite tripleadd_mult3.
      rewrite mult_comm; auto.
Qed.



Lemma exp3_div3_pred : forall n, div3 (exp3 (S n)) = exp3 n.
intro; unfold exp3.
 apply mult3_div3.
Qed.




Lemma div3_le : forall m n, m <= n -> div3 m <= div3 n.
fix f 1; intros.
 destruct m as [ | [ | [ | m ]]]; try (apply le_O_n).
  destruct n.
   elim (le_Sn_O _ H).
   apply le_S_n in H; destruct n.
    elim (le_Sn_O _ H).
    apply le_S_n in H; destruct n.
     elim (le_Sn_O _ H).
     simpl; apply le_n_S.
      apply f.
       apply le_S_n; apply H.
Qed.


Lemma div3_mult3_S : forall m, div3 (m * 3) = div3 (S (m * 3)).
fix f 1.
 intro.
  destruct m.
   reflexivity.
    simpl.
     f_equal.
      apply f.
Qed.


Lemma div3_mult3_SS : forall m, div3 (m * 3) = div3 (S (S (m * 3))).
fix f 1.
 intro.
  destruct m.
   reflexivity.
    simpl.
     f_equal.
      apply f.
Qed.



Lemma div3_exp3_lt : forall m n, m < exp3 (S n) -> div3 m < exp3 n.
induction m; intros.
 case_eq (exp3 n); intros.
  elim (exp3_not0 _ H0).
  unfold lt; apply le_n_S; apply le_O_n.
 rewrite (div3_mod3 m).
  case (mod3_case m); intro.
   rewrite H0.
    rewrite plus_comm; simpl plus; rewrite <- div3_mult3_S.
     rewrite mult_comm; rewrite mult3_div3.
      apply IHm.
       apply lt_trans with (S m); auto.
   destruct H0.
    rewrite H0; rewrite plus_comm; simpl plus; rewrite <- div3_mult3_SS.
     rewrite mult_comm; rewrite mult3_div3.
      apply IHm.
       apply lt_trans with (S m); auto.
    rewrite H0; rewrite plus_comm; simpl.
     rewrite mult_comm; rewrite mult3_div3.
      assert (m < S m).
       auto.
       apply (lt_trans _ _ (exp3 (S n))) in H1; auto.
        apply IHm in H1.
         unfold lt in H1; apply le_lt_or_eq in H1.
          destruct H1; auto.
           unfold lt in H.
            rewrite (div3_mod3 m) in H.
             rewrite plus_comm in H; rewrite H0 in H; simpl plus in H.
              simpl exp3 in H; rewrite <- H1 in H.
               rewrite mult_comm in H; simpl in H.
                rewrite (plus_comm _ 0) in H; apply le_S_n in H.
                 rewrite (plus_comm _ (S _)) in H; simpl in H; apply le_S_n in H.
                  rewrite (plus_comm _ (S _)) in H.
                   rewrite <- plus_assoc in H.
                    simpl in H; apply le_S_n in H.
                     elim (le_Sn_n _ H).
Qed.




Lemma div3num_div3_decrease : forall m n, div3num n (S m) -> div3num (div3 n) m.
intros.
 inversion H.
  destruct m.
   unfold lt in *; simpl in *.
    destruct n as [ | [ | [ | n ]]]; try constructor.
     repeat (apply le_S_n in H3).
      elim (le_Sn_O n H3).
   constructor.
    rewrite <- exp3_div3_pred; apply div3_le; auto.
    apply div3_exp3_lt; auto.
Qed.



(* div3に基づく帰納法：割ったもので証明が作れる *)
Lemma div3_ind : forall P : nat -> Prop,
 P 0 ->
 (forall n, P (div3 n) -> P n) -> forall n, P n.
intros P H0 IH n.
 destruct (div3num_ex n).
  revert n H; induction x; intros.
   inversion H.
    auto.
   apply IH.
    apply div3num_div3_decrease in H.
     auto.
Qed.




(*  (3)の一部：a = 0のみ  *)
Lemma Prob3_a : forall a b c, a * a + b * b = 3 * c * c -> a = 0.
intro a; apply div3_ind with (n:=a); intros.
 auto.
 destruct (Prob2 n b c H0) as [H1 [H2 H3]].
  apply square_mod3_0 in H1;
     apply square_mod3_0 in H2;
     apply square_mod3_0 in H3.
   apply mod3_0_mult3 in H1;
       apply mod3_0_mult3 in H2;
       apply mod3_0_mult3 in H3.
    destruct H1;
        destruct H2;
        destruct H3.
     subst.
      rewrite mult3_div3 in H.
       assert (3 * x = 3 * 0 -> 3 * x = 0).
        auto.
        apply H1.
         f_equal.
          apply H with x0 x1.
           repeat (rewrite <- mult_assoc in H0).
            rewrite <- mult_plus_distr_l in H0.
             apply mult3_eq in H0.
              repeat (rewrite (mult_comm 3) in H0).
               repeat (rewrite mult_assoc in H0).
                repeat (rewrite (mult_comm _ 3) in H0).
                 rewrite <- mult_plus_distr_l in H0.
                  apply mult3_eq in H0.
                   rewrite H0; apply mult_assoc.
Qed.




(*  (3)の一部：b = 0のみ  *)
Lemma Prob3_b : forall a b c, a * a + b * b = 3 * c * c -> b = 0.
intros.
 rewrite (Prob3_a _ _ _ H) in H.
  clear a; revert c H; apply div3_ind with (n:=b); intros.
   auto.
   destruct (Prob2 _ _ _ H0) as [_ [H2 H3]].
    simpl plus in *.
     apply square_mod3_0 in H2;
         apply square_mod3_0 in H3.
      apply mod3_0_mult3 in H2;
          apply mod3_0_mult3 in H3.
       destruct H2; destruct H3.
        subst.
         rewrite mult3_div3 in H.
          repeat (rewrite <- mult_assoc in H0).
           apply mult3_eq in H0.
            repeat (rewrite mult_assoc in H0).
             repeat (rewrite (mult_comm _ 3) in H0).
              repeat (rewrite <- mult_assoc in H0).
               apply mult3_eq in H0.
                rewrite mult_assoc in H0.
                 apply H in H0.
                  rewrite H0; auto.
Qed.


(*  (3) a^2 + b^2 = 3c^2 ならば a = b = c = 0  *)
Theorem Prob3 : forall a b c, a * a + b * b = 3 * c * c -> a = 0 /\ b = 0 /\ c = 0.
intros.
 assert (H0 := Prob3_a _ _ _ H).
  assert (H1 := Prob3_b _ _ _ H).
   subst; split; auto.
    split; auto.
     simpl plus in H.
      destruct c; auto.
       simpl in H; inversion H.
Qed.




End tpp2014.

