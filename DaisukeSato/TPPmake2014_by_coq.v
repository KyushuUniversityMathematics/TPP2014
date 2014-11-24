Require Import Arith.
Require Import Omega.

Print nat_rect.

Definition mod3_rect:=
  fun (P:nat -> Type) 
      (f0:P 0) 
      (f1:P 1)
      (f2:P 2)
      (fk:forall k,P k -> P (S (S (S k)))) => 
    fix F (n:nat) :P n:=
       match n as i return (P i) with
         | 0 => f0
         | 1 => f1
         | 2 => f2
         | (S (S (S i))) => fk i (F i)
       end.

Definition mod3_ind:=
  fun (P:nat -> Prop)=> mod3_rect P.

Fixpoint mod3 n:=
  match n with
    | S (S (S k)) => mod3 k
    | _ => n
  end.

Definition pow2 (n:nat):= n*n.

Lemma mod3_lt_3:
  forall n,mod3 n < 3.
Proof.
  induction n using mod3_ind;simpl;omega.
Qed.

Lemma mod3_dec:
  forall n,{mod3 n = 0} + {mod3 n = 1} + {mod3 n = 2}.
Proof.
  intros n.
  induction n using mod3_rect.
  - left;left;reflexivity.
  - left;right;reflexivity.
  - right;reflexivity.
  - simpl.
    exact IHn.
Qed.

Lemma mod3_exists:
  forall m n,mod3 m = n -> exists k,m = 3 * k + n.
Proof.
  intros m.
  induction m using mod3_ind;simpl;
  intros n H;try (rewrite <-H; exists 0;simpl;omega).
  cut (mod3 m = n).
  intros H'.
  apply IHm in H.
  destruct H as [k H].
  exists (S k).
  omega.
  exact H.
Qed.

Lemma mod3_mult3:
  forall m n,mod3 (3 * m + n) = mod3 n.
Proof.
  intros m.
  induction m.
  - intros;reflexivity.
  - intros n.
    replace (3 * S m + n) with (3 + (3 * m + n)).
    change (mod3 (3 + (3 * m + n))) with
      (mod3 (3 * m + n)).
    apply IHm.
    ring.
Qed.

Lemma mod3_eq:
  forall m n,m = n -> mod3 m = mod3 n.
Proof.
  intros m n.
  case (mod3_dec m) as [[Hm|Hm]|Hm];
  case (mod3_dec n) as [[Hn|Hn]|Hn];
  apply mod3_exists in Hm;destruct Hm as [m' Hm];
  apply mod3_exists in Hn;destruct Hn as [n' Hn];
  subst m;subst n ;repeat rewrite mod3_mult3;simpl;omega.
Qed.

Lemma mod3_distr:
  forall m n,mod3 (m + n) = mod3 ((mod3 m)+ (mod3 n)).
Proof.
  intros m n.
  assert (forall r s t u v,
            (r*s + u) + (r*t+v) =
               r*(s+t) + (u+v)) as P.
  intros;ring.

  case (mod3_dec m) as [[Hm |Hm]|Hm];
  case (mod3_dec n) as [[Hn |Hn]|Hn];
  rewrite Hm;rewrite Hn;
  apply mod3_exists in Hm;destruct Hm as [m' Hm];
  apply mod3_exists in Hn;destruct Hn as [n' Hn];
  rewrite Hm;rewrite Hn;rewrite P;apply mod3_mult3. 
Qed.

Lemma square_expand :
  forall n m,pow2 (3 * m + n) = (3 * (3 * m * m + 2*m*n) + n*n).
Proof.
  intros;unfold pow2;ring.
Qed.

Lemma mod3_sq:
  forall a,mod3 (pow2 a) = 0 -> mod3 a = 0.
Proof.
  intros a.
  case (mod3_dec a)  as [[H|H]|H];
  apply mod3_exists in H;destruct H as [t H];
  subst a;
  rewrite square_expand;
  repeat rewrite mod3_mult3;
  simpl;omega.
Qed.    


Lemma square_plus_expand :
  forall n m s t,
    pow2 (3 * m + s) + pow2 (3*n+t) =
    3 * (3 * (m * m + n*n) + 2*(m*s +n*t)) + (s*s + t*t).
Proof.
  intros;unfold pow2;ring.
Qed.

Lemma Quest2_sub:
   forall a b,mod3 (pow2 a + pow2 b) = 0 -> mod3 a = 0/\mod3 b = 0 .
Proof.
  intros a b.
  case (mod3_dec a) as [[Ha|Ha]|Ha];
  case (mod3_dec b) as [[Hb|Hb]|Hb];
  apply mod3_exists in Ha;destruct Ha as [a' Ha];
  apply mod3_exists in Hb;destruct Hb as [b' Hb];
  subst a;subst b;rewrite square_plus_expand;
  repeat rewrite mod3_mult3;
  simpl;omega.
Qed.


  
Theorem Quest2:
  forall a b c,pow2 a + pow2 b = 3 * pow2 c -> mod3 a = 0/\mod3 b = 0 /\ mod3 c=0.
Proof.
  intros a b c H.
  cut (mod3 a =0/\mod3 b = 0).
  intros P.
  destruct P as [Pa Pb].
  split.
  exact Pa.
  split.
  exact Pb.
  apply mod3_exists in Pa;destruct Pa as [a' Pa].
  apply mod3_exists in Pb;destruct Pb as [b' Pb].
  rewrite plus_0_r in Pa.
  rewrite plus_0_r in Pb.
  subst a;subst b.
  replace (pow2 (3 * a') + pow2 (3 * b')) with
  (3 * (3 * (a'*a' + b'*b') + 0)) in H.
  rewrite NPeano.Nat.mul_cancel_l in H.
  symmetry in H.
  apply mod3_eq in H.
  rewrite mod3_mult3 in H.
  simpl in H.
  apply mod3_sq in H.
  exact H.
  omega.
  unfold pow2.
  ring.
  apply Quest2_sub.
  rewrite H.
  replace (3*pow2 c) with (3*pow2 c + 0).
  rewrite mod3_mult3.
  reflexivity.
  ring.
Qed.

Lemma plus_eq_0:
  forall m n:nat,m+n=0 -> m=0/\n=0.
Proof.
  intros ;omega.
Qed.

Lemma sq_eq_0:
  forall m,m*m = 0 -> m=0.
Proof.
  intros m.
  destruct m.
  omega.
  simpl.
  intros H.
  inversion H.
Qed.

Theorem Quest3:
  forall a b c,pow2 a + pow2 b = 3 * pow2 c -> a = 0/\b = 0 /\ c=0.
Proof.
  intros a b c.
  generalize dependent b.
  generalize dependent a.

  apply lt_wf_ind with (n:=c).
  intros n P a b.
  destruct n as [|n].
  simpl.
  intros H.
  apply plus_eq_0 in H.
  destruct H as [Ha Hb].
  apply sq_eq_0 in Ha.
  apply sq_eq_0 in Hb.
  omega.
  remember (S n) as k.
  intros H.
  cut (mod3 a = 0/\mod3 b = 0 /\ mod3 k=0).
  intros Hm.
  destruct Hm as [Ha [Hb Hk]].
  apply mod3_exists in Ha;destruct Ha as [a' Ha].
  apply mod3_exists in Hb;destruct Hb as [b' Hb].
  apply mod3_exists in Hk;destruct Hk as [k' Hk].
  rewrite plus_0_r in Ha.
  rewrite plus_0_r in Hb.
  rewrite plus_0_r in Hk.
  subst a;subst b.
  rewrite Hk.
  cut ((a' = 0 /\ b' = 0 /\ k' = 0)->
       (3 * a' = 0 /\ 3 * b' = 0 /\ 3 * k' = 0)).
  intros T.
  apply T.
  apply P.
  omega.
  rewrite Hk in H.
  replace (pow2 (3 * a') + pow2 (3 * b'))
    with (9 * ( pow2 a' + pow2 b')) in H.
  replace (3 * pow2 (3 * k'))
    with (9 * (3 * ( pow2 k'))) in H.
  apply NPeano.Nat.mul_cancel_l in H.
  exact H.
  omega.
  unfold pow2;ring.
  unfold pow2;ring.
  intros;omega.
  apply Quest2 in H.
  exact H.
Qed.
