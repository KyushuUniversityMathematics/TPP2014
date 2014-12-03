Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma mod3_012 a:
  [|| a == 0 %[mod 3], a == 1 %[mod 3] | a == 2 %[mod 3]].
Proof.
  elim: a => [| a /or3P[||] IH]; first (by apply/or3P; apply Or31);
    by rewrite -(eqn_modDr 1) !addn1 in IH; rewrite IH // !orbT.
Qed.

Proposition tppmark1 a:
  (a^2 == 0 %[mod 3]) || (a^2 == 1 %[mod 3]).
Proof.
    by move: (mod3_012 a) => /or3P[||]/eqP Hmod;
      apply/orP; [left | right | right]; rewrite -modnMm Hmod //=.
Qed.

Lemma sqr_mod a p: prime p -> (p %| (a^2)) -> p %| a.
Proof. by move=> /Euclid_dvdM-> /orP[|]. Qed.

Proposition tppmark2 a b c:
  a^2 + b^2 == 3*c^2 ->
  [&& 3 %| a, 3 %| b & 3 %| c ].
Proof.
  move=> Heq; move: (Heq) => /eqP/(f_equal (modn^~3))/eqP; rewrite modnMr -modnDm.
  move: (tppmark1 a)(tppmark1 b) => /orP[|]Ha /orP[|]Hb; move: (Ha)(Hb) => /eqP-> /eqP-> // _.
  move: Ha Hb; rewrite !eqn_mod_dvd //= !subn0 => Ha Hb.
  have H: prime 3 by []; move: (sqr_mod H Ha) (sqr_mod H Hb) => Ha' Hb'; rewrite Ha' Hb' //=.
  move: Ha' Hb' Heq => /dvdnP[ka->] /dvdnP[kb->].
  rewrite !expnMn -mulnDl -[3^2]mulnn mulnCA eqn_pmul2l // mulnC => /eqP Heq.
  by have Hdvdn: (3 %| c^2); first rewrite -Heq dvdn_mulr //=; apply sqr_mod.
Qed.

Lemma lt_wf_ind n P:
  (forall n0 : nat, (forall m : nat, m < n0 -> P m) -> P n0) -> P n.
Proof.
  elim: n P => [| n IHn] P IH; first by apply IH; move=> m; rewrite (ltn0 m).
  apply IHn; move=> m IHm; apply IH.
  move=> [| k] Hltk; first by apply IH; move=> k; rewrite (ltn0 k).
  by apply IHm; rewrite -ltnS.
Qed.

Proposition tppmark3 a b c:
  a^2 + b^2 == 3*c^2 ->
  [&& a == 0, b == 0 & c == 0].
Proof.
  move=> Heq; suff Heqc0: c == 0 by move: a b Heqc0 Heq => [| a] [| b] /eqP->//.
  move: a b Heq; elim/lt_wf_ind: c => [] [| c] // IH a b Heq.
  move: Heq (Heq) => /tppmark2/and3P[/dvdnP[ka->] /dvdnP[kb->] /dvdnP[kc Hc]].
  rewrite Hc !expnMn -mulnDl !mulnA !eqn_pmul2r // -[3*_*_]mulnA mulnn muln_eq0 => Heq.
  by apply/orP; left; move: Heq; apply/IH; rewrite -(@mulnK kc 3) // -Hc ltn_Pdiv //.
Qed.