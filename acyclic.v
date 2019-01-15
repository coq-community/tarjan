From mathcomp Require Import all_ssreflect.
Require Import extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Cycles.

Variable V : finType.
Variable g : rel V.

Lemma self_loop_cycle x : g x x -> cycle g [:: x].
Proof. by move=> H; rewrite /cycle /=; apply/andP. Qed.

Lemma symconnect_path_cycle x y :
  x != y -> symconnect g x y -> exists p, cycle g (x :: p).
Proof.
move=> Hn /andP /= [H_x H_y].
move/connectP: H_x; case => px H_px H_pl.
move/connectP: H_y; case => py H_py H_pl'.
case: py H_py H_pl' Hn => /=; first by move=> H_py Hy; rewrite Hy; move/negP.
move => y' py' /andP [H_in H_py'] H_x.
exists (px ++ belast y' py').
rewrite rcons_cat /= {2}H_x -lastI cat_path -H_pl /=.
by apply/andP; split => //; apply/andP.
Qed.

Lemma cycle_path_symconnect x p :
  cycle g (x :: p) -> x \in g x \/ (exists y, symconnect g x y /\ x != y).
Proof.
rewrite /=; case: p => //=; first by rewrite andbT => Hg; left.
move=> y p Hx; case Hxy: (x == y).
- move/andP: Hx => [Hg Hp].
  by move: Hg; move/eqP: Hxy => Hxy; rewrite Hxy; left.
- move/andP: Hx => [Hg Hp].
  move/eqP/eqP: Hxy => Hxy; right.
  exists y; split => //.
  apply/andP; split; last by apply/connectP; exists (rcons p x) => //; rewrite last_rcons.
  by apply/connectP; exists [:: y]; first by rewrite /=; apply/andP.
Qed.

End Cycles.

Section Acyclic.

Variable V : finType.

Variable g : rel V.

Definition acyclic := forall x p, path g x p -> ~~ cycle g (x :: p).

Hypothesis g_acyclic : acyclic.

Lemma acyclic_no_self_loop x : ~~ g x x.
Proof.
apply/negP; case => Hg; move/g_acyclic: (self_loop_cycle Hg).
by move/negP; case => /=; apply/and3P; split.
Qed.

Lemma acyclic_symconnect x y : symconnect g x y -> x = y.
Proof.
move=> Hd; case Hx: (x == y); first by apply/eqP.
move/negP/negP: Hx => Hx.
have [p Hc] := symconnect_path_cycle Hx Hd.
have Hp: path g x p.
  by move: Hc; rewrite /= rcons_path; move/andP => [Hp Ha].
by move/negP: (g_acyclic Hp); case.
Qed.

End Acyclic.

Section AcyclicRev.

Variable V : finType.

Variable g : rel V.

Hypothesis g_acyclic : acyclic g.

Local Notation grev := [rel x y | g y x].

Lemma acyclic_rev : acyclic grev.
Proof.
move=> x p Hp; apply/negP=> H_c; move: H_c.
move/cycle_path_symconnect; case.
- move => Hxx.
  have Hx: g x x by [].
  move/self_loop_cycle: Hx.
  by apply/negP; apply: g_acyclic.
- move => [y [Hd Hn]].
  have H_rev: g =2 [rel x y | grev y x] by [].
  have Hd': symconnect g x y.
    have Heq := eq_symconnect H_rev.
    rewrite Heq; move/andP: Hd => [Hc1 Hc2]; apply/andP.
    by split; rewrite connect_rev.
  have Hc := symconnect_path_cycle _ Hd'.
  move: (Hc Hn) => [p' Hc'].
  have Hp': path g x p'.
    move: Hc'; rewrite /= rcons_path.
    by move/andP => [Hp' Hgl].
  case: Hc'; apply/negP.
  exact: g_acyclic.
Qed.

End AcyclicRev.

Lemma eq_acyclic (V : finType) (g g' : rel V) :
  g =2 g' -> acyclic g -> acyclic g'.
Proof.
move => Heq Hg x p.
rewrite -(eq_path Heq).
move/Hg => Hc.
apply/negP => Hc'; case/negP: Hc.
move: Hc'; rewrite /cycle.
by rewrite -(eq_path Heq).
Qed.

Section AcyclicSCCS.

Variable V : finType.
Variable sccs : rel V -> seq (seq V).
Variable g : rel V.

Hypothesis uniq_flatten : uniq (flatten (sccs g)).

Hypothesis all_in_flatten : forall v : V, v \in (flatten (sccs g)).

Hypothesis class_symconnected :
  forall c, c \in sccs g ->
  exists x, forall y, (y \in c) = symconnect g x y.

Lemma in_flatten (A : seq (seq V)) s :
  s \in A -> subseq s (flatten A).
Proof.
elim: A => //=.
move => vs c IH H_in.
have H_or: s = vs \/ s \in c.
  move/orP: H_in; case; last by right.
  by move/eqP; left.
case: H_or => H_in'; first by rewrite H_in' prefix_subseq.
have IH' := IH H_in'.
have ->: s = [::] ++ s by [].
by apply cat_subseq; first exact: sub0seq.
Qed.

Lemma non_singleton_neq v v' vs :
  [:: v, v' & vs] \in sccs g -> v != v'.
Proof.
move => H_ks; apply/negP; move/eqP => Hv.
move: Hv H_ks =>->.
move/in_flatten/subseq_uniq => Hf.
move/Hf: uniq_flatten {Hf}.
rewrite /=; move/and3P; case; rewrite inE.
move => [H_n H_u]; move/negP: H_n => H_n.
by case: H_n; apply/orP; left.
Qed.

Lemma non_singleton_cycle v v' vs :
  [:: v, v' & vs] \in sccs g ->
  exists x p, cycle g (x :: p).
Proof.
move => H_ks.
have H_c := class_symconnected H_ks.
rewrite /class_symconnected /= in H_c.
move: H_c => /= [x H_y].
have H_v := H_y v.
have H_v' := H_y v'.
have H_neq := non_singleton_neq H_ks.
have H_in_v: v \in [:: v, v' & vs] by rewrite inE; apply/orP; left.
have H_in_v': v' \in [:: v, v' & vs] by rewrite inE; apply/orP; right; apply/orP; left.
rewrite H_v {H_v} in H_in_v.
rewrite H_v' {H_v'} in H_in_v'.
rewrite /symconnect in H_in_v H_in_v'.
move/andP: H_in_v => [H_cn_v H_cn'_v].
move/connectP: H_cn_v => [pv H_pv] H_vl.
move/connectP: H_cn'_v => [p'v H_p'v] H_vl'.
move/andP: H_in_v' => [H_cn_v' H_cn'_v'].
move/connectP: H_cn_v' => [pv' H_pv'] H_v'l.
move/connectP: H_cn'_v' => [p'v' H_p'v'] H_v'l'.
have H_pvv': connect g v v'.
  apply/connectP.
  exists (p'v ++ pv'); last by rewrite last_cat -H_vl'.
  rewrite cat_path.
  rewrite -H_vl'.
  by apply/andP.
have H_p'vv': connect g v' v.
  apply/connectP.
  exists (p'v' ++ pv); last by rewrite last_cat -H_v'l'.
  rewrite cat_path.
  rewrite -H_v'l'.
  by apply/andP.
have H_di: symconnect g v v'.
  rewrite /symconnect.
  by apply/andP.
have [p H_p] := symconnect_path_cycle H_neq H_di.
by exists v, p.
Qed.

Lemma all_in_sccs v : exists vs, vs \in sccs g /\ v \in vs.
Proof.
have H_all := all_in_flatten v.
move/flattenP: H_all => [vs [H_vs H_in]].
by exists vs.
Qed.

Lemma symconnect_neq_sccs x y :
  symconnect g x y -> x != y ->
  exists v v' vs, [:: v, v' & vs] \in sccs g.
Proof.
move => H_y H_neq.
have [vs [H_vs H_in]] := all_in_sccs x.
have [x' H_c] := class_symconnected H_vs.
have H_eq: x \in vs by [].
have H_c' := H_c x.
rewrite H_c' in H_eq.
have H_di: symconnect g x' y.
  move/andP: H_eq => [H_x'x H_xx'].
  move/andP: H_y => [H_xy H_yx].
  apply/andP; split.
  - by move: H_x'x H_xy; apply: connect_trans.
  - by move: H_yx H_xx'; apply: connect_trans.
rewrite -H_c in H_di.
move {H_y H_c H_c' H_eq}.
case: vs H_in H_di H_vs => // v.
case; last by move => v' vs H_x H_y; exists v, v', vs.
rewrite 2!inE; move/eqP => H_xv; rewrite -H_xv.
move/eqP => H_yx; move/negP: H_neq => H_neq.
by case: H_neq; apply/eqP.
Qed.

Definition class_acyclic (c : seq V) :=
match c with
| [::] => true  
| [:: v] => ~~ g v v
| [:: _, _ & _] => false
end.

Definition sccs_acyclic :=
 all [pred c | class_acyclic c] (sccs g).

Lemma sccs_acyclicP : reflect (acyclic g) sccs_acyclic.
Proof.
apply: (iffP idP).
- move/allP => /=.
  move => H_in_ac v p H_p.
  apply/negP => H_ce.
  apply cycle_path_symconnect in H_ce.
  case: H_ce => H_ce.
  * have [vs [H_vs H_v]] := all_in_sccs v.
    move: H_vs H_v; move/H_in_ac.
    case: vs => //= v'.
    case => //=.
    move/negP.
    rewrite inE => H_in.
    move/eqP => H_eq; move: H_ce.
    by rewrite H_eq.
  * move: H_ce => [y [H_d H_neq]].
    have [v0 [v1 [vs H_ks]]] := symconnect_neq_sccs H_d H_neq.
    by move/H_in_ac: H_ks.
- move => H_gc.
  apply/allP.
  case => //= v; case => //=.
  * move => H_in.
    apply/negP.
    move => H_in'.
    have H_ce: cycle g [:: v] by apply/andP.
    contradict H_ce.
    apply/negP.
    exact: H_gc.
  * move => v' vs; move/non_singleton_cycle.
    move => [x [p H_ce]].
    have H_ce' := H_ce.
    rewrite /= in H_ce'.
    rewrite rcons_path in H_ce'.
    move/andP: H_ce' => [H_p H_l].
    contradict H_ce.
    apply/negP.
    exact: H_gc.
Qed.

End AcyclicSCCS.
