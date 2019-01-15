From mathcomp Require Import all_ssreflect.
Require Import extra acyclic Kosaraju.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AcyclicTsorted.

Variable V : finType.

Variable g : rel V.

Variable ts : seq V.

Hypothesis ts_tsorted : tsorted g (pred_of_simpl predT) ts.

Hypothesis ts_all : forall x, x \in ts.

Hypothesis g_acyclic : acyclic g.

Lemma ts_nth x y :
 connect g x y -> before ts (nth x ts (find (symconnect g x) ts)) y.
Proof. by move: (ts_all x); apply ts_tsorted. Qed.

Lemma acyclic_find_in_symconnect s x :
 x \in s -> nth x s (find (symconnect g x) s) = x.
Proof.
elim: s x => //= y s IH x.
rewrite in_cons; move/orP.
case; first by move/eqP =>->; case: ifP => //=; move/negP; case; apply: symconnect0.
case Hx: (x == y); first by move/eqP: Hx =>->; case: ifP => // /negP; case; apply: symconnect0.
move/negP/negP: Hx => Hx Hs; case: ifP; last by move => Hd; apply: IH.
by move=> Hd; move/negP/negP/eqP: Hx; case; move: Hd; apply: acyclic_symconnect.
Qed.

Lemma ts_connect_before x y :
  connect g x y -> before ts x y.
Proof.
move => Hc; move: (ts_nth Hc).
by rewrite acyclic_find_in_symconnect.
Qed.

End AcyclicTsorted.

Section ToposTseq.

Variable V : finType.

Variable g : V -> seq V.

Hypothesis g_acyclic : acyclic (grel g).

Lemma tseq_sorted : tsorted (grel g) (pred_of_simpl predT) (tseq g).
Proof. by apply tseq_correct. Qed.
  
Lemma tseq_all x : x \in tseq g.
Proof. by apply tseq_correct. Qed.

Lemma tseq_connect_before x y :
  connect (grel g) x y -> before (tseq g) x y.
Proof.
apply: ts_connect_before => //.
- exact: tseq_sorted.
- exact: tseq_all.
Qed.

End ToposTseq.

Section ToposTseqRel.

Variable V : finType.

Variable g : rel V.

Hypothesis g_acyclic : acyclic g.

Lemma tseq_rel_connect_before x y :
  connect g x y -> before (tseq (rgraph g)) x y.
Proof.
move => Hc.
apply: tseq_connect_before.
- apply (@eq_acyclic _ g) => //.
  move => x0 y0.
  by rewrite /grel /rgraph /= mem_enum.
- rewrite -(@eq_connect _ g) //.
  move => x0 y0.
  by rewrite /grel /rgraph /= mem_enum.
Qed.

End ToposTseqRel.

Section Kosaraju.

Variable V : finType.

Variable g : rel V.  

Definition kosaraju_acyclic :=
  sccs_acyclic (@kosaraju V) g.

Lemma kosaraju_acyclicP :
  reflect (acyclic g) kosaraju_acyclic.
Proof.
case: (kosaraju_correct g) => Hu Hf Hc.
exact: sccs_acyclicP.
Qed.

End Kosaraju.
