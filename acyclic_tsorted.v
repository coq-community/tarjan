From mathcomp Require Import all_ssreflect.
Require Import extra acyclic Kosaraju.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AcyclicTSorted.

Variables (V : finType) (g : rel V).
Hypothesis acyclicg : acyclic g.

Variable vs : seq V.
Hypothesis vs_all : forall x, x \in vs.
Hypothesis vs_tsorted : tsorted g (pred_of_simpl predT) vs.

Lemma tsorted_connect_before_nth x y :
  connect g x y ->
  before vs (nth x vs (find (symconnect g x) vs)) y.
Proof. by move: (vs_all x); apply vs_tsorted. Qed.

Lemma nth_find_symconnect s x : x \in s ->
   nth x s (find (symconnect g x) s) = x.
Proof.
move=> xs; suff /eq_find-> : symconnect g x =1 pred1 x by rewrite nth_index.
by move=> y; rewrite acyclic_symconnect_eq// inE eq_sym.
Qed.

Lemma acyclic_connect_before x y : connect g x y -> before vs x y.
Proof. by move=> /tsorted_connect_before_nth; rewrite nth_find_symconnect. Qed.

End AcyclicTSorted.

Section AcyclicTseq.

Variable V : finType.

Lemma tseq_connect_before (g : V -> seq V) x y :
  acyclic (grel g) -> connect (grel g) x y -> before (tseq g) x y.
Proof.
move=> acycg; have [sorted all] := tseq_correct g.
by apply: acyclic_connect_before.
Qed.

Lemma tseq_rel_connect_before (g : rel V) x y :
  acyclic g -> connect g x y ->  before (tseq (rgraph g)) x y.
Proof.
move=> acycg cgxy; have rgK := rgraphK g.
by apply: tseq_connect_before; rewrite (eq_acyclic rgK, eq_connect rgK).
Qed.

End AcyclicTseq.

Section AcyclicKosaraju.

Variable V : finType.

Definition kosaraju_acyclic := sccs_acyclic (@kosaraju V).

Lemma kosaraju_acyclicE : kosaraju_acyclic =1 @acyclic V.
Proof. by move=> g; rewrite [LHS]sccs_acyclicE; case: (kosaraju_correct g). Qed.

End AcyclicKosaraju.
