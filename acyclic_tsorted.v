From mathcomp Require Import all_ssreflect.
Require Import extra acyclic Kosaraju.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AcyclicTSorted.

Variable V : finType.
Variable g : rel V.

Hypothesis acyclicg : acyclic g.

Variable vs : seq V.

Hypothesis vs_all : forall x, x \in vs.
Hypothesis vs_tsorted : tsorted g (pred_of_simpl predT) vs.

Lemma tsorted_connect_before_nth x y :
  connect g x y ->
  before vs (nth x vs (find (symconnect g x) vs)) y.
Proof. by move: (vs_all x); apply vs_tsorted. Qed.

Lemma in_nth_find_symconnect s x :
  x \in s -> nth x s (find (symconnect g x) s) = x.
Proof.
elim: s x => //= y s IH x.
rewrite inE => /orP[/eqP->|]; first by rewrite ifT // symconnect0.
have [<-|/eqP xneqy]:= x =P y; first by rewrite ifT // symconnect0.
case: ifP => [symcgxy|_] xins /=; last by apply: IH.
by apply/sym_equal/(acyclic_symconnect acyclicg).
Qed.

Lemma acyclic_connect_before x y : connect g x y -> before vs x y.
Proof.
move => cgxy; move: (tsorted_connect_before_nth cgxy).
by rewrite in_nth_find_symconnect.
Qed.

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
move => acycg cgxy.
have grelE : grel (rgraph g) =2 g => [x0 y0|].
   by rewrite /grel /rgraph /= mem_enum.
apply: tseq_connect_before; first by apply: eq_acyclic acycg.
by rewrite (eq_connect grelE).
Qed.

End AcyclicTseq.

Section AcyclicKosaraju.

Variable V : finType.
Variable g : rel V.

Definition kosaraju_acyclic := sccs_acyclic (@kosaraju V) g.

Lemma kosaraju_acyclicP : reflect (acyclic g) kosaraju_acyclic.
Proof.
have [Hu Hf Hc] := kosaraju_correct g.
exact: sccs_acyclicP.
Qed.

End AcyclicKosaraju.
