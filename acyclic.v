From mathcomp Require Import all_ssreflect.
Require Import extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Acyclic.

Variable V : finType.
Implicit Types g : rel V.

Lemma cyclexx g x : g x x -> cycle g [:: x].
Proof. by move=> gxx; rewrite /cycle /=; apply/andP. Qed.

Lemma symconnect_path_cycle g x y :
  x != y -> symconnect g x y -> exists p, cycle g (x :: p).
Proof.
move=> xneqy /andP /= [connxy connyx].
move/connectP: connxy; case => px pathpx lastpx.
move/connectP: connyx; case => py pathpy lastpy.
case: py pathpy lastpy => /=.
  by move=> _ xeqy; move: xeqy xneqy=>->; move/negP.
move => y' py' /andP /= [gyy' pathpy'].
exists (px ++ belast y' py').
rewrite rcons_cat /= {2}lastpy -lastI cat_path -lastpx.
by apply/andP; split => //; apply/andP.
Qed.

Lemma cycle_path_symconnect g x p :
  cycle g (x :: p) -> x \in g x \/ (exists y, symconnect g x y /\ x != y).
Proof.
rewrite /=; case: p => //=; first by rewrite andbT => ?; left.
move=> y p /andP; case xeqy: (x == y); move => [gxy pathpx].
  by move/eqP: xeqy gxy -> => gyy; left.
move/eqP/eqP: xeqy => xneqy; right.
exists y; split => //; apply/andP.
split; last by apply/connectP; exists (rcons p x) => //; rewrite last_rcons.
by apply/connectP; exists [:: y]; first by rewrite /=; apply/andP.
Qed.

Definition acyclic g := forall x p, path g x p -> ~~ cycle g (x :: p).

Lemma acyclic_cyclexx g x : acyclic g -> ~~ g x x.
Proof.
move => acycg; apply/negP => gxx; move/acycg: (cyclexx gxx).
by move/negP; case => /=; apply/and3P; split.
Qed.

Lemma acyclic_symconnect g x y :
 acyclic g -> symconnect g x y -> x = y.
Proof.
move => acycg symgxy; case xeqy: (x == y); first by apply/eqP.
move/negP/negP: xeqy => xeqy.
case (symconnect_path_cycle xeqy symgxy) => [p pcycle].
have pathxp: path g x p.
  by move: pcycle; rewrite /= rcons_path; move/andP => [? ?].
by move/negP: (acycg _ _ pathxp).
Qed.

Lemma acyclic_rev g : acyclic g -> acyclic [rel x y | g y x].
Proof.
move=> acycg x p pathxp; apply/negP.
move/cycle_path_symconnect; case => [xgx|[y [symcg xneqy]]].
  have gxx: g x x by [].
  by move/cyclexx: gxx; apply/negP; apply: acycg.
have geq: g =2 [rel x y | [rel x y | g y x] y x] by [].
have symgxy: symconnect g x y.
  rewrite (eq_symconnect geq); move/andP: symcg => [? ?].
  by apply/andP; split; rewrite connect_rev.
move: (symconnect_path_cycle xneqy symgxy) => [p' cyclep'].
have pathp': path g x p'.
  by move: cyclep'; rewrite /= rcons_path; move/andP => [? ?].
by apply/negP: cyclep'; apply: acycg.
Qed.

Lemma eq_acyclic g g' : g =2 g' -> acyclic g -> acyclic g'.
Proof.
move => eqg acycg x p; rewrite -(eq_path eqg).
move/acycg; move/negP => cycg; apply/negP => cycg'.
by case: cycg; rewrite /cycle (eq_path eqg).
Qed.

End Acyclic.

Section AcyclicSCCS.

Variable V : finType.
Variable sccs : rel V -> seq (seq V).
Variable g : rel V.

Hypothesis uniq_flatten : uniq (flatten (sccs g)).
Hypothesis all_in_flatten : forall v : V, v \in (flatten (sccs g)).
Hypothesis class_symconnect :
  forall c, c \in sccs g -> exists x, forall y, (y \in c) = symconnect g x y.

Lemma in_subseq_flatten (A : seq (seq V)) s :
  s \in A -> subseq s (flatten A).
Proof.
elim: A => //= vs c IH invc.
have eqin: s = vs \/ s \in c.
  move/orP: invc; case; last by right.
  by move/eqP; left.
case: eqin => [eqsvs|sc]; first by rewrite eqsvs prefix_subseq.
have ->: s = [::] ++ s by [].
apply cat_subseq; first exact: sub0seq.
exact: IH.
Qed.

Lemma non_singleton_sccs_neq v v' vs :
  [:: v, v' & vs] \in sccs g -> v != v'.
Proof.
move=> vsccs; apply/negP; move/eqP=> veqv'.
move: veqv' vsccs =>->.
move/in_subseq_flatten/subseq_uniq => uniqsccs.
move/uniqsccs: uniq_flatten {uniqsccs}.
rewrite /=; move/and3P; case.
by rewrite inE eqxx.
Qed.

Lemma non_singleton_sccs_cycle v v' vs :
  [:: v, v' & vs] \in sccs g -> exists x p, cycle g (x :: p).
Proof.
move => insccs; move: (class_symconnect insccs).
move => [x symcx].
have vneqv' := non_singleton_sccs_neq insccs.
have inv: v \in [:: v, v' & vs].
  by rewrite inE; apply/orP; left.
have inv': v' \in [:: v, v' & vs].
  by rewrite inE; apply/orP; right; apply/orP; left.
move: (inv) (inv') => {inv inv'}.
rewrite (symcx v) (symcx v') /symconnect.
move/andP => [cgxv cgvx]; move/andP => [cgxv' cgv'x].
move/connectP: cgxv => [pxv pathpxv] lastpxv.
move/connectP: cgvx => [pvx pathpvx] lastpvx.
move/connectP: cgxv' => [pxv' pathpxv'] lastpxv'.
move/connectP: cgv'x => [pv'x pathpv'x] lastpv'x.
have cgvv': connect g v v'.
  apply/connectP.
  exists (pvx ++ pxv'); last by rewrite last_cat -lastpvx.
  by rewrite cat_path -lastpvx pathpvx pathpxv'.
have cgv'v: connect g v' v.
  apply/connectP.
  exists (pv'x ++ pxv); last by rewrite last_cat -lastpv'x.
  by rewrite cat_path -lastpv'x pathpv'x pathpxv.
have symgvv': symconnect g v v' by apply/andP.
have [p pathp] := symconnect_path_cycle vneqv' symgvv'.
by exists v, p.
Qed.

Lemma all_in_sccs v : exists vs, vs \in sccs g /\ v \in vs.
Proof.
by case/flattenP: (all_in_flatten v) => vs ? ?; exists vs.
Qed.

Lemma symconnect_neq_sccs x y :
  symconnect g x y -> x != y ->
  exists v v' vs, [:: v, v' & vs] \in sccs g.
Proof.
move => symcgxy xneqy.
have [vs [vsg xvs]] := all_in_sccs x.
have [x' symcgyvs] := class_symconnect vsg.
move: (xvs); rewrite (symcgyvs x) => symcgx'x.
have symcgx'y: symconnect g x' y.
  move/andP: symcgx'x => [cgx'x cgxx'].
  move/andP: symcgxy => [cgxy cgyx]; apply/andP; split.
    by move: cgx'x cgxy; apply: connect_trans.
  by move: cgyx cgxx'; apply: connect_trans.
move: (symcgx'y) => {symcgx'y}.
rewrite -symcgyvs {symcgyvs symcgx'x x'}.
case: vs vsg xvs => // v.
case; last by move => v' vs vsg xvs yvs; exists v, v', vs.
rewrite 2!inE => vg; move/eqP => xeqv; move/eqP => yeqv.
by move/negP: xneqy; rewrite xeqv yeqv.
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
  move/allP => /= insccs v p pathgvp; apply/negP => cycgvp.
  move/cycle_path_symconnect: cycgvp.
  case; last first.
    move=> [y [symcgvy vneqy]].
    move: (symconnect_neq_sccs symcgvy vneqy).
    move=> [v0 [v1 [vs vssccs]]].
    by move/insccs: vssccs.
  have [vs [vssccs vvs]] := all_in_sccs v.
  move: vssccs vvs; move/insccs.
  case: vs => //= v'; case => //=.
  move/negP; rewrite inE => gvv'.
  by move/eqP=>->.
move=> acycg; apply/allP.
case => //= v; case => //=.
  move=> vinsccs; apply/negP => gvv.
  have cycgv: cycle g [:: v] by apply/andP.
  contradict cycgv; apply/negP.
  exact: acycg.
move => v' vs; move/non_singleton_sccs_cycle.
move => [x [p cycg]]; move: (cycg).
rewrite /= rcons_path.
move/andP => [p' gp'].
contradict cycg; apply/negP.
exact: acycg.
Qed.

End AcyclicSCCS.
