From mathcomp Require Import all_ssreflect.
Require Import extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Acyclic.

Variable V : finType.
Implicit Types g : rel V.

Lemma cyclexx g x : g x x -> cycle g [:: x].
Proof. by move=> gxx; rewrite /cycle /= gxx. Qed.

Lemma symconnect_path_cycle g x y :
  x != y -> symconnect g x y -> exists p, cycle g (x :: p).
Proof.
move=> /eqP xneqy /andP /= [connxy connyx].
have /connectP[px pathpx lastpx] := connxy.
have /connectP[[//|y' py'] /= /andP[gyy' pathpy'] lastpy'] := connyx.
exists (px ++ belast y' py').
by rewrite rcons_cat /= {2}lastpy' -lastI cat_path -lastpx pathpx /= gyy'.
Qed.

Lemma cycle_path_symconnect g x p :
  cycle g (x :: p) -> ~~ g x x -> exists2 y, symconnect g x y & x != y.
Proof.
case: p => [/andP[gxx _] /negP//|y p /= /andP[gxy pathpx] ngxx].
exists y; last by apply: contra ngxx => /eqP{2}->.
apply/andP; split; apply/connectP; first by exists [::y]; rewrite /= ?gxy.
by exists (rcons p x); rewrite ?last_rcons.
Qed.

Definition acyclic g := forall x p, path g x p -> ~~ cycle g (x :: p).

Lemma acyclic_cyclexx g x : acyclic g -> ~~ g x x.
Proof. by move => /(_ x [::] isT); rewrite /= andbT. Qed.

Lemma acyclic_symconnect g x y : acyclic g -> symconnect g x y -> x = y.
Proof.
have [//|/eqP xneqy acycg symgxy] := x =P y.
have [p cyclexp] := symconnect_path_cycle xneqy symgxy.
suff /acycg/negP : path g x p by [].
by move: cyclexp; rewrite /cycle rcons_path => /andP[].
Qed.

Lemma symconnect_rev g : symconnect g =2 symconnect [rel x y | g y x].
Proof. by move=> x y; rewrite /symconnect connect_rev andbC connect_rev. Qed.

Lemma acyclic_rev g : acyclic g -> acyclic [rel x y | g y x].
Proof.
move=> acycg x p pathxp.
apply/negP => /cycle_path_symconnect[/=|y symcg /eqP[]].
  by apply: acyclic_cyclexx.
by apply: acyclic_symconnect acycg _; rewrite symconnect_rev.
Qed.

Lemma eq_acyclic g g' : g =2 g' -> acyclic g -> acyclic g'.
Proof.
move => eqg acycg x p; rewrite -(eq_path eqg) => /acycg.
by apply: contra; rewrite /cycle (eq_path eqg).
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

Lemma in_subseq_flatten (A : seq (seq V)) s :  s \in A -> subseq s (flatten A).
Proof.
elim: A => //= vs c IH.
by rewrite in_cons => /orP[/eqP->|/IH/subseq_trans->//];
   [exact: prefix_subseq | exact: suffix_subseq].
Qed.

Lemma non_singleton_sccs_neq v v' vs : [:: v, v' & vs] \in sccs g -> v != v'.
Proof.
move=> vsccs; suff : uniq [:: v, v' & vs] by rewrite /= in_cons negb_or; case: eqP.
by apply: subseq_uniq (in_subseq_flatten vsccs) uniq_flatten.
Qed.

Lemma non_singleton_sccs_cycle v v' vs :
  [:: v, v' & vs] \in sccs g -> exists x p, cycle g (x :: p).
Proof.
move => insccs; have [x symcx] := class_symconnect insccs.
have [xeqv|/eqP xneqv] := x =P v.
  exists v; apply: symconnect_path_cycle (non_singleton_sccs_neq insccs) _ => //.
  by rewrite -xeqv -symcx !inE eqxx orbT.
exists x; apply: symconnect_path_cycle xneqv _.
by rewrite -symcx inE eqxx.
Qed.

Lemma all_in_sccs v : exists2 vs, vs \in sccs g & v \in vs.
Proof. by case/flattenP: (all_in_flatten v) => vs ? ?; exists vs. Qed.

Lemma symconnect_neq_sccs x y :
  symconnect g x y -> x != y -> exists v v' vs, [:: v, v' & vs] \in sccs g.
Proof.
move => symcgxy xneqy.
have [vs vsg xvs] := all_in_sccs x.
have [x' symcgyvs] := class_symconnect vsg.
case: vs xvs symcgyvs vsg => // [v [|v' vs]]; last first.
  by move=> *; exists v; exists v'; exists vs.
rewrite inE => /eqP<- _ /class_symconnect[z symcgzyE].
suff : symconnect g z y by rewrite -symcgzyE inE eq_sym (negPf xneqy).
apply: symconnect_trans symcgxy.
by rewrite -symcgzyE inE.
Qed.

Definition class_acyclic (c : seq V) :=
  if c is [:: v & vs] then (vs == [::]) && ~~ g v v else true.

Definition sccs_acyclic := all [pred c | class_acyclic c] (sccs g).

Lemma sccs_acyclicP : reflect (acyclic g) sccs_acyclic.
Proof.
apply: (iffP allP) => [insccs v p pathgvp|acycg [|v [|v1 vs] scssv]] //=.
- apply/negP => /cycle_path_symconnect[| x cymcgvx xneqy].
    have [/= [|v1 [|v2 vs]] /insccs] //= := all_in_sccs v.
    by rewrite inE => ngv1v1 /eqP->.
  by have [v1 [v2 [vs /insccs]]] := symconnect_neq_sccs cymcgvx xneqy.
- by apply: acyclic_cyclexx.
have /non_singleton_sccs_cycle[x [p cyxp]] := scssv.
suff /acycg/negP : path g x p by [].
by move: cyxp; rewrite /= rcons_path => /andP[].
Qed.

End AcyclicSCCS.
