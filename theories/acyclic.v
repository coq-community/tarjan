From Corelib Require Import Setoid.
From mathcomp Require Import all_ssreflect.
Require Import extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[export] Hint Resolve equiv_refl equiv_sym equiv_trans : core.
#[export] Hint Resolve connect0 symconnect0 : core.

Section EquivalenceExtra.
Variable (T : Type).
Implicit Type (R : rel T).

Lemma left_trans_trans R : left_transitive R -> transitive R.
Proof. by move=> Rltrans y x z Rxy Ryz; rewrite (Rltrans _ y). Qed.

Lemma refl_left_trans_sym  R : reflexive R -> left_transitive R -> symmetric R.
Proof. by move=> Rrefl Rltrans x y; apply/idP/idP => /Rltrans<-. Qed.

Lemma equivalence_rel3P R :
  equivalence_rel R <-> [/\ reflexive R, symmetric R & transitive R].
Proof.
rewrite equivalence_relP; split=> [[Rrefl Rltrans]|[Rrefl Rsym Rtrans]].
  by split=> //; [apply: refl_left_trans_sym | apply: left_trans_trans].
by split=> //; apply: left_trans.
Qed.

Lemma eq_equivalence_rel R R' : R =2 R' ->
  equivalence_rel R <-> equivalence_rel R'.
Proof. by move=> eqR; split=> + x y z => /(_ x y z); rewrite !eqR. Qed.

Lemma equiv_relP R : equivalence_rel R -> { e : equiv_rel T | R = e }.
Proof. by move=> /equivalence_rel3P [r s t]; exists (EquivRel R r s t). Qed.

Lemma equivalence_rel_refl R : equivalence_rel R -> reflexive R.
Proof. by move=> /equiv_relP[{}R->]; apply: equiv_refl. Qed.

Lemma equivalence_rel_sym R : equivalence_rel R -> symmetric R.
Proof. by move=> /equiv_relP[{}R->]; apply: equiv_sym. Qed.

Lemma equivalence_rel_trans R : equivalence_rel R -> transitive R.
Proof. by move=> /equiv_relP[{}R->]; apply: equiv_trans. Qed.

Lemma equiv_equivalence_rel (e : equiv_rel T) : equivalence_rel e.
Proof. by apply/equivalence_rel3P; split. Qed.

End EquivalenceExtra.
Coercion equivalence_rel_refl : equivalence_rel >-> reflexive.
Coercion equivalence_rel_sym : equivalence_rel >-> symmetric.
Coercion equivalence_rel_trans : equivalence_rel >-> transitive.

Notation EquivalenceRel R Req := (EquivRel R Req Req Req).

#[export] Hint Resolve equiv_equivalence_rel : core.

Section EquivalencePartitionExtra.

Variables (T : finType) (P : {set {set T}}) (D : {set T}).
Hypothesis D_partition : partition P D.

Lemma partition_neq0 C : C \in P -> C != set0.
Proof. by apply: contraTneq => ->; have /and3P[] := D_partition. Qed.

Lemma partition_ex C : C \in P -> exists x, C = pblock P x.
Proof.
move=> /[dup]/partition_neq0/set0Pn[x xC] CP.
by exists x; apply/esym/def_pblock => //; have /and3P[] := D_partition.
Qed.

End EquivalencePartitionExtra.

Section Acyclic.

Variable V : finType.
Implicit Types g : rel V.

Lemma cyclexx g x : g x x -> cycle g [:: x].
Proof. by move=> gxx; rewrite /cycle /= gxx. Qed.

Canonical symconnect_equiv_rel g :=
  EquivalenceRel (symconnect g) (symconnect_equiv g).

Lemma symconnect_cycle g p : cycle g p ->
   {in p &, forall x y, symconnect g x y}.
Proof.
by move=> p_cycle x y x_p y_p; rewrite /symconnect !(connect_cycle p_cycle).
Qed.

Lemma sub_symconnect g g' :
  subrel g (connect g') -> subrel (symconnect g) (symconnect g').
Proof. by move=> /connect_sub subg x y /andP[/subg ? /subg ?]; apply/andP. Qed.

Definition rtclosed g := [forall x, forall y, connect g x y ==> g x y].

Lemma sub_connectP {g} : reflect (subrel (connect g) g) (rtclosed g).
Proof. exact: (iffP 'forall_'forall_implyP). Qed.

Lemma connect_eqP {g} : reflect (connect g =2 g) (rtclosed g).
Proof.
apply: (iffP sub_connectP) => + x y => [gP|-> //].
by apply/idP/idP => [/gP|/connect1].
Qed.

Lemma rtclosedP {g} : reflect (reflexive g /\ transitive g) (rtclosed g).
Proof.
apply: (iffP idP) => [/connect_eqP eqg|[grefl gtrans]].
  split=> [x|y x z]; first by rewrite -eqg connect0.
  by rewrite -!eqg; apply: connect_trans.
apply/sub_connectP => x y /connectP[p].
elim: p => //= [|z p IHp] in x *; first by move=> _ ->.
by move=> /andP[gxz gzp] eqy; apply: gtrans gxz _; apply: IHp.
Qed.

Lemma rtclosed_refl g : rtclosed g -> reflexive g.
Proof. by move=> /rtclosedP[]. Qed.

Lemma rtclosed_trans g : rtclosed g -> transitive g.
Proof. by move=> /rtclosedP[]. Qed.

Lemma connect_rtclosed g : rtclosed (connect g).
Proof. by apply/rtclosedP; split; [apply: connect0|apply: connect_trans]. Qed.
Hint Resolve connect_rtclosed : core.

Lemma equiv_rtclosed (g : equiv_rel V) : rtclosed g.
Proof. by apply/rtclosedP; split; [apply: equiv_refl | apply: equiv_trans]. Qed.
Hint Resolve equiv_rtclosed : core.

Lemma symconnect_rtclosed g : rtclosed (symconnect g).
Proof. by []. Qed.

Definition rstclosed g := [forall x, forall y, symconnect g x y == g x y].

Lemma symconnect_eqP {g} : reflect (symconnect g =2 g) (rstclosed g).
Proof. exact: (iffP 'forall_'forall_eqP). Qed.

Lemma sub_symconnectP {g} :
   reflect (symmetric g /\ subrel (symconnect g) g) (rstclosed g).
Proof.
apply: (iffP symconnect_eqP) => [gP|[gsym gsub] x y].
  by split=> x y; rewrite -?gP// symconnect_sym.
by apply/idP/idP => [/gsub//|gxy]; rewrite /symconnect !connect1// gsym.
Qed.

Lemma rstclosedP {g} : reflect (equivalence_rel g) (rstclosed g).
Proof.
apply: (iffP idP) => [/symconnect_eqP gP|/equiv_relP[{}g->]].
  by rewrite -(eq_equivalence_rel gP).
by apply/sub_symconnectP; split=> // x y /andP[]; rewrite !(connect_eqP _).
Qed.

Lemma equiv_rstclosed (g : equiv_rel V) : rstclosed g.
Proof. exact/rstclosedP. Qed.
Hint Resolve equiv_rstclosed : core.

Lemma rstclosed_ex {g} : rstclosed g -> { e : equiv_rel V | g = e }.
Proof. by move=> /rstclosedP/equiv_relP. Qed.

Lemma rstclosed_refl g : rstclosed g -> reflexive g.
Proof. by move=> /rstclosed_ex[R ->]. Qed.

Lemma rstclosed_sym g : rstclosed g -> symmetric g.
Proof. by move=> /rstclosed_ex[R ->]. Qed.

Lemma rstclosed_trans g : rstclosed g -> transitive g.
Proof. by move=> /rstclosed_ex[R ->]. Qed.

Lemma connect_id g : connect (connect g) =2 connect g.
Proof. exact/connect_eqP/connect_rtclosed. Qed.

Lemma symconnect_connect g : symconnect (connect g) =2 symconnect g.
Proof. by move=> x y; rewrite /symconnect !connect_id. Qed.

Lemma rstclosedW : {subset rstclosed <= rtclosed}.
Proof. by move=> _/rstclosed_ex[g ->]; apply/rtclosedP; split. Qed.

Lemma rstclosed_connect g : rstclosed g -> connect g =2 g.
Proof. by move=> /rstclosedW/connect_eqP. Qed.

Lemma connect_symconnect g : connect (symconnect g) =2 symconnect g.
Proof. exact/connect_eqP/symconnect_rtclosed. Qed.

Lemma symconnect_rstclosed g : rstclosed (symconnect g).
Proof. by []. Qed.

Lemma symconnect_id g : symconnect (symconnect g) =2 symconnect g.
Proof. exact/symconnect_eqP. Qed.

Lemma cycle_ex_symconnect g x p :
  cycle g (x :: p) -> ~~ g x x -> exists2 y, x != y & symconnect g x y.
Proof.
case: p => [/andP[->]//|y p] /[dup] /symconnect_cycle/(_ x y) sg /andP[gxy _].
by exists y; rewrite ?sg ?(in_cons, eqxx, orbT)//; apply: contraTneq gxy => <-.
Qed.

Lemma symconnect_cycle2P g x y : x != y ->
  reflect (exists2 p, y \in p & cycle g (x :: p)) (symconnect g x y).
Proof.
move=> Nxy; apply: (iffP idP) => [|[p yp]]; last first.
  by move=> /symconnect_cycle->; rewrite ?(in_cons, eqxx, yp, orbT).
move: Nxy => /[swap]/andP[/connectP[p gp ->] /connectP[]].
elim/last_ind => /=[_ <-|q z _]; first by rewrite eqxx.
rewrite rcons_path last_rcons => /[swap]{z}<- /andP[gq gzq] Nxy.
have := mem_last x p; rewrite in_cons eq_sym (negPf Nxy)/= => yp.
exists (p ++ q); first by rewrite mem_cat yp.
by rewrite rcons_path cat_path gp gq last_cat gzq.
Qed.

Definition preacyclic g := [forall x, forall y, symconnect g x y ==> (x == y)].

Lemma preacyclicP {g} :
  reflect (forall x y, symconnect g x y -> x = y) (preacyclic g).
Proof. by apply: (iffP 'forall_'forall_implyP) => [] gP *; apply/eqP/gP. Qed.

Lemma preacyclic_eqP {g} : reflect (symconnect g =2 eq_op) (preacyclic g).
Proof.
apply: (iffP preacyclicP); last by move=> eqg x y; rewrite eqg => /eqP.
by move=> eqxy x y; apply/idP/eqP => [/eqxy//|->].
Qed.

Lemma preacyclic_sccsP {g} :
  reflect {in sccs g, forall C : {set V}, #|C| <= 1} (preacyclic g).
Proof.
apply: (iffP preacyclicP) => [gNsymc C Cscc | card_sccs_le1 x y].
  apply/card_le1_eqP => x y xC yC.
  by apply: gNsymc; rewrite -mem_scc (def_scc Cscc yC).
rewrite -mem_scc => /card_le1_eqP; apply; rewrite ?mem_pblock ?cover_sccs//.
by rewrite card_sccs_le1 ?pblock_mem ?cover_sccs.
Qed.

Definition acyclic g := [forall x, ~~ g x x] && preacyclic g.

Lemma acyclicP {g} :
  reflect ((forall x, ~~ g x x) /\ preacyclic g) (acyclic g).
Proof. by apply: (iffP andP) => [] [/forallP]; split. Qed.

Lemma acyclic_cyclexx g x : acyclic g -> ~~ g x x.
Proof. by case/acyclicP. Qed.

Lemma acyclic_refl g x : acyclic g -> g x x = false.
Proof. by move/acyclic_cyclexx/negPf. Qed.

Lemma acyclic_symconnect_eq g : acyclic g -> symconnect g =2 eq_op.
Proof. by move=> /acyclicP[_ /preacyclic_eqP] eqxy x y. Qed.

Lemma acyclic_cycleP {g} :
  reflect (forall p, ~~ nilp p -> sorted g p -> ~~ cycle g p) (acyclic g).
Proof.
apply: (iffP acyclicP) => [|Ncycle]; last first.
  split; first by move=> x; have /(_ _ _)/nandP[] := Ncycle [:: x].
  apply/preacyclicP => x y; apply: contraTeq => neqxy.
  apply/symconnect_cycle2P => // -[p yp] /[dup].
  by rewrite [X in X -> _]/= rcons_path => /andP[gxp _]; apply/negP/Ncycle.
move=> [/(_ _)/negPf gN] /preacyclic_eqP e.
move=> [//|x [/=|y p] _]; rewrite ?gN// => /andP[gxy _].
have: ~~ symconnect g x y by rewrite e; apply: contraTneq gxy => ->; rewrite gN.
by apply: contra => /symconnect_cycle->; rewrite ?(in_cons, eqxx, orbT).
Qed.

Lemma symconnect_rev g : symconnect g =2 symconnect [rel x y | g y x].
Proof. by move=> x y; rewrite /symconnect connect_rev andbC connect_rev. Qed.

Lemma preacyclic_rev g : preacyclic g = preacyclic [rel x y | g y x].
Proof.
by apply/preacyclicP/preacyclicP => gc x y; rewrite -symconnect_rev => /gc.
Qed.

Lemma acyclic_rev g : acyclic g = acyclic [rel x y | g y x].
Proof. by rewrite /acyclic preacyclic_rev. Qed.

Lemma preacyclic_connect : {homo connect : g / preacyclic g}.
Proof.
move=> g /preacyclic_eqP eqsc; apply/preacyclicP => x y.
by rewrite symconnect_connect eqsc => /eqP.
Qed.

Lemma sub_preacyclic :
 {homo preacyclic : g g' / subrel g (connect g') >-> g' -> g}.
Proof.
move=> g g' subg /preacyclicP eqsc; apply/preacyclicP => x y.
by move=> /(sub_symconnect subg)/eqsc.
Qed.

Lemma sub_acyclic : {homo acyclic : g g' / subrel g g' >-> g' -> g}.
Proof.
move=> g g' subg /acyclicP[gxx /(sub_preacyclic _) pag].
apply/acyclicP; split; last by apply: pag => x y /subg/connect1.
by move=> x; apply: contra (gxx x); apply: subg.
Qed.

Lemma eq_preacyclic :
   {homo preacyclic : g g' / connect g =2 connect g' >-> g = g'}.
Proof.
by move=> g g' eqg; apply/idP/idP; apply/sub_preacyclic => x y;
   rewrite (eqg, =^~eqg); apply: connect1.
Qed.

Lemma eq_acyclic : {homo acyclic : g g' / g =2 g' >-> g = g'}.
Proof.
move=> g g' eqg.
by apply/idP/idP; apply/sub_acyclic => x y; rewrite (eqg, =^~eqg).
Qed.

End Acyclic.

#[export] Hint Resolve connect_rtclosed equiv_rtclosed : core.
Arguments preacyclicP {V g}.
Arguments preacyclic_sccsP {V g}.
Arguments acyclicP {V g}.
Arguments acyclic_cycleP {V g}.
Arguments sub_connectP {V g}.
Arguments connect_eqP {V g}.
Arguments rtclosedP {V g}.
Arguments sub_symconnectP {V g}.
Arguments symconnect_eqP {V g}.
Arguments rstclosedP {V g}.

Section AcyclicSCCS.

Variables (V : finType) (scc_seq : rel V -> seq (seq V)) (g : rel V).
Hypothesis uniq_flatten : uniq (flatten (scc_seq g)).
Hypothesis all_in_flatten : forall v : V, v \in flatten (scc_seq g).
Hypothesis class_symconnect : forall c, c \in scc_seq g ->
  exists x, forall y, (y \in c) = symconnect g x y.

Lemma sccs_ex C : C \in sccs g -> exists2 c, C = [set x in c] & c \in scc_seq g.
Proof.
move=> /(partition_ex (sccs_partition g))[x ->].
have /flattenP[c cscc xc] := all_in_flatten x; exists c => //.
apply/setP=> y; rewrite inE; have [z cz] := class_symconnect cscc.
by rewrite mem_scc cz; rewrite cz in xc; apply/esym/left_trans.
Qed.

Lemma sccsP c : c \in scc_seq g -> [set x in c] \in sccs g.
Proof.
move=> /class_symconnect[x xg].
suff -> : [set x in c] = pblock (sccs g) x by rewrite pblock_mem ?cover_sccs.
by apply/setP=> y; rewrite !inE mem_scc.
Qed.

Definition class_acyclic (c : seq V) :=
  if c is [:: v & vs] then (vs == [::]) && ~~ g v v else true.

Lemma class_acyclicP c (C := [set x in c]) : c \in scc_seq g ->
  reflect (#|C| <= 1 /\ {in C, forall x, ~~ g x x}) (class_acyclic c).
Proof.
case: c => [|v [|w vs]]//= in C * => vsscc.
- by have /and3P[_ _] := sccs_partition g; rewrite (sccsP vsscc).
- have -> : C = [set v] by apply/setP => x; rewrite !inE.
  rewrite cards1; apply: (iffP idP) => [Ngvv|[_ /(_ v (set11 _))//]].
  by split=> // x; rewrite !inE => /eqP->.
have -> : C = v |: (w |: [set x in vs]) by apply/setP => x; rewrite !inE.
have := uniq_flatten; rewrite (perm_uniq (perm_flatten (perm_to_rem vsscc))).
rewrite /= !inE !mem_cat/= !negb_or -!andbA => /and5P[Nvw vNvs _ wNvs _].
rewrite !cardsU1 !inE (negPf Nvw)/= vNvs wNvs !add1n !ltnS ltn0.
by apply: (iffP idP) => // -[].
Qed.

Definition sccs_acyclic := all [pred c | class_acyclic c] (scc_seq g).

Lemma sccs_acyclicE : sccs_acyclic = acyclic g.
Proof.
apply: (sameP allP); apply: (equivP acyclicP); rewrite -(rwP preacyclic_sccsP).
split=> /= [[/= Ng scc_le1 c cscc]|acyP].
  by apply/class_acyclicP => //; rewrite scc_le1 ?sccsP//; split.
split=> [x|C /sccs_ex[c -> /acyP/class_acyclicP[]]//].
have /flattenP[c /[swap] xc cscc] := all_in_flatten x.
by have /class_acyclicP[//|_->//] := acyP _ cscc; rewrite inE.
Qed.

End AcyclicSCCS.
