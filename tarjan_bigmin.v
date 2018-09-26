From mathcomp Require Import all_ssreflect.
Require Import bigmin extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tarjan.

Variable (V : finType) (successors : V -> seq V).
Notation edge := (grel successors).
Notation gconnect := (connect edge).
Notation infty := #|V|.+1.

(*************************************************************)
(*               Tarjan 72 algorithm,                        *)
(* rewritten in a functional style  with extra modifications *)
(*************************************************************)

Record env := Env {sccs : {set {set V}}; num: {ffun V -> nat}}.
Implicit Types (e : env) (x : V) (roots : {set V}).
Definition seen e := [set x | num e x < infty].
Notation sn e := #|seen e|.
Definition stack e := [set x | num e x < sn e].
Notation new_stack e1 e2 := (stack e2 :\: stack e1).

Definition visit x e :=
  Env (sccs e) (finfun [eta num e with x |-> sn e]).
Definition store scc e :=
  Env (scc |: sccs e) [ffun x => if x \in scc then #|V| else num e x].

Definition dfs1 dfs x e :=
    let: (m1, e1) as res := dfs [set y in successors x] (visit x e) in
    if m1 >= sn e then (#|V|, store (new_stack e e1) e1) else res.

Definition dfs dfs1 dfs roots e :=
  if [pick x in roots] isn't Some x then (#|V|, e) else
  let: (m1, e1) := if num e x != infty then (num e x, e) else dfs1 x e in
  let: (m2, e2) := dfs (roots :\ x) e1 in (minn m1 m2, e2).

Fixpoint tarjan_rec n :=
  if n is n.+1 then dfs (dfs1 (tarjan_rec n)) (tarjan_rec n)
  else fun r e => (#|V|, e).

Let N := #|V| * #|V|.+1 + #|V|.
Definition e0 := (Env set0 [ffun _ => infty]).
Definition tarjan := sccs (tarjan_rec N setT e0).2.

(*************************************************)
(* Connected components of the graph, abstractly *)
(*************************************************)

Notation gsymconnect := [rel x y | gconnect x y && gconnect y x].

Lemma gsymconnect_equiv : equivalence_rel gsymconnect.
Proof.
split; first by rewrite /gsymconnect /= connect0.
move=> /andP [xy yx]; rewrite /gsymconnect /=.
by apply/idP/idP => /andP [/(connect_trans _)-> // /connect_trans->].
Qed.

Definition gsccs := equivalence_partition gsymconnect setT.

Lemma gsccs_partition : partition gsccs setT.
Proof. by apply: equivalence_partitionP => ?*; apply: gsymconnect_equiv. Qed.

Definition cover_gsccs := cover_partition gsccs_partition.

Lemma trivIset_gsccs : trivIset gsccs.
Proof. by case/and3P: gsccs_partition. Qed.
Hint Resolve trivIset_gsccs.

Notation scc_of := (pblock gsccs).

Lemma mem_scc x y : x \in scc_of y = gsymconnect y x.
Proof.
by rewrite pblock_equivalence_partition // => ?*; apply: gsymconnect_equiv.
Qed.

Definition def_scc scc x := @def_pblock _ _ scc x trivIset_gsccs.

Definition connected := forall x y, gconnect x y.

Lemma cover1U (A : {set V}) P : cover (A |: P) = A :|: cover P.
Proof. by apply/setP => x; rewrite /cover bigcup_setU big_set1. Qed.

Lemma connectedU (A B : {set V}) : {in A &, connected} -> {in B &, connected} ->
  {in A & B, connected} -> {in B & A, connected} -> {in A :|: B &, connected}.
Proof.
move=> cA cB cAB cBA z t; rewrite !inE => /orP[zA|zB] /orP[tA|tB];
by[apply: cA|apply: cB|apply: cAB|apply: cBA].
Qed.

(*******************)
(* next, and nexts *)
(*******************)

Lemma setUD (B A C : {set V}) : B \subset A -> C \subset B -> 
  (A :\: B) :|: (B :\: C) = (A :\: C).
Proof.
move=> subBA subCB; apply/setP=> x; rewrite !inE.
have /implyP  := subsetP subBA x; have /implyP  := subsetP subCB x.
by do !case: (_ \in _).
Qed.

Lemma setUDl (T : finType) (A B : {set T}) : A :|: B :\: A = A :|: B.
Proof. by apply/setP=> x; rewrite !inE; do !case: (_ \in _). Qed.

Section Nexts.
Variable (D : {set V}).

Definition nexts (A : {set V}) :=
  \bigcup_(v in A) [set w in connect (relfrom (mem D) edge) v].

Lemma nexts0 : nexts set0 = set0.
Proof. by rewrite /nexts big_set0. Qed.

Lemma nexts1 x :
  nexts [set x] = x |: (if x \in D then nexts [set y in successors x] else set0).
Proof.
apply/setP=> y; rewrite /nexts big_set1 !inE.
have [->|neq_yx/=] := altP eqP; first by rewrite connect0.
apply/idP/idP=> [/connect1l[]// z/=/andP[/= xD xz zy]|].
  by rewrite xD; apply/bigcupP; exists z; rewrite !inE.
case: ifPn; rewrite ?inE// => xD /bigcupP[z]; rewrite !inE.
by move=> xz; apply/connect_trans/connect1; rewrite /= xD.
Qed.

Lemma nextsU A B : nexts (A :|: B) = nexts A :|: nexts B.
Proof. exact: bigcup_setU. Qed.

Lemma nextsS (A : {set V}) : A \subset nexts A.
Proof. by apply/subsetP=> a aA; apply/bigcupP; exists a; rewrite ?inE. Qed.

Lemma nextsT : nexts setT = setT.
Proof. by apply/eqP; rewrite eqEsubset nextsS subsetT. Qed.

Lemma nexts_id (A : {set V}) : nexts (nexts A) = nexts A.
Proof.
apply/eqP; rewrite eqEsubset nextsS andbT; apply/subsetP=> x.
move=> /bigcupP[y /bigcupP[z zA]]; rewrite !inE => /connect_trans yto /yto zx.
by apply/bigcupP; exists z; rewrite ?inE.
Qed.

Lemma in_nextsW A y : y \in nexts A -> exists2 x, x \in A & gconnect x y.
Proof.
move=>/bigcupP[x xA]; rewrite inE => xy; exists x => //.
by apply: connect_sub xy => u v /andP[_ /connect1].
Qed.

End Nexts.

Lemma sub_nexts (D D' A B : {set V}) :
  D \subset D' -> A \subset B -> nexts D A \subset nexts D' B.
Proof.
move=> /subsetP subD /subsetP subAB; apply/subsetP => v /bigcupP[a /subAB aB].
rewrite !inE => av; apply/bigcupP; exists a; rewrite ?inE //=.
by apply: connect_sub av => x y /andP[xD xy]; rewrite connect1//= subD.
Qed.

Lemma nextsUI A B C : nexts B A \subset A ->
  A :|: nexts (B :&: ~: A) C = A :|: nexts B C.
Proof.
move=> subA; apply/setP=> y; rewrite !inE; have [//|/= yNA] := boolP (y \in A).
apply/idP/idP; first by apply: subsetP; rewrite sub_nexts// subsetIl.
move=> /bigcupP[z zr zy]; apply/bigcupP; exists z; first by [].
rewrite !inE; apply: contraTT isT => Nzy; move: zy; rewrite !inE.
move=> /(connect_from (mem (~: A))) /= [t].
rewrite !inE => -[xtxy zt ty]; move: zt.
rewrite (@eq_connect _ _ (relfrom (mem (B :&: ~: A)) edge)); last first.
  by move=> u v /=; rewrite !inE andbCA andbA.
case: (altP eqP) xtxy => /= [<-|neq_yt]; first by rewrite (negPf Nzy).
rewrite implybF negbK => tA zt; rewrite -(negPf yNA) (subsetP subA)//.
by apply/bigcupP; exists t; rewrite // inE.
Qed.

Lemma nexts1_split (A : {set V}) x : x \in A ->
  nexts A [set x] = x |: nexts (A :\ x) [set y in successors x].
Proof.
move=> xA; apply/setP=> y; apply/idP/idP; last first.
  rewrite nexts1 !inE xA; case: (_ == _); rewrite //=.
  by apply: subsetP; rewrite sub_nexts// subsetDl.
move=> /bigcupP[z]; rewrite !inE => /eqP[{z}->].
move=> /connectP[p /shortenP[[_ _ _ /eqP->//|z q/=/andP[/andP[_ xz]]]]].
rewrite path_from => /andP[zq] /allP/= qA.
move=> /and3P[xNzq _ _] _ ->; apply/orP; right.
apply/bigcupP; exists z; rewrite !inE//.
apply/connectP; exists q; rewrite // path_from zq/=.
apply/allP=> t tq; rewrite !inE qA ?andbT//.
by apply: contraNneq xNzq=> <-; apply: mem_belast tq.
Qed.

(*******************)
(* Well formed env *)
(*******************)

Lemma num_lt_infty e x : num e x < infty = (x \in seen e).
Proof. by rewrite inE. Qed.

Lemma num_lt_sn e x : num e x < sn e = (x \in stack e).
Proof. by rewrite inE. Qed.

Lemma seen_visit e x : seen (visit x e) = x |: seen e.
Proof.
apply/setP=> y; rewrite !inE ffunE/=; case: (altP eqP);
by rewrite //= ltnS max_card.
Qed.

Lemma sub_stack_seen e : stack e \subset seen e.
Proof.
apply/subsetP => x; rewrite !inE => /leq_trans; apply;
by rewrite leqW// max_card.
Qed.

Lemma sub_new_stack_seen e1 e2: new_stack e1 e2 \subset seen e2.
Proof. by rewrite (subset_trans _ (sub_stack_seen _)) ?subsetDl. Qed.

Section wfenv.

Record wf_env e := WfEnv {
  sub_gsccs : sccs e \subset gsccs;
  max_num : forall x, num e x <= infty;
  num_lt_V_is_stack : forall x, num e x < #|V| -> num e x < sn e;
  num_sccs : forall x, (num e x == #|V|) = (x \in cover (sccs e));
  visit_new : forall x y, num e x <= num e y < sn e -> gconnect x y;
}.

Variables (e : env) (e_wf : wf_env e).

Lemma notseen_num x : x \notin seen e -> num e x = infty.
Proof. by rewrite inE ltn_neqAle max_num// andbT negbK => /eqP. Qed.

Lemma num_lt_V x : (num e x < #|V|) = (num e x < sn e).
Proof.
apply/idP/idP => [/num_lt_V_is_stack//|]; first exact.
by move=> /leq_trans; apply; rewrite max_card.
Qed.

Lemma num_lt_card x (A : pred V) : seen e \subset A ->
  (num e x < #|A|) = (num e x < sn e).
Proof.
move=> subeA; apply/idP/idP => /leq_trans.
  by rewrite -num_lt_V; apply; rewrite max_card.
by apply; rewrite subset_leq_card.
Qed.

Lemma seenE : seen e = stack e :|: cover (sccs e).
Proof.
by apply/setP=> x; rewrite !inE ltnS leq_eqVlt -num_sccs// num_lt_V orbC.
Qed.

Lemma vs_disjoint : [disjoint stack e & cover (sccs e)].
Proof.
rewrite -setI_eq0; apply/eqP/setP=> x; rewrite !inE -num_sccs//.
by rewrite -num_lt_V; case: ltngtP.
Qed.

Lemma sub_sccs_seen : cover (sccs e) \subset seen e.
Proof. by apply/subsetP => x; rewrite !inE -num_sccs// => /eqP->. Qed.

Lemma stack_visit x : x \notin seen e -> stack (visit x e) = x |: stack e.
Proof.
move=> xNseen; apply/setP=> y; rewrite !inE/= ffunE/= seen_visit.
have [->|neq_yx]//= := altP eqP; first by rewrite cardsU1 xNseen ltnS ?leqnn.
by rewrite num_lt_card// subsetUr.
Qed.

End wfenv.

Lemma wf_visit e x : wf_env e ->
   (forall y, num e y < sn e -> gconnect y x) ->
   x \notin seen e -> wf_env (visit x e).
Proof.
move=> e_wf x_connected xNseen; constructor=> [|y|y|y] //=; rewrite ?inE ?ffunE/=.
- exact: sub_gsccs.
- by case: ifP; rewrite ?max_num// leqW ?max_card.
- rewrite seen_visit cardsU1 xNseen; case: ifPn => // _.
  by rewrite num_lt_V// ltnS => /ltnW.
- have [->|] := altP (y =P x); last by rewrite num_sccs.
  rewrite -num_sccs// notseen_num// eq_sym !gtn_eqF//.
  by rewrite (@leq_trans #|x |: seen e|) ?max_card// cardsU1 xNseen.
move=> y z; rewrite !ffunE/=.
have sub_visit : seen e \subset seen (visit x e).
  by apply/subsetP => ?; rewrite seen_visit !inE orbC => ->.
have [{y}->|neq_yx] := altP eqP; have [{z}->|neq_zx]//= := altP eqP.
+ by rewrite num_lt_card//; case: ltngtP.
+ move=> /andP[/leq_ltn_trans lt/lt].
  by rewrite num_lt_card//; apply: x_connected.
+ by rewrite num_lt_card//; apply: visit_new.
Qed.

Definition subenv e1 e2 := [&&
  sccs e1 \subset sccs e2,
  [forall x, (num e1 x < infty) ==> (num e2 x == num e1 x)] &
  [forall x, (num e2 x < sn e1) ==> (num e1 x < sn e1)]].

Lemma sub_sccs e1 e2 : subenv e1 e2 -> sccs e1 \subset sccs e2.
Proof. by move=> /and3P[]. Qed.

Lemma sub_snum e1 e2 : subenv e1 e2 -> forall x, num e1 x < infty -> num e2 x = num e1 x.
Proof. by move=> /and3P[_ /forall_inP /(_ _ _) /eqP]. Qed.

Lemma sub_vnum e1 e2 : subenv e1 e2 -> forall x, num e1 x < sn e1 -> num e2 x = num e1 x.
Proof.
move=> sube12 x num_lt; rewrite (sub_snum sube12)//.
by rewrite (leq_trans num_lt)// leqW// max_card.
Qed.

Lemma sub_num_lt e1 e2 : subenv e1 e2 ->
  forall x, (num e1 x < sn e1) = (num e2 x < sn e1).
Proof.
move=> /and3P[_ /forall_inP /(_ _ _)/eqP num_eq /forall_inP] num_lt x.
have nume1_lt := num_lt x; apply/idP/idP => // {nume1_lt}nume1_lt.
by rewrite num_eq ?inE// (leq_trans nume1_lt)// leqW// max_card.
Qed.

Lemma sub_seen e1 e2 : subenv e1 e2 -> seen e1 \subset seen e2.
Proof.
move=> sube12; apply/subsetP=> x; rewrite !inE => x_seen1.
by rewrite (sub_snum sube12)// inE.
Qed.

Lemma leq_sn e1 e2 : subenv e1 e2 -> sn e1 <= sn e2.
Proof. by move=> sube12; rewrite subset_leq_card// sub_seen. Qed.

Lemma sub_stack e1 e2 : subenv e1 e2 -> stack e1 \subset stack e2.
Proof.
move=> sube12; apply/subsetP=> x; rewrite !inE => x_stack.
by rewrite (sub_vnum sube12)// (leq_trans x_stack)// leq_sn.
Qed.

Lemma new_stackE e1 e2 : subenv e1 e2 ->
  new_stack e1 e2 = [set x | sn e1 <= num e2 x < sn e2].
Proof.
move=> sube12; apply/setP=> x; rewrite !inE.
have [x_e2|] := ltnP (num e2 x) (sn e2); rewrite ?andbT ?andbF//.
have [e1_after|e1_before] /= := leqP (sn e1) (num e1 x).
  by rewrite leqNgt -sub_num_lt// -leqNgt.
by rewrite leqNgt -sub_num_lt// e1_before.
Qed.

Notation new_seen e1 e2 := (seen e2 :\: seen e1).

Lemma new_seenE e1 e2 : wf_env e1 -> wf_env e2 -> subenv e1 e2 ->
 (new_seen e1 e2) = (new_stack e1 e2) :|: cover (sccs e2) :\: cover (sccs e1).
Proof.
move=> e1_wf e2_wf sube12; rewrite !seenE//; apply/setP=> x.
rewrite !inE -!num_sccs -?num_lt_V//; do 2!case: ltngtP => //=.
  by rewrite num_lt_V// (sub_num_lt sube12)// => ->; rewrite ltnNge max_card.
by move=> xe2 xe1; move: xe2; rewrite (sub_snum sube12)// ?xe1// ltnn.
Qed.

Lemma sub_new_stack_new_seen e1 e2 : subenv e1 e2 -> wf_env e1 -> wf_env e2 ->
  (new_stack e1 e2) \subset (new_seen e1 e2).
Proof. by move=> e1_wf e2_wf sube12; rewrite (@new_seenE e1 e2)// subsetUl. Qed.

Lemma sub_refl e : subenv e e.
Proof. by rewrite /subenv !subxx /=; apply/andP; split; apply/forall_inP. Qed.
Hint Resolve sub_refl.

Lemma sub_trans : transitive subenv.
Proof.
move=> e2 e1 e3 sub12 sub23; rewrite /subenv.
rewrite (subset_trans (sub_sccs sub12))// ?sub_sccs//=.
apply/andP; split; apply/forall_inP=> x xP.
  by rewrite (sub_snum sub23) ?(sub_snum sub12)//.
have x2 : num e3 x < sn e2 by rewrite (leq_trans xP)// leq_sn.
by rewrite (sub_num_lt sub12)// -(sub_vnum sub23)// (sub_num_lt sub23).
Qed.

Lemma sub_visit e x : x \notin seen e -> subenv e (visit x e).
Proof.
move=> xNseen; rewrite /subenv subxx/=; apply/andP; split; last first.
  by apply/forall_inP => y; rewrite !ffunE/=; case: ifP; rewrite ?ltnn.
apply/forall_inP => y y_in; rewrite !ffunE/=.
by case: (altP (y =P x)) xNseen => // <-; rewrite inE y_in.
Qed.

Lemma stackE e : wf_env e -> stack e = seen e :\: cover (sccs e).
Proof.
move=> e_wf; apply/setP=> x; rewrite seenE// setDUl setDv setU0.
by rewrite !inE -num_sccs// -num_lt_V//; case: ltngtP.
Qed.

Lemma seen_store (A : {set V}) e : A \subset seen e -> seen (store A e) = seen e.
Proof.
move=> A_sub; apply/setP=> x; rewrite !inE/= ffunE.
by case: ifPn => // /(subsetP A_sub); rewrite inE leqnn => ->.
Qed.

Lemma stack_store (A : {set V}) e : A \subset seen e ->
  stack (store A e) = stack e :\: A.
Proof.
move=> A_sub; apply/setP => x; rewrite !inE seen_store//= ffunE.
by case: (x \in A); rewrite //= ltnNge max_card.
Qed.

(*********************)
(* DFS specification *)
(*********************)

Definition outenv (roots : {set V}) (e e' : env) := [/\
  {in new_stack e e' &, connected},
  {in new_stack e e', forall x, exists2 y, y \in stack e & gconnect x y} &
  seen e' = seen e :|: nexts (~: seen e) roots ].

Variant dfs_spec_def (dfs : nat * env) (roots : {set V}) e :
  (nat * env) -> nat -> env -> Type := DfsSpec me' m e' of
    me' = (m, e') &
    m = val (\min_(x in nexts (~:seen e) roots) @inord #|V| (num e' x)) &
    wf_env e' & subenv e e' & outenv roots e e' :
  dfs_spec_def dfs roots e me' m e'.
Notation dfs_spec dfs roots e := (dfs_spec_def dfs roots e dfs dfs.1 dfs.2).

Definition dfs_correct dfs roots e := wf_env e ->
  {in stack e & roots, connected} -> dfs_spec (dfs roots e) roots e.
Definition dfs1_correct dfs1 x e := wf_env e -> x \notin seen e ->
  {in stack e & [set x], connected} -> dfs_spec (dfs1 x e) [set x] e.

(*****************)
(* Correctness *)
(*****************)

Lemma dfsP dfs1 dfsrec (roots : {set V}) e:
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots -> forall e1, subenv e e1 -> dfs_correct dfsrec (roots :\ x) e1) ->
  dfs_correct (dfs dfs1 dfsrec) roots e.
Proof.
rewrite /dfs => dfs1P dfsP e_wf roots_connected.
case: pickP => /= [x x_roots|]; last first.
  move=> r0; have {r0}r_eq0 : roots = set0 by apply/setP=> x; rewrite inE.
  do ?constructor=> //=;
    rewrite ?setDv ?r_eq0 ?nexts0 ?sub0set ?eqxx ?setU0 ?big_set0 //=;
    by move=> ?; rewrite inE.
have [numx_infty|numx_ninfty]/= := altP eqP.
  case: dfs1P => //=; first by rewrite inE numx_infty ltnn.
    by move=> u v ue; rewrite inE => /eqP->; apply: roots_connected.
  move=> _ _  e1 -> -> e1_wf subee1 [new1c new1old seen1E].
  case: dfsP => //=.
    move=> u v ue1; rewrite inE => /andP[_ v_roots].
    have [ue|uNe] := boolP (u \in stack e); first by rewrite roots_connected.
    have [|w we] := new1old u; first by rewrite inE ue1 uNe.
    by move=> /connect_trans->//; rewrite roots_connected//.
  move=> _ _ e2 -> -> e2_wf sube12 [new2c new2old seen2E].
  have sube2 : subenv e e2 by exact: sub_trans sube12.
  have nexts_split : nexts (~: seen e) roots =
        nexts (~: seen e) [set x] :|: nexts (~: seen e1) (roots :\ x).
    by rewrite -[in LHS](setD1K x_roots) nextsU seen1E setCU nextsUI// nexts_id.
  constructor => //=.
    rewrite (eq_bigr (fun x => inord (num e2 x))); last first.
      move=> y y_in; rewrite (@sub_snum e1 e2)// num_lt_infty.
        by rewrite seen1E setUC inE y_in.
    by rewrite -[LHS]/(val (ord_minn _ _)) -bigmin_setU /= -nexts_split.
  constructor => /=.
  + rewrite -(@setUD (stack e1)) ?sub_stack//.
    apply: connectedU => // y z; last first.
      rewrite !new_stackE// ?inE => /andP[y_ge y_lt] /andP[z_ge z_lt].
      rewrite (@visit_new e2) // z_lt (leq_trans _ z_ge)//.
      by rewrite (sub_vnum sube12)// ltnW.
    rewrite !new_stackE// ?inE => /andP[y_ge y_lt] /andP[z_ge z_lt].
    have [|r] := new2old y; rewrite ?new_stackE ?inE ?y_ge//.
    move=> r_lt /connect_trans->//; have [rz|zr] := leqP (num e1 r) (num e1 z).
      by rewrite (@visit_new e1)// rz/=.
    by rewrite new1c ?new_stackE ?inE ?z_ge ?z_lt //= (leq_trans z_ge)// ltnW.
  + move=> y; rewrite ?new_stackE ?inE// => /andP[y_ge y_lt].
    have [y_lt1|y_ge1] := ltnP (num e1 y) (sn e1).
      have [|r] := new1old y; last by exists r.
      by rewrite new_stackE ?inE// ?y_lt1 -(sub_vnum sube12) ?y_ge.
    have [|r r_lt1 yr] := new2old y; first by rewrite !inE -leqNgt y_ge1//.
    rewrite ?inE in r_lt1; have [r_lt|r_ge] := ltnP (num e r) (sn e).
      by exists r; rewrite ?inE.
    have [|r' r's rr'] := new1old r; first by rewrite ?inE -leqNgt r_ge r_lt1.
    by exists r'; rewrite // (connect_trans yr rr').
  + by rewrite seen2E {1}seen1E nexts_split setUA.
have numx_lt : num e x < infty by rewrite ltn_neqAle numx_ninfty max_num.
have x_seen : x \in seen e by rewrite inE.
case: dfsP => //=.
  by move=> u v ue; rewrite inE => /andP[_ v_roots]; rewrite roots_connected.
move=> _ _  e1 -> -> e1_wf subee1 [new1c new1old seen1E].
constructor => //=.
  rewrite -[in RHS](setD1K x_roots) nextsU nexts1 inE x_seen/= setU0.
  by rewrite bigmin_setU /= big_set1/= (@sub_snum e e1)// inordK//.
constructor=> //=.
rewrite -(setD1K x_roots) nextsU nexts1 inE x_seen/= setU0 setUCA setUA.
by rewrite [x |: _](setUidPr _) ?sub1set.
Qed.

Lemma dfs1P dfs x e (A := [set y in successors x]):
  dfs_correct dfs A (visit x e) -> dfs1_correct (dfs1 dfs) x e.
Proof.
rewrite /dfs1 => dfsP e_wf xNseen x_connected.
have subexe: subenv e (visit x e) by exact: sub_visit.
have num0x : num e x = infty by apply: notseen_num.
have xNstack : x \notin stack e.
  by rewrite inE num0x ltnNge leqW// max_card.
have xe_wf : wf_env (visit x e).
  by apply: wf_visit => // y y_lt; rewrite x_connected ?inE.
have nexts1E : nexts (~: seen e) [set x] = x |: nexts (~: (x |: seen e)) A.
  by rewrite nexts1_split ?setDE ?setCU 1?setIC 1?inE.
case: dfsP => //=.
  rewrite stack_visit// => u v; rewrite in_setU1=> /predU1P[->|ue];
  rewrite inE => /(@connect1 _ edge)// /(connect_trans _)->//.
  by rewrite x_connected// set11.
move=> _ _ e1 //= -> -> e1_wf subxe1 [newc new_old seen1E].
have sube1 : subenv e e1 by apply: sub_trans subxe1.
have num1x : num e1 x = sn e.
  by rewrite (sub_snum subxe1)// ?inE ?ffunE/= ?eqxx// ltnS max_card.
rewrite seen_visit in seen1E *.
have lt_sn_sn1 : sn e < sn e1.
  by rewrite (leq_trans _ (leq_sn subxe1))// seen_visit cardsU1 xNseen.
have x_seen1 : x \in seen e1 by rewrite seen1E inE setU11.
have [min_after|min_before] := leqP; last first.
  have x_stack : x \in stack e1.
    by rewrite (subsetP (sub_stack subxe1))//= stack_visit// setU11.
  constructor => //=.
    rewrite nexts1E bigmin_setU big_set1 /= inordK ?num1x ?ltnS ?max_card//.
    by rewrite (minn_idPr _)// ltnW.
  constructor=> //=; last by rewrite nexts1E setUCA setUA seen1E.
    move=> y z; have [-> _|neq_yx] := eqVneq y x.
      by rewrite new_stackE ?inE// -num1x; apply: visit_new.
    rewrite -(@setUD (stack (visit x e))) ?sub_stack//.
    rewrite [in X in _ :|: X]stack_visit// setDUl setDv setU0.
    rewrite [_ :\: stack e](setDidPl _) ?disjoint1s//.
    rewrite setUC !in_setU1 (negPf neq_yx)/=.
    move=> y_e1 /predU1P[->|]; last exact: newc y_e1.
    have [t] := new_old y y_e1; rewrite !inE => t_le /connect_trans->//.
    rewrite (@visit_new (visit x e))// andbC; move: t_le.
    by rewrite seen_visit !ffunE /= eqxx cardsU1 xNseen add1n !ltnS leqnn.
  move=> y; have [v ve xv] : exists2 v, v \in stack e & gconnect x v.
    have [|v] := @eq_bigmin_cond _ _ (mem (nexts (~: (x |: seen e)) A))
                               (@inord #|V| \o (num e1)).
      rewrite card_gt0; apply: contraTneq min_before => ->.
      by rewrite big_set0 -leqNgt max_card.
    rewrite !inE => v_in min_is_v; move: min_before; rewrite min_is_v/=.
    rewrite inordK; last by rewrite num_lt_infty seen1E inE v_in orbT.
    rewrite -sub_num_lt// => v_lt; exists v; rewrite ?inE//.
    move: v_in => /in_nextsW[z]; rewrite inE => /(@connect1 _ edge).
    by apply: connect_trans.
  rewrite -(@setUD (stack (visit x e))) ?sub_stack//.
  rewrite [in X in _ :|: X]stack_visit// setDUl setDv setU0.
  rewrite [_ :\: stack e](setDidPl _) ?disjoint1s// setUC !in_setU1.
  move=> /predU1P[->|]; first by exists v.
  move=> /new_old[z]; rewrite stack_visit// in_setU1.
  move=> /predU1P[->|]; last by exists z.
  by move=> yx; exists v; rewrite // (connect_trans yx).
have all_geq y : y \in nexts (~: seen e) [set x] ->
  (#|seen e| <= num e1 y) * (num e1 y < infty).
  have := min_after; have sn_inord : sn e = @inord #|V| (sn e).
    by rewrite inordK// ltnS max_card.
  rewrite {1}sn_inord; move/bigmin_geqP => /(_ y) y_ge.
  rewrite nexts1E !inE => /predU1P[->|yA]; rewrite ?num1x.
    by rewrite ltnS max_card leqnn.
  rewrite sn_inord (leq_trans (y_ge _))// ?inordK//;
  by rewrite num_lt_infty seen1E 2!inE yA orbT.
constructor => //=.
- rewrite big1// => y xy; rewrite ffunE new_stackE ?inE//=.
  have y_seen1 : num e1 y < infty.
    by rewrite num_lt_infty seen1E -setUA setUCA -nexts1E inE xy orbT.
  apply/val_inj=> /=; case: ifPn; rewrite ?inordK//.
  rewrite all_geq//= -num_lt_V// -leqNgt; move: y_seen1; rewrite ltnS.
  by case: ltngtP.
- constructor => //=; rewrite ?seen_store ?sub_new_stack_seen//.
  + rewrite subUset sub_gsccs// andbT sub1set.
    suff -> : new_stack e e1 = scc_of x by rewrite pblock_mem ?cover_gsccs.
    apply/setP=> y; rewrite mem_scc /=.
    have [->|neq_yx] := eqVneq y x.
      by rewrite connect0 !inE num0x -leqNgt leqW ?max_card//= num1x lt_sn_sn1.
    apply/idP/andP=> [|[xy yx]].
      move=> y_ee1; have y_xee1 : y \in new_stack (visit x e) e1.
        by rewrite inE stack_visit// in_setU1 (negPf neq_yx)/= -in_setD.
      split; last first.
        have [z] := new_old _ y_xee1.
        rewrite stack_visit// in_setU1 => /predU1P[->//|/x_connected].
        by move=> /(_ _ (set11 x))/(connect_trans _) xz /xz.
      have: y \in new_seen (visit x e) e1.
        by apply: subsetP y_xee1; rewrite sub_new_stack_new_seen.
      rewrite inE seen1E in_setU seen_visit//; case: (y \in _ |: _) => //=.
      move=> /in_nextsW[z]; rewrite inE=> /(@connect1 _ edge).
      exact: connect_trans.
    have /(connect_from (mem (~: seen e))) [z []] := xy; rewrite inE.
    move=> eq_yz xz zy; have /all_geq [] : z \in nexts (~: seen e) [set x].
      by apply/bigcupP; exists x; rewrite !inE.
    rewrite leqNgt -sub_num_lt// -num_lt_V// -leqNgt ltnS => zNstack.
    have zNcover e' : wf_env e' -> z \in cover (sccs e') -> x \in cover (sccs e').
      move=> e'_wf /bigcupP[C] Ce zC; apply/bigcupP; exists C => //.
      have /def_scc: C \in gsccs by apply: subsetP Ce; apply: sub_gsccs.
      move=> /(_ _ zC)<-; rewrite mem_scc /= (connect_trans zy)//=.
      by apply: connect_sub xz => ?? /andP[_ /connect1].
    rewrite leq_eqVlt num_sccs// num_lt_V// => /orP[|z_stack].
       move=> /zNcover; rewrite -num_sccs// num1x => /(_ _) /eqP eq_V.
       by rewrite eq_V// ltnNge max_card in lt_sn_sn1.
    have zNseen : z \notin seen e.
      rewrite inE -leqNgt ltn_neqAle eq_sym num_sccs// zNstack andbT.
      apply: contraTN isT => /(zNcover _ e_wf).
      by rewrite -num_sccs// num0x; elim: #|V|.
    move: eq_yz; rewrite zNseen /= => /andP[/eqP eq_yz _].
    rewrite -eq_yz in zNstack z_stack.
    by rewrite !inE -num_lt_V// -leqNgt zNstack.
  + by move=> v; rewrite ffunE/=; case: ifP; rewrite ?max_num //.
  + move=> v; rewrite ffunE/=; case: ifPn; rewrite ?ltnn// => vNe12.
    by rewrite num_lt_V// seen_store.
  + move=> v; rewrite ffunE /= cover1U [in RHS]inE.
    by case: ifPn; rewrite ?eqxx//= => vNe12; rewrite -num_sccs//.
  + move=> y z; rewrite !ffunE; case: ifPn => _.
      by move=> /andP[/leq_ltn_trans Vsmall/Vsmall]; rewrite ltnNge max_card.
    by case: ifPn => _; [by rewrite ltnNge max_card andbF|exact : visit_new].
- rewrite /subenv /= (subset_trans (sub_sccs sube1)) ?subsetUr//=.
  apply/andP; split; apply/forallP => v; apply/implyP;
  rewrite ffunE/= new_stackE// ?inE.
    move=> vs; rewrite (sub_snum sube1)// leqNgt -!num_lt_V// -leqNgt ifN//.
    by apply/negP => /andP[/leq_ltn_trans Vlt/Vlt]; rewrite ltnNge max_card.
  by case: ifPn; [move=> _; rewrite ltnNge max_card|rewrite -sub_num_lt].
- rewrite /outenv stack_store ?seen_store ?sub_new_stack_seen//.
  rewrite setDDr setDUl setDv set0D set0U setDIl !setDv setI0.
  split; do ?by move=> ?; rewrite inE.
  by rewrite seen1E -setUA setUCA -nexts1E.
Qed.

Theorem tarjan_rec_terminates n (roots : {set V}) e :
  n >= #|~: seen e| * #|V|.+1 + #|roots| ->
  dfs_correct (tarjan_rec n) roots e.
Proof.
move=> n_ge; elim: n => [|n IHn/=] in roots e n_ge *.
  move: n_ge; rewrite leqn0 addn_eq0 cards_eq0 => /andP[_ /eqP-> e_wf _]/=.
  constructor=> //=; rewrite /outenv ?nexts0 ?setDv ?big_set0// ?setU0.
  by split=> // ?; rewrite inE.
apply: dfsP=> x x_roots; last first.
  move=> e1 subee1; apply: IHn; rewrite -ltnS (leq_trans _ n_ge)//.
  rewrite (cardsD1 x roots) x_roots add1n -addSnnS ltn_add2r ltnS.
  by rewrite leq_mul2r //= subset_leq_card// setCS sub_seen.
move=> e_wf xNseen; apply: dfs1P => //; apply: IHn.
rewrite seen_visit setCU setIC -setDE -ltnS (leq_trans _ n_ge)//.
rewrite (cardsD1 x (~: _)) inE xNseen add1n mulSnr -addnA ltn_add2l.
by rewrite ltn_addr// ltnS max_card.
Qed.

Lemma seen0 : seen e0 = set0.
Proof. by apply/setP=> y; rewrite !inE ffunE ltnn. Qed.

Lemma stack0 : stack e0 = set0.
Proof. by apply/setP=> y; rewrite !inE ffunE ltnNge leqW ?max_card. Qed.

Lemma tarjan_recP : tarjan_rec N setT e0 = (#|V|, Env gsccs [ffun x => #|V|]).
Proof.
case: tarjan_rec_terminates; first by rewrite seen0 setC0 cardsT.
- constructor; rewrite /= ?sub0set// => x; rewrite !ffunE//.
  + by rewrite ltnNge leqW//.
  + by rewrite gtn_eqF// /cover big_set0 inE.
  + by move=> y; rewrite !ffunE//= andbC ltnNge leqW// ?max_card.
  + by move=> y; rewrite !inE !ffunE/= ltnNge leqW// max_card.
move=> _ _ e -> -> e_wf _ [_]; rewrite stack0 setD0.
have [stacke _|[x xe]] := set_0Vmem (stack e); last first.
  by move=> /(_ _ xe)[?]; rewrite inE.
rewrite seen0 set0U setC0 nextsT => seene.
have numE x : num e x = #|V|.
  apply/eqP; have /setP/(_ x) := seene.
  by rewrite seenE// stacke set0U !inE -num_sccs.
have sccse : sccs e = gsccs.
  apply/eqP; rewrite eqEsubset sub_gsccs//=; apply/subsetP => _/imsetP[/=x _->].
  have: x \in cover (sccs e) by rewrite -num_sccs ?numE//.
  move=> /bigcupP [C Csccs /(def_scc (subsetP (sub_gsccs e_wf) _ Csccs))] eqC.
  rewrite -eqC (_ : [set _ in _ | _] = scc_of x)// in Csccs *.
  by apply/setP => y; rewrite !inE mem_scc /=.
rewrite big1; last by move=> x _; apply: val_inj; rewrite /= inordK// ?numE.
congr (_, _); case: e {stacke seene e_wf} => /= sccs num in numE sccse *.
by congr (Env _ _) => //; apply/ffunP=> x; rewrite ffunE.
Qed.

Theorem tarjan_correct : tarjan = gsccs.
Proof. by rewrite /tarjan; have [->] := tarjan_recP. Qed.

End tarjan.
