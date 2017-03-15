From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop finset finfun perm fingraph path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section extra.

Lemma drop_subseq (T : eqType) n (s : seq T) : subseq (drop n s) s.
Proof. by rewrite -[X in subseq _ X](cat_take_drop n) suffix_subseq. Qed.

Lemma uniq_catLR (T : eqType) (x : T) s1 s2 : uniq (s1 ++ s2) ->
  x \in s1 ++ s2 -> (x \in s1) = (x \notin s2).
Proof.
rewrite mem_cat=> s_uniq /orP[] x_in; move: s_uniq.
  by rewrite uniq_catC cat_uniq => /and3P[_ /hasPn /(_ _ x_in)->].
by rewrite cat_uniq => /and3P[_ /hasPn /(_ _ x_in) /= /negPf->]; rewrite x_in.
Qed.

Lemma uniq_catRL (T : eqType) (x : T) s1 s2 : uniq (s1 ++ s2) ->
  x \in s1 ++ s2 -> uniq (s1 ++ s2) -> (x \in s2) = (x \notin s1).
Proof.
rewrite mem_cat uniq_catC => s_uniq x_s.
by rewrite (uniq_catLR s_uniq) // mem_cat orbC.
Qed.

End extra.

Section tarjan.
Variable (V : finType) (successors : V -> seq V).
Notation edge := (grel successors).
Notation gconnect := (connect edge).
Notation infty := #|V|.

Definition split_after (T :eqType) (x : T) (s : seq T) :=
  let i := index x s in (rcons (take i s) x, drop i.+1 s).

Fixpoint rank (x : V) stack : nat :=
  if stack isn't y :: s then infty
  else if (x == y) && (x \notin s) then size s else rank x s.

Lemma rankE x stack :
  rank x stack = if x \in stack then index x (rev stack) else infty.
Proof.
elim: stack => [|a s /= ->] //.
have [->|neq_xa] /= := altP eqP; rewrite rev_cons -cats1.
  by rewrite mem_head index_cat mem_rev /= eqxx addn0 size_rev; case: in_mem.
by rewrite in_cons (negPf neq_xa) /= index_cat /= mem_rev; case: in_mem.
Qed.

Lemma rank_cons x y s : rank x (y :: s) =
  if (x == y) && (x \notin s) then size s else rank x s.
Proof. by []. Qed.

Lemma rank_catl x s s' : x \in s' -> rank x (s ++ s') = rank x s'.
Proof.
by move=> x_s; rewrite !rankE rev_cat mem_cat x_s orbT index_cat mem_rev x_s.
Qed.

Lemma rank_catr x s s' :
  x \in s -> x \notin s' -> rank x (s ++ s') = size s' + rank x s.
Proof.
move=> x_s xNs'; rewrite !rankE rev_cat mem_cat x_s /=.
by rewrite index_cat mem_rev (negPf xNs') size_rev.
Qed.

Arguments rank : simpl never.

Record env := Env {blacks : {set V}; stack : seq V; sccs : {set {set V}}}.
Definition grays (e : env) := [set x in stack e] :\: blacks e.
Definition whites (e : env) := ~: (grays e :|: blacks e).

Definition add_stack x e := Env (blacks e) (x :: stack e) (sccs e).
Definition add_blacks x e := Env (x |: blacks e) (stack e) (sccs e).
Definition add_sccs x e := let (s2, s3) := split_after x (stack e) in
                            Env (x |: blacks e) s3 ([set y in s2] |: sccs e).

Definition dfs1 (dfs' : {set V} -> env -> nat * env) (x : V) e :=
    let m := rank x (x :: stack e) in
    let: (m1, e1) := dfs' [set y in successors x] (add_stack x e) in
    if m1 >= m then (infty, add_sccs x e1) else (m1, add_blacks x e1).

Definition dfs' dfs1 dfs' (roots : {set V}) e :=
  if [pick x in roots] isn't Some x then (infty, e)
  else let roots' := roots :\ x in
       let: (m1, e1) :=
         if x \in stack e then (rank x (stack e), e)
         else if x \in blacks e then (infty, e)
         else dfs1 x e in
       let: (m2, e2) := dfs' roots' e1 in (minn m1 m2, e2).

Fixpoint tarjan n : {set V} -> env -> nat * env :=
  if n is n.+1 then dfs' (dfs1 (tarjan n)) (tarjan n)
  else fun r e => (infty, e).

Notation gbiconnect := [rel x y | gconnect x y && gconnect y x].
Lemma gbiconnect_equiv : equivalence_rel gbiconnect.
Proof.
split; first by rewrite /gbiconnect /= connect0.
move=> /andP [xy yx]; rewrite /gbiconnect /=.
by apply/idP/idP => /andP [/(connect_trans _)-> // /connect_trans->].
Qed.

Definition gsccs := equivalence_partition gbiconnect setT.

Lemma gsccs_partition : partition gsccs setT.
Proof. by apply: equivalence_partitionP => ?*; apply: gbiconnect_equiv. Qed.

Lemma trivIset_gsccs : trivIset gsccs.
Proof. by case/and3P: gsccs_partition. Qed.
Hint Resolve trivIset_gsccs.

Notation scc_of := (pblock gsccs).

Lemma mem_scc x y : x \in scc_of y = gbiconnect y x.
Proof.
by rewrite pblock_equivalence_partition // => ?*; apply: gbiconnect_equiv.
Qed.

Definition def_scc scc x := @def_pblock _ _ scc x trivIset_gsccs.

(* Lemma mem_scc x (scc : {set V}) : scc \in gsccs -> x \in scc -> scc = scc_of x. *)
(* Proof. *)
(* move=> /imsetP [y _ ->]; rewrite inE => /and3P [_ yx xy]. *)
(* gen have sub_ssc_of : x y yx xy / scc_of y \subset scc_of x. *)
(*    apply/subsetP=> z; rewrite !inE /= => /andP [yz zy]. *)
(*    by rewrite (connect_trans xy) // (connect_trans zy). *)
(* by apply/eqP; rewrite eqEsubset !sub_ssc_of. *)
(* Qed. *)

Inductive wf_env e := WfEnv {
   wf_stack : [set x in stack e] =
              grays e :|: (blacks e :\: cover (sccs e));
   wf_sccs : cover (sccs e) \subset blacks e;
   wf_stack_uniq : uniq (stack e)
}.

Inductive color_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| ColorGray of x \in grays e : color_spec x e false true false true false
| ColorSccs of x \in cover (sccs e) :
                       color_spec x e true false true false false
| ColorWhite of x \in whites e : color_spec x e false false false false true
| ColorBlackStack of x \in blacks e & x \in stack e :
                        color_spec x e true true false false false.

Lemma colorP x e : wf_env e ->
                   color_spec x e (x \in blacks e) (x \in stack e)
                              (x \in cover (sccs e))
                              (x \in grays e) (x \in whites e).
Proof.
move=> [/setP /(_ x) s_def] /subsetP /(_ x) /implyP.
move: s_def; rewrite /grays /whites !inE.
case x_black: (_ \in blacks _) => /=;
case x_stack : (_ \in stack _) => /=;
case x_sccs : (_ \in cover _) => //=; do ?by constructor.
  by constructor=> //; rewrite /grays !inE x_black.
by constructor; rewrite /whites !inE x_black x_stack.
Qed.

Lemma whites_blacksF x e : x \in whites e -> x \in blacks e = false.
Proof. by rewrite !inE; case: (x \in blacks _). Qed.

Lemma whites_stackF x e : x \in whites e -> x \in stack e = false.
Proof. by rewrite !inE andbC; case: (x \in stack _); rewrite //= orNb. Qed.

Lemma whites_graysF x e : x \in whites e -> x \in grays e = false.
Proof. by rewrite !inE andbC; case: (x \in stack _); rewrite //= orNb. Qed.

Lemma grays_stack x e : x \in grays e -> x \in stack e.
Proof. by rewrite !inE andbC; case: (x \in stack _). Qed.

Lemma grays_sccsF x e : wf_env e -> x \in grays e ->
   x \in cover (sccs e) = false.
Proof. by case/colorP. Qed.

Lemma sccs_stackF x e : wf_env e ->
  x \in cover (sccs e) -> x \in stack e = false.
Proof. by case/colorP. Qed.

Lemma add_stack_ewf x e : x \in whites e -> wf_env e -> wf_env (add_stack x e).
Proof.
move=> x_white [s_def sccs_blacks s_uniq]; split => //=;
  last by rewrite whites_stackF.
apply/setP=> y; rewrite !inE.
by have [->|] := altP (y =P x); case: colorP=> //=; case: colorP x_white.
Qed.

Lemma add_blacks_ewf x e : x \in grays e -> wf_env e -> wf_env (add_blacks x e).
Proof.
move=> x_gray [s_def sccs_blacks s_uniq]; split => //=; last first.
  by rewrite subsetU // sccs_blacks orbT.
apply/setP=> y; rewrite !inE.
by have [->|] := altP (y =P x); case: colorP=> //=; case: colorP x_gray.
Qed.

Hint Resolve wf_stack_uniq.

Lemma add_sccs_wf x e :
  take (index x (stack e)) (stack e) \subset blacks e ->
  x \in grays e -> wf_env e -> wf_env (add_sccs x e).
Proof.
move=> /subsetP new_blacks x_gray e_wf.
have [s_def /subsetP sccs_blacks s_uniq] := e_wf.
split => //=; last first.
- by rewrite (subseq_uniq (drop_subseq _ _)).
- apply/subsetP=> y; rewrite !inE.
  rewrite /cover bigcup_setU inE big_set1 !inE /= => /orP[|/sccs_blacks->];
    last by rewrite !orbT.
  by rewrite mem_rcons !inE; case: eqP => //= _ /new_blacks.
apply/setP=> y; rewrite !inE /cover bigcup_setU inE big_set1 !inE !negb_or.
have [->|neq_xy] //= := altP (y =P x); rewrite ?(andbT, andbF).
  case: splitP new_blacks s_uniq => //=; first by rewrite grays_stack.
  move=> s1 s2 s1x_blacks s_uniq; rewrite grays_sccsF // andbT.
  by rewrite (uniq_catRL s_uniq) // mem_cat mem_rcons mem_head.
case: colorP; rewrite ?(andbT, andbF, orbT, orbF) //=.
  by move=> y_sccs; apply: contraTF y_sccs => /mem_drop; case: colorP.
move=> y_blacks; case: splitP s_uniq; first by rewrite grays_stack.
by move=> s1 s2 s_uniq y_in; apply: uniq_catRL.
Qed.

Definition noblack_to_white e :=
  forall x, x \in blacks e -> [disjoint successors x & whites e].

Inductive wf_graph e := WfGraph {
  wf_grays_to_stack : {in grays e & stack e, forall x y,
         (rank x (stack e) <= rank y (stack e)) -> gconnect x y};
  wf_stack_to_grays : forall y, y \in stack e ->
                      exists x, [/\ x \in grays e,
     (rank x (stack e) <= rank y (stack e)) & gconnect y x]
  }.

Lemma whites_add_stack x e : whites (add_stack x e) = whites e :\ x.
Proof.
apply/setP=> y; rewrite !inE /=.
by case: (_ \in _) (_ \in _) (_ == _) => [] [] [].
Qed.

Lemma grays_add_stack x e : x \in whites e ->
  grays (add_stack x e) = x |: grays e.
Proof.
move=> x_whites; apply/setP=> y; move: x_whites; rewrite !inE.
by case: eqP => [->|]; case: (_ \in _) (_ \in _)=> [] [].
Qed.

Lemma stack_add_stack x e : stack (add_stack x e) = x :: stack e.
Proof. by []. Qed.

(* Lemma grays_add_stack x e : x \in blacks e ->  *)
(*   grays (add_stack x e) = x |: grays e. *)
(* Proof. *)
(* move=> x_whites; apply/setP=> y; move: x_whites; rewrite !inE. *)
(* by case: eqP => [->|]; case: (_ \in _) (_ \in _)=> [] []. *)
(* Qed. *)

Lemma rank_small x s : uniq s -> (rank x s < size s) = (x \in s).
Proof.
move=> s_uniq; rewrite rankE; case: (boolP (x \in s)) => [xNs|_].
  by rewrite -size_rev index_mem mem_rev.
apply: negbTE; rewrite -ltnNge ltnS cardE uniq_leq_size //.
by move=> y; rewrite mem_enum.
Qed.

Definition access_to e (roots : {set V}) :=
  (forall x, x \in grays e ->
   forall y, y \in roots -> gconnect x y).

Definition black_gsccs e := [set scc in gsccs | scc \subset blacks e].

Inductive pre_dfs (roots : {set V}) (e : env) := PreDfs {
  pre_access_to : access_to e roots;
  pre_wf_env : wf_env e;
  pre_wf_graph : wf_graph e;
  wf_noblack_towhite : noblack_to_white e;
  pre_sccs : sccs e = black_gsccs e;
}.

Lemma add_stack_gwf e w :
  access_to e [set w] -> wf_env e -> w \in whites e -> wf_graph e ->
  wf_graph (add_stack w e).
Proof.
move=> grays_to e_wf w_white [gs sg]; split.
- rewrite grays_add_stack //= => x y; rewrite rank_cons !inE.
  move=> /orP[/eqP->|/andP[xNb xs]] /orP[/eqP->|/=ys];
  rewrite ?rank_cons ?eqxx ?(@whites_stackF w) ?xs ?ys ?(andbF, andbT) //=.
  + by rewrite leqNgt rank_small ?wf_stack_uniq // ys.
  + by move=> _; rewrite grays_to ?inE //= xNb.
  + by apply: gs; rewrite ?inE ?xNb.
- move=> y; rewrite inE => /predU1P [->|].
    exists w; rewrite ?grays_add_stack ?inE ?eqxx //.
    by rewrite whites_blacksF ?whites_stackF.
  move=> y_stack; have /sg [x [x_gray le_xy y_to_x]] := y_stack.
  exists x; split=> //.
    by rewrite grays_add_stack // inE x_gray orbT.
  rewrite stack_add_stack !rank_cons [x == w]negbTE /= 1?[y == w]negbTE //=.
    by apply: contraTneq y_stack => ->; rewrite whites_stackF.
  by apply: contraTneq x_gray => ->; rewrite whites_graysF.
Qed.

Lemma add_stack_pre e w :
  access_to e [set w] -> wf_env e -> w \in whites e -> wf_graph e ->
  access_to (add_stack w e) [set x in successors w].
Proof.
move=> grays_to e_wf w_white e_gwf.
move=> x; rewrite grays_add_stack // 2?inE => /predU1P [->|].
  by move=> y; rewrite inE => y_succ_w; rewrite connect1.
move=> /grays_to x_to_y y; rewrite inE => y_succ_w.
by rewrite (connect_trans _ (connect1 y_succ_w)) // x_to_y ?inE.
Qed.

Definition xedges (new old : seq V) :=
  [set y in old | [exists x in new, (x \notin old) && edge x y]].

Definition rank_of_reachable m x s :=
  exists2 y, y \in gconnect x & m = rank y s.

Definition post_dfs (roots : {set V}) (e e' : env) (m : nat) :=
[/\ [/\ wf_env e', wf_graph e', noblack_to_white e',
    grays e' = grays e & sccs e' = black_gsccs e'],

   [/\
    exists2 s, stack e' = s ++ stack e & s \subset (blacks e'),
    blacks e \subset blacks e'  & sccs e \subset sccs e' ]&

   [/\
    forall x, x \in roots -> m <= rank x (stack e'),
    m = infty \/ exists2 x, x \in roots & rank_of_reachable m x (stack e') &
    forall y, y \in xedges (stack e') (stack e) -> m <= rank y (stack e')
   ]
  ].

Definition dfs1_correct (dfs1 : V -> env -> nat * env) x e :=
  (x \in whites e) -> pre_dfs [set x] e ->
  let (m, e') := dfs1 x e in
  (x \in blacks e') /\ post_dfs [set x] e e' m.

Definition dfs'_correct (dfs' : {set V} -> env -> nat * env) roots e :=
  pre_dfs roots e ->
  let (m, e') := dfs' roots e in
  roots \subset blacks e' :|: grays e' /\ post_dfs roots e e' m.

Lemma pre_dfs_subroots (roots roots' : {set V}) e : roots' \subset roots ->
  pre_dfs roots e -> pre_dfs roots' e.
Proof.
move=> sub_roots [to_roots e_wf e_gwf black_sccs Nbw]; split=> //.
by move=> x x_gray y y_roots'; rewrite to_roots //; apply: subsetP y_roots'.
Qed.

Lemma rank_le x (s : seq V) : uniq s -> rank x s <= infty.
Proof.
move=> s_uniq; rewrite rankE; case: ifP => // x_s.
by rewrite (leq_trans (index_size _ _)) ?size_rev -?(card_uniqP _) // max_card.
Qed.

Lemma rank_lt x (s : seq V) : uniq s -> (rank x s < infty) = (x \in s).
Proof.
rewrite rankE; case: ifPn; rewrite ?ltnn // => x_s s_uniq.
rewrite (@leq_trans (size (rev s))) ?index_mem ?mem_rev ?size_rev //.
by rewrite -?(card_uniqP _) // max_card.
Qed.

Lemma rank_infty x (s : seq V) : x \notin s -> rank x s = infty.
Proof. by rewrite rankE => /negPf->. Qed.

Lemma subset_bigcup (sccs sccs' : {set {set V}}) :
  sccs \subset sccs' -> cover sccs \subset cover sccs'.
Proof.
move=> /subsetP subsccs; apply/subsetP=> x /bigcupP [scc /subsccs].
by move=> scc' x_in; apply/bigcupP; exists scc.
Qed.

Lemma dfs'_is_correct dfs1 dfsrec' (roots : {set V}) e :
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots ->
     let: (m1, e1) :=
        if x \in stack e then (rank x (stack e), e)
        else if x \in blacks e then (infty, e)
             else dfs1 x e in dfs'_correct dfsrec' (roots :\ x) e1) ->
  dfs'_correct (dfs' dfs1 dfsrec') roots e.
Proof.
move=> dfs1_is_correct dfs'_is_correct; rewrite /dfs'_correct /dfs'.
case: pickP => [x|no_roots]; last first.
  move=> [gto_roots e_wf e_gwf black_sccs]; split=> //.
    by apply/subsetP=> x; rewrite !inE no_roots.
  split=> //; first by split=> //; first by exists [::] => //; apply/subsetP.
  split=> //; first by move=> x; rewrite no_roots.
    by left.
  by move=> y; rewrite inE => /andP[_ /existsP [x /and3P[->]]].
move=> x_root; have := dfs'_is_correct _ x_root; rewrite /dfs'_correct.
case: ifPn=> [x_stack|xNstack].
  case: (dfsrec' _ _) => [m2 e'].
  move=> e'_correct [to_roots e_wf e_gwf Nbw black_sccs].
  have e_uniq := wf_stack_uniq e_wf.
  case: e'_correct; first exact: (pre_dfs_subroots (subD1set _ _)).
  move=> change_color [invariants monotony [pc1 pc2 pc3]].
  split=> //.
  - rewrite -(setD1K x_root) subUset change_color sub1set !inE.
    have [//|xNblack /=] := boolP (x \in blacks _).
    by have [[s ->]] := monotony; rewrite mem_cat x_stack orbT.
  split=> //; split=> //.
  - move=> y y_root; have [->|neq_yx]:= eqVneq y x; last first.
      by rewrite geq_min pc1 ?orbT // !inE neq_yx.
    by have [[s -> _ _ _]] := monotony; rewrite rank_catl // geq_min leqnn.
  - right; case: (leqP (rank x (stack e)) m2) => [rx_small|/ltnW rx_big].
      rewrite (minn_idPl _) //.
      exists x => //; exists x; rewrite ?inE ?connect0 //.
      by have [[s ->]] := monotony; rewrite rank_catl.
    rewrite (minn_idPr _) //.
    case: pc2 rx_big=> [->|[y]]; first by rewrite leqNgt rank_lt ?x_stack.
    rewrite !inE => /andP[neq_yx y_roots [z y_to_z m_def]].
    by move=> m_small; exists y => //; exists z.
  - by move=> y y_xedge; rewrite (@leq_trans m2) ?pc3 // geq_min leqnn orbT.
case: ifPn=> [x_black|xNblack] //=.
  case: (dfsrec' _ _) => [m2 e'].
  move=> e'_correct [to_roots e_wf e_gwf Nbw black_sccs].
  case: e'_correct; first exact: (pre_dfs_subroots (subD1set _ _)).
  move=> change_color [[e'_wf e'_gwf keep_gray Nbw' sccs'_black]
                       [mon1 mon2 mon3] [pc1 pc2 pc3]].
  have e'_uniq := wf_stack_uniq e'_wf.
  split=> //.
    by rewrite -(setD1K x_root) subUset change_color sub1set !inE (subsetP mon2).
  have m2_rank: m2 <= infty by case: pc2=> [->|[?? [??->]]]; rewrite ?rank_le.
  split=> //; split=> //.
  - move=> y y_root; have [->{y y_root}|neq_yx]:= eqVneq y x; last first.
      by rewrite geq_min pc1 ?orbT // !inE neq_yx.
    rewrite rank_infty ?geq_min ?leqnn // sccs_stackF //.
    by apply: (subsetP (subset_bigcup mon3)); case: colorP x_black xNstack.
  - rewrite (minn_idPr _) //; case: pc2 => [->//|]; first by left.
    by move=> [y]; rewrite !inE => /andP[_ ?]; right; exists y.
  - by move=> y y_xedge; rewrite (@leq_trans m2) ?pc3 // geq_min leqnn orbT.
have := dfs1_is_correct _ x_root; rewrite /dfs1_correct.
case: (dfs1 _ _) => [m1 e1]; case: (dfsrec' _ _) => [m2 e2].
move=> post_dfs1 post_dfs' pre {dfs1_is_correct dfs'_is_correct}.
have [e_access_to e_wf e_gwf Nbw sccs_black] := pre.
have e_uniq := wf_stack_uniq e_wf.
have x_white : x \in whites e by case: colorP xNstack xNblack.
have := post_dfs1 x_white (pre_dfs_subroots _ pre).
rewrite sub1set x_root => /(_ isT) {post_dfs1}.
case=> [x_black [[e1_wf e1_gwf Nbw1 keep_gray sccs_e1]
       [[s1 s1_def s1b] mo_b1 mo_sccs1] [pc1 pc2 pc3]]].
have e1_uniq := wf_stack_uniq e1_wf.
case: post_dfs'.
  split=> // y; rewrite !inE s1_def mem_cat.
  case: (y \in s1) (subsetP s1b y) => //= [->//|_ /andP[yNb ys]].
  move=> z; rewrite inE => /andP[_ z_roots]; rewrite e_access_to //.
  by rewrite !inE ys andbT; apply: contraNN yNb; apply/subsetP.
move=> rootsDx_subset [[e2_wf e2_gwf Nbw2 keep_gray2 sccs_e2]
  [[s2 s2_def s2b] mo_b2 mo_sccs2] [pc21 pc22 pc23]].
have e2_uniq := wf_stack_uniq e2_wf.
split.
  rewrite -(setD1K x_root) subUset rootsDx_subset andbT sub1set.
  by rewrite inE (subsetP mo_b2).
split; first by rewrite keep_gray2 keep_gray.
  split.
  + exists (s2 ++ s1); first by rewrite s2_def s1_def catA.
    apply/subsetP=> y; rewrite mem_cat => /orP [/(subsetP s2b) //|].
    by apply/subsetP/(subset_trans s1b).
  + exact/(subset_trans mo_b1).
  + exact/(subset_trans mo_sccs1).
have m1_rank: m1 <= infty by case: pc2=> [->|[?? [??->]]]; rewrite ?rank_le.
have m2_rank: m2 <= infty by case: pc22=> [->|[?? [??->]]]; rewrite ?rank_le.
split.
- move=> y y_roots; have [->|neq_yx] := eqVneq y x; last first.
    by rewrite (@leq_trans m2) ?geq_minr // pc21 // !inE neq_yx.
  have [xs|xNs] := boolP (x \in stack e1).
    by rewrite s2_def rank_catl // (@leq_trans m1) ?geq_minl // pc1 ?inE.
  have x_sccs2 : x \in cover (sccs e2).
    apply: (subsetP (subset_bigcup mo_sccs2)).
    by case: colorP xNs x_black.
  by rewrite rank_infty ?geq_min ?m1_rank //; case: colorP x_sccs2.
- case: pc22 => [->|m2_reachable].
  + rewrite (minn_idPl _) //; case: pc2=> [->|pc2]; [by left|].
    case: ltngtP m1_rank => // [m1_lt _|]; last by left.
    right; exists x => //.
    case: pc2=> z; rewrite inE => /eqP -> [t x_to_t m1_def].
    by exists t => //; rewrite s2_def rank_catl // -rank_lt -?m1_def.
  + case: (leqP m1 m2) => [m12|/ltnW m21]; last first.
      rewrite (minn_idPr _) //.
      case: m2_reachable => y; rewrite !inE => /andP[_ y_root] [z y_to_z m2_def].
      by right; exists y => //; exists z => //.
    rewrite (minn_idPl _) //.
    case: ltngtP m1_rank => // [m1_lt _|]; last by left.
    right; exists x => //; case: pc2=> [m1_infty|[z]].
      by rewrite m1_infty ltnn in m1_lt.
    rewrite inE => /eqP -> [t x_to_t m1_def].
    by exists t => //; rewrite s2_def rank_catl // -rank_lt -?m1_def.
- move=> y.
  rewrite !inE => /andP [y_s0 /existsP[z /and3P [z_s2 zNs0 z_to_y]]].
  move: z_s2; rewrite s2_def mem_cat orbC.
  have [z_s1 _|/= zNs1 z_s2] := boolP (z \in stack e1).
    rewrite rank_catl; last by rewrite s1_def mem_cat y_s0 orbT.
    rewrite (@leq_trans m1) ?geq_minl // pc3 // inE y_s0.
    by apply/existsP; exists z; rewrite z_s1 zNs0.
  rewrite -s2_def (@leq_trans m2) ?geq_minr // pc23 // inE.
  rewrite s1_def mem_cat y_s0 orbT /=.
  apply/existsP; exists z; rewrite s2_def mem_cat z_s2 /= [X in _ && X]z_to_y.
  by rewrite -s1_def zNs1.
Qed.

Definition is_subscc (A : {set V}) := A != set0 /\ {in A &, forall x y, gconnect x y}.

Lemma is_subscc_in_scc (A : {set V}) :
  is_subscc A -> exists2 scc, scc \in gsccs & A \subset scc.
Proof.
move=> []; have [->|[x xA]] := set_0Vmem A; first by rewrite eqxx.
move=> AN0 A_sub; exists (scc_of x).
  by rewrite pblock_mem ?(cover_partition gsccs_partition).
by apply/subsetP => y yA; rewrite mem_scc /= !A_sub //.
Qed.

Lemma is_subscc1 x (A : {set V}) : x \in A ->
  (forall y, y \in A -> gconnect x y /\ gconnect y x) -> is_subscc A.
Proof.
move=> xA AP; split; first by apply: contraTneq xA => ->; rewrite inE.
by move=> y z /AP [xy yx] /AP [xz zx]; rewrite (connect_trans yx).
Qed.

Lemma rank_mem x s : x \in s -> rank x s < size s.
Proof. by move=> x_s; rewrite rankE x_s -size_rev index_mem mem_rev. Qed.

Lemma rank_le_head s z x : x \notin s -> z \in s ->
  rank z (x :: s) < rank x (x :: s).
Proof.
by move=> xNs z_s; rewrite !rank_cons z_s andbF eqxx xNs /= rank_mem.
Qed.


Lemma path_xset_xedge x y (s : pred V) :
  gconnect x y -> x \in s -> y \notin s ->
  exists x' y', [/\ x' \in s, y' \notin s,
                    gconnect x x', edge x' y' & gconnect y' y].
Proof.
move=> /connectP [p path_xp ->] xs yNs.
pose n := find (predC s) p.
have hasNs_p : has (predC s) p.
  apply/hasP; exists (last x p) => //=.
  have := mem_last x p; rewrite in_cons => /predU1P [eq_x|//].
  by rewrite eq_x xs in yNs.
have n_small : n < size p by rewrite -has_find.
exists (nth x (x :: p) n), (nth x p n).
rewrite [_ \notin s](@nth_find _ _ (predC s)) ?(pathP _ _) //.
have [->|n_gt0] := posnP n.
  rewrite ?nth0 /= xs connect0; split=> //.
  case: p {yNs n hasNs_p n_small} path_xp => //= z p.
  by move=> /andP [xz zp]; rewrite (appP connectP idP) //; exists p.
rewrite -{1 2}[n]prednK //= -[_ \in s]negbK.
rewrite [_ \notin s](@before_find _ _ (predC s)) ?prednK //=.
split=> //; apply/connectP.
  exists (take n p).
    by move: path_xp; rewrite -{1}[p](@cat_take_drop n) cat_path=> /andP[].
  rewrite (last_nth x) size_take n_small.
  by case: (n) n_gt0 => //= k _; rewrite nth_take.
exists (drop n.+1 p).
  move: path_xp; rewrite -{1}[p](@cat_take_drop n.+1) cat_path=> /andP[_].
  rewrite (last_nth x) /= size_take ltn_neqAle n_small andbT.
   by have [->|] := altP eqP; rewrite /= ?drop_size ?nth_take.
rewrite !(last_nth x) size_drop.
move: n_small; rewrite leq_eqVlt => /predU1P[<-|]; rewrite ?subnn //.
case: (size p) => //= - [|k] //; rewrite !ltnS => n_small.
by rewrite subSS subSn // [RHS]/= nth_drop addSn subnKC.
Qed.

Lemma grays_add_blacks e x : grays (add_blacks x e) = grays e :\ x.
Proof. by apply/setP=> y; rewrite !inE /= negb_or andbA. Qed.

Lemma whites_add_blacks e x : whites (add_blacks x e) = whites e :\ x.
Proof.
by apply/setP=> y; rewrite !inE; case: (_ == _) (_ \in _) (_ \in _) => [] [].
Qed.

Lemma grays_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  uniq (stack e) -> s \subset blacks e -> x \in grays e ->
  grays (add_sccs x e) = grays e :\ x.
Proof.
move=> /= se_uniq sb x_gray; rewrite /add_sccs /grays /=.
case: splitP sb se_uniq; first by rewrite grays_stack.
move=> s s' sb sxs'_uniq.
apply/setP=> y; rewrite !inE mem_cat mem_rcons in_cons.
have [->|] //= := altP eqP; rewrite orbC ![(y \notin _) && _]andbC.
have [|yNs' neq_yx] //= := boolP (y \in s').
by have [y_s|] //= := boolP (y \in s); rewrite (subsetP sb).
Qed.

Lemma whites_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  x \in grays e -> uniq (stack e) -> s \subset blacks e ->
  whites (add_sccs x e) = whites e.
Proof.
move=> /= x_gray se_uniq sb; rewrite /whites grays_add_sccs //=.
by rewrite setUCA setUA setD1K.
Qed.

Lemma blacks_add_sccs e x : blacks (add_sccs x e) = x |: blacks e.
Proof. by []. Qed.

Lemma sccs_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  sccs (add_sccs x e) = [set y in rcons s x] |: sccs e.
Proof. by []. Qed.

Lemma stack_add_sccs e x :
  let s := drop (index x (stack e)).+1 (stack e) in
  stack (add_sccs x e) = s.
Proof. by []. Qed.

Lemma dfs1_is_correct dfs' (x : V) e :
  (dfs'_correct dfs' [set y in successors x] (add_stack x e)) ->
  dfs1_correct (dfs1 dfs') x e.
Proof.
rewrite /dfs1 /dfs1_correct /dfs'_correct; case: (dfs' _ _) => m1 e1.
move=> post_dfs'; set m := rank x _.
move=> x_white [access_to_x e_wf e_gwf Nbw black_sccs].
have e_uniq := wf_stack_uniq e_wf.
case: post_dfs' => //=.
  split => //; do?[exact: add_stack_ewf|exact: add_stack_gwf]; last first.
     move=> y /Nbw; rewrite whites_add_stack.
     rewrite ![[disjoint successors _ & _]]disjoint_sym.
     by apply/disjoint_trans/subsetDl.
  move=> y; rewrite grays_add_stack // => /setU1P [->|]; last first.
    move=> y_gray z; rewrite inE => /(@connect1 _ edge).
    by apply/connect_trans/access_to_x; rewrite ?set11.
  by move=> z; rewrite inE => /(@connect1 _ edge).
move=> succ_bVg [[e1_wf e1_gwf Nbw1 keep_gray black_sccs1]
                   [[s/= s_def sb] mo_b mo_sccs] [pc1 pc2 pc3]].
set s2 := rcons s x.
have e1_uniq := wf_stack_uniq e1_wf.
have xe_uniq : uniq (x :: stack e).
  by have := e1_uniq; rewrite s_def cat_uniq => /and3P [].
have x_stack : x \in stack e1 by rewrite s_def mem_cat mem_head orbT.
have x_grays : x \in grays e1 by rewrite keep_gray grays_add_stack ?setU11.
have sx_subscc : is_subscc [set y in rcons s x].
  apply: (@is_subscc1 x); first by rewrite inE mem_rcons mem_head.
  move=> y; rewrite !inE mem_rcons in_cons => /predU1P [->//|y_s]; split.
    apply: (@wf_grays_to_stack e1) => //; first by rewrite s_def mem_cat y_s.
    rewrite s_def rank_catl ?mem_head // rank_catr //=; last first.
       by rewrite -(@uniq_catLR _ _ s) ?mem_cat ?y_s // -?s_def //.
    rewrite rankE mem_head (leq_trans (index_size _ _)) //.
    by rewrite size_rev leq_addr.
  have [] := @wf_stack_to_grays _ e1_gwf y; first by rewrite s_def mem_cat y_s.
  move=> z [z_gray rank_z] /connect_trans; apply.
  rewrite (@wf_grays_to_stack e1) // s_def.
  have := z_gray; rewrite !(inE, s_def) mem_cat.
  case: (boolP (z \in s)) => [/(subsetP sb)->//|_ /= /andP [_ z_xe]].
  rewrite !rank_catl ?mem_head //.
  move: z_xe; rewrite in_cons.
  have [->//|neq_zx /= z_s] := altP eqP.
  rewrite ltnW // rank_le_head //.
  rewrite -(@uniq_catLR _ _ (rcons s x)) ?mem_rcons ?mem_head //.
    by rewrite cat_rcons -s_def wf_stack_uniq.
  by rewrite mem_cat mem_rcons mem_head.
case: ltnP => [m1_small|m1_big] //=; rewrite !inE eqxx /=; split=> //.
  have [x1 rank_x1 x_to_x1] : exists2 x1,
    rank x1 (stack e1) = m1 & gconnect x x1.
    case: pc2 m1_small => [->|]; first by rewrite /m ltnNge ?rank_le.
    move=> [y]; rewrite inE => /(@connect1 _ edge) x_to_y.
    move=> [x1 y_to_x1 rank_x1 _]; exists x1 => //.
    by rewrite (connect_trans x_to_y).
  have [x' [rank_x' x'_gray x_to_x' ]] : exists x',
    [/\ rank x' (stack e1) < rank x (stack e1), x' \in grays e1 & gconnect x x'].
    move: m1_small; rewrite -{}rank_x1 => rank_x1.
    have x1_stack : x1 \in stack e1.
      by rewrite -rank_lt ?(leq_trans rank_x1) // rank_le.
    have [z [z_gray rank_z y_to_z]] := wf_stack_to_grays e1_gwf x1_stack.
    exists z; split=> //; rewrite 2?inE ?z_gray ?andbT.
    - rewrite (leq_ltn_trans rank_z) // (leq_trans rank_x1) // /m.
      by rewrite s_def rank_catl ?mem_head.
    - by rewrite (connect_trans x_to_x1).
  have neq_x'x : x' != x by apply: contraTneq rank_x' => ->; rewrite -ltnNge.
  split=> //.
  - split=> //; first exact: add_blacks_ewf.
    + split => //.
        move=> y z /=; rewrite grays_add_blacks => y_gray z_stack.
        apply: wf_grays_to_stack => //; apply: subsetP y_gray.
        by rewrite subD1set.
      move=> y /= y_stack; rewrite grays_add_blacks.
      have [z] // := wf_stack_to_grays e1_gwf y_stack.
      have [->{z} [_ rank_x y_to_x]|] := eqVneq z x; last first.
        move=> neq_zx [z_gray rank_z y_to_z].
        by exists z; split=> //; rewrite 2!inE neq_zx.
      exists x'; split; rewrite 2?inE ?x'_gray ?andbT //.
      - by rewrite (leq_trans _ rank_x) 1?ltnW // {2}s_def rank_catl ?mem_head.
      - by rewrite (connect_trans y_to_x).
    + move=> y; rewrite !inE whites_add_blacks.
      move=> /predU1P [->{y}|y_black]; last first.
        apply/pred0P=> z /=; rewrite 2!inE.
        have /pred0P /(_ z) /= := Nbw1 _ y_black.
        by apply: contraFF=> /and3P[->_->].
      apply/pred0P=> z /=; rewrite 2!inE.
      have /subsetP /(_ z) := succ_bVg.
      rewrite 2!inE => /implyP.
      by case: (_ \in successors _) (_ == _) colorP => [] [] [].
    + rewrite grays_add_blacks keep_gray grays_add_stack //.
      by rewrite setU1K // whites_graysF.
    + rewrite /= black_sccs1; apply/setP=> scc; rewrite !inE /=.
      have [scc_gsccs|] //= := boolP (scc \in gsccs).
      apply/idP/idP; first by move=> /subset_trans; apply; rewrite subsetU1.
      move=> /subsetP scc_sub; apply/subsetP => y y_scc.
      have /setU1P [eq_yx|//] := scc_sub y y_scc.
      rewrite eq_yx in y_scc.
      have x'_scc : (x' \in scc).
        rewrite -(def_scc _ y_scc) // mem_scc /= x_to_x' /=.
        by rewrite (wf_grays_to_stack e1_gwf) // ltnW.
      have /scc_sub := x'_scc.
      rewrite !inE (negPf neq_x'x) /=.
      by case: colorP x'_gray.
  - split=> //=.
    + exists (rcons s x); first by rewrite cat_rcons.
      apply/subsetP=> y; rewrite !inE mem_rcons in_cons=> /predU1P [->|].
        by rewrite eqxx.
      by move=> y_s; rewrite (subsetP sb) ?orbT.
    + by rewrite subsetU // mo_b orbT.
  - split=> //=.
    + move=> y; rewrite inE => /eqP->.
      by rewrite s_def rank_catl ?mem_head // ltnW.
    + by right; exists x; rewrite ?set11 //; exists x1.
    + move=> y; rewrite inE => /andP [y_stack /existsP].
      move=> [z /and3P[z_stack1 zNstack zy]].
      have [eq_zx|neq_zx] := eqVneq z x.
        by rewrite pc1 // -eq_zx inE.
      apply: pc3; rewrite inE in_cons y_stack orbT /=.
      apply/existsP; exists z.
      by rewrite z_stack1 in_cons negb_or neq_zx zNstack.
have scc_max : scc_of x \subset [set y in s2].
  apply/subsetP=> y; rewrite inE=> y_sccx; apply: contraTT isT => yNs2.
  have xy : gconnect x y.
    by have := y_sccx; rewrite mem_scc /= => /andP[].
  have x_s2 : x \in s2 by rewrite mem_rcons mem_head.
  have [x' [y' [x'_s2 y'Ns xx' x'y' y'y]]] := path_xset_xedge xy x_s2 yNs2.
  apply: contraNN y'Ns => _.
  have: y' \in ([set y in stack e1] :|:
               (\bigcup_(scc in sccs e1) scc :|: whites e1)).
    by rewrite !inE; case: colorP.
  rewrite 3!inE => /or3P[].
  - rewrite s_def -cat_rcons mem_cat => /orP[//|y'_stack].
    have xNstack: x \notin stack e.
      rewrite -(@uniq_catLR _ x s2) ?mem_cat ?x_s2 //.
      by rewrite cat_rcons -s_def wf_stack_uniq.
    have x'Nstack: x' \notin stack e.
      rewrite -(@uniq_catLR _ x' s2) ?mem_cat ?x'_s2 //.
      by rewrite cat_rcons -s_def wf_stack_uniq.
    have rank_y': rank y' (x :: stack e) < rank x (x :: stack e).
      by rewrite rank_le_head //.
    have neq_y'x : y' != x by apply: contraTneq rank_y' => ->; rewrite ltnn.
    have [eq_x'x|neq_x'x] := eqVneq x' x.
      have := pc1 y'; rewrite inE -eq_x'x => /(_ x'y').
      rewrite leqNgt (leq_trans _ m1_big) // /m.
      by rewrite s_def rank_catl ?in_cons ?y'_stack ?orbT.
    apply: contraTT rank_y' => y'Ns2; rewrite -leqNgt.
    rewrite [rank y' _]rank_cons (negPf neq_y'x) /=.
    have := pc3 y'; rewrite inE in_cons y'_stack orbT /=.
    rewrite {2}s_def -cat_rcons rank_catl // => /(_ _) /(leq_trans _) -> //.
    apply/existsP; exists x'; rewrite s_def -cat_rcons mem_cat x'_s2 /=.
    by rewrite in_cons (negPf neq_x'x) /= x'Nstack.
  - move=> /bigcupP [scc'].
    rewrite black_sccs1 inE => /andP[scc'_gsccs scc'_black].
    move=> /def_scc - /(_ scc'_gsccs) eq_scc'; rewrite -eq_scc' in scc'_black.
    have : x \in scc_of y'.
      have:= y_sccx; rewrite !mem_scc /= andbC => /andP[yx _].
      by rewrite (connect_trans y'y) //= (connect_trans xx') //= connect1.
    by move=> /(subsetP scc'_black); case: colorP x_grays.
  - move: x'_s2; rewrite mem_rcons in_cons => /predU1P [eq_x'x|x_s].
      have /subsetP /(_ y') := succ_bVg.
      by rewrite 2!inE -eq_x'x => /(_ x'y'); case: colorP.
    have /(_ x') := Nbw1; rewrite (subsetP sb) => // /(_ isT).
    by move=> /pred0P /(_ y') /=; rewrite [_ \in _]x'y' /= => ->.
have take_s : take (index x (stack e1)) (stack e1) = s.
  rewrite s_def index_cat /= eqxx addn0.
  rewrite (@uniq_catLR _ _ _ (x :: stack e)) -?s_def ?wf_stack_uniq //.
  by rewrite mem_head /= ?s_def take_cat ltnn subnn take0 cats0.
have drop_s : drop (index x (stack e1)).+1 (stack e1) = stack e.
  rewrite s_def index_cat /= eqxx addn0.
  rewrite (@uniq_catLR _ _ _ (x :: stack e)) -?s_def ?wf_stack_uniq //.
  rewrite mem_head /= ?s_def drop_cat ltnNge leqW //.
  by rewrite subSn // subnn //= drop0.
have g1Nx : grays e1 :\ x = grays e.
  by rewrite keep_gray grays_add_stack // setU1K // whites_graysF.
split=> //.
- split=> //.
  + by apply: add_sccs_wf=> //; rewrite take_s //.
  + split=> //; rewrite ?grays_add_sccs ?stack_add_sccs ?take_s ?drop_s// ?g1Nx.
      exact: wf_grays_to_stack.
      exact: wf_stack_to_grays.
  + move=> y; rewrite !inE whites_add_sccs ?take_s //.
    move=> /predU1P [->|/Nbw1//]; apply/pred0P=> z //=.
    rewrite 2!inE; have /subsetP /(_ z) := succ_bVg.
    by rewrite 2!inE => /implyP; rewrite -negb_imply orbC => ->.
  + by rewrite grays_add_sccs ?take_s ?g1Nx.
  + rewrite sccs_add_sccs take_s //=; apply/setP=> scc.
    rewrite !inE blacks_add_sccs ?take_s//= black_sccs1 !inE.
    have x_s2 : x \in [set y in s2] by rewrite inE mem_rcons mem_head.
    have s2_gsccs : [set y in rcons s x] \in gsccs.
       apply/imsetP => /=; exists x => //.
      rewrite -[RHS](@def_scc _ x); last 2 first.
      * by apply/imsetP; exists x.
      * by rewrite !inE ?connect0.
      apply/eqP; rewrite eqEsubset scc_max.
      have [scc' scc'_gsccs sub'] := is_subscc_in_scc sx_subscc.
      by rewrite (@def_scc scc') ?sub' //; apply: (subsetP sub').
    have [scc_gsccs|] //= := boolP (scc \in gsccs); last first.
      by apply: contraNF; rewrite orbF => /eqP->.
    apply/idP/idP.
      move=> /predU1P [->|].
        apply/subsetP => y; rewrite !inE mem_rcons in_cons.
        by case: eqP=> [->|] //= _ => /(subsetP sb).
      by move=> /subset_trans; apply; rewrite subsetU1.
    have [x_scc|xNscc] := boolP (x \in scc).
      by move=> _; rewrite -(def_scc _ x_scc) // (def_scc s2_gsccs) ?eqxx.
    rewrite -subDset (setDidPl _); first by move->; rewrite orbT.
    by rewrite disjoint_sym (@eq_disjoint1 _ x) // => y; rewrite !inE.
- split=> //.
  + rewrite stack_add_sccs drop_s; exists [::] => //.
    by apply/subsetP=> y; rewrite inE.
  + by rewrite blacks_add_sccs ?take_s// (subset_trans mo_b) ?subsetU1.
  + by rewrite sccs_add_sccs take_s (subset_trans mo_sccs) ?subsetU1.
- split=> //; do ?by [left].
  + move=> y; rewrite inE => /eqP->.
    by rewrite stack_add_sccs drop_s leqNgt rank_lt ?whites_stackF.
  + move=> y; rewrite inE stack_add_sccs drop_s => /andP[_ /existsP].
    by move=> [z /and3P[->]].
Qed.


(* Theorem tarjan_terminates e roots n: n >= #|whites e| * #|V| + #|roots| -> *)
(*   tarjan n roots e = (infty, Env setT [::] gsccs). *)
(* Proof. *)

Theorem tarjan_is_correct : forall n, n >= #|V| * #|V| + #|V| ->
  tarjan n setT (Env set0 [::] set0) = (infty, Env setT [::] gsccs).
Proof.
move=> n n_geV.
elim: n n_geV => /= [|n IHn].
  rewrite leqn0 -cardsT cards_eq0 => /eqP V_eq0; rewrite V_eq0.
(*   suff -> : sccs = set0 by []. *)
(*   apply: contraTeq isT => /set0Pn [x] /imsetP [i]. *)
(*   by have := in_setT i; rewrite V_eq0 inE. *)
(* move=> Sn_geV; rewrite /dfs'. *)
(* have [x xV /=|/= ?] := pickP; last first. *)
(*   admit. *)
Abort.

End tarjan.
