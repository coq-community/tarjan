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

Definition scc_of x := [set y in V | gconnect x y && gconnect y x].
Definition gsccs := [set scc_of x | x in V].

Lemma mem_scc x (scc : {set V}) : scc \in gsccs -> x \in scc -> scc = scc_of x.
Proof.
move=> /imsetP [y _ ->]; rewrite inE => /and3P [_ yx xy].
gen have sub_ssc_of : x y yx xy / scc_of y \subset scc_of x.
   apply/subsetP=> z; rewrite !inE /= => /andP [yz zy].
   by rewrite (connect_trans xy) // (connect_trans zy).
by apply/eqP; rewrite eqEsubset !sub_ssc_of.
Qed.

Inductive wf_env e := WfEnv {
   wf_stack : [set x in stack e] =
              grays e :|: (blacks e :\: \bigcup_(scc in sccs e) scc);
   wf_sccs : \bigcup_(scc in sccs e) scc \subset blacks e;
   wf_stack_uniq : uniq (stack e)
}.

Inductive color_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| ColorGray of x \in grays e : color_spec x e false true false true false
| ColorSccs of x \in \bigcup_(scc in sccs e) scc :
                       color_spec x e true false true false false
| ColorWhite of x \in whites e : color_spec x e false false false false true
| ColorBlackStack of x \in blacks e & x \in stack e :
                        color_spec x e true true false false false.

Lemma colorP x e : wf_env e ->
                   color_spec x e (x \in blacks e) (x \in stack e)
                              (x \in \bigcup_(scc in sccs e) scc)
                              (x \in grays e) (x \in whites e).
Proof.
move=> [/setP /(_ x) s_def] /subsetP /(_ x) /implyP.
move: s_def; rewrite /grays /whites !inE.
case x_black: (_ \in blacks _) => /=;
case x_stack : (_ \in stack _) => /=;
case x_sccs : (_ \in \bigcup_(_ in _) _) => //=; do ?by constructor.
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
   x \in \bigcup_(scc in sccs e) scc = false.
Proof. by case/colorP. Qed.

Lemma sccs_stackF x e : wf_env e ->
  x \in \bigcup_(scc in sccs e) scc -> x \in stack e = false.
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
  rewrite bigcup_setU inE big_set1 !inE /= => /orP[|/sccs_blacks->];
    last by rewrite !orbT.
  by rewrite mem_rcons !inE; case: eqP => //= _ /new_blacks.
apply/setP=> y; rewrite !inE bigcup_setU inE big_set1 !inE !negb_or.
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

Lemma rank_le x (s : seq V) : rank x s <= infty.
Admitted.
Hint Resolve rank_le.

Lemma rank_lt x (s : seq V) : (rank x s < infty) = (x \in s).
Admitted.
Hint Resolve rank_lt.

Lemma rank_infty x (s : seq V) : x \notin s -> rank x s = infty.
Admitted.

Lemma subset_bigcup (sccs sccs' : {set {set V}}) :
  sccs \subset sccs' ->
  \bigcup_(scc in sccs) scc \subset \bigcup_(scc in sccs') scc.
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
    case: pc2 rx_big=> [->|[y]]; first by rewrite leqNgt rank_lt x_stack.
    rewrite !inE => /andP[neq_yx y_roots [z y_to_z m_def]].
    by move=> m_small; exists y => //; exists z.
  - by move=> y y_xedge; rewrite (@leq_trans m2) ?pc3 // geq_min leqnn orbT.
case: ifPn=> [x_black|xNblack] //=.
  case: (dfsrec' _ _) => [m2 e'].
  move=> e'_correct [to_roots e_wf e_gwf Nbw black_sccs].
  case: e'_correct; first exact: (pre_dfs_subroots (subD1set _ _)).
  move=> change_color [[e'_wf e'_gwf keep_gray Nbw' sccs'_black]
                       [mon1 mon2 mon3] [pc1 pc2 pc3]].
  split=> //.
    by rewrite -(setD1K x_root) subUset change_color sub1set !inE (subsetP mon2).
  have m2_rank: m2 <= infty by case: pc2=> [->|[?? [??->]]].
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
have x_white : x \in whites e by case: colorP xNstack xNblack.
have := post_dfs1 x_white (pre_dfs_subroots _ pre).
rewrite sub1set x_root => /(_ isT) {post_dfs1}.
case=> [x_black [[e1_wf e1_gwf Nbw1 keep_gray sccs_e1]
       [[s1 s1_def s1b] mo_b1 mo_sccs1] [pc1 pc2 pc3]]].
case: post_dfs'.
  split=> // y; rewrite !inE s1_def mem_cat.
  case: (y \in s1) (subsetP s1b y) => //= [->//|_ /andP[yNb ys]].
  move=> z; rewrite inE => /andP[_ z_roots]; rewrite e_access_to //.
  by rewrite !inE ys andbT; apply: contraNN yNb; apply/subsetP.
move=> rootsDx_subset [[e2_wf e2_gwf Nbw2 keep_gray2 sccs_e2]
  [[s2 s2_def s2b] mo_b2 mo_sccs2] [pc21 pc22 pc23]].
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
have m1_rank: m1 <= infty by case: pc2=> [->|[?? [??->]]].
have m2_rank: m2 <= infty by case: pc22=> [->|[?? [??->]]].
split.
- move=> y y_roots; have [->|neq_yx] := eqVneq y x; last first.
    by rewrite (@leq_trans m2) ?geq_minr // pc21 // !inE neq_yx.
  have [xs|xNs] := boolP (x \in stack e1).
    by rewrite s2_def rank_catl // (@leq_trans m1) ?geq_minl // pc1 ?inE.
  have x_sccs2 : x \in \bigcup_(scc in sccs e2) scc.
    apply: (subsetP (subset_bigcup mo_sccs2)).
    by case: colorP xNs x_black.
  by rewrite rank_infty ?geq_min ?m1_rank //; case: colorP x_sccs2.
- case: pc22 => [->|m2_reachable].
  + rewrite (minn_idPl _) //; case: pc2=> [->|pc2]; [by left|].
    case: ltngtP m1_rank => // [m1_lt _|]; last by left.
    right; exists x => //.
    case: pc2=> z; rewrite inE => /eqP -> [t x_to_t m1_def].
    by exists t => //; rewrite s2_def rank_catl // -rank_lt -m1_def.
  + case: (leqP m1 m2) => [m12|/ltnW m21]; last first.
      rewrite (minn_idPr _) //.
      case: m2_reachable => y; rewrite !inE => /andP[_ y_root] [z y_to_z m2_def].
      by right; exists y => //; exists z => //.
    rewrite (minn_idPl _) //.
    case: ltngtP m1_rank => // [m1_lt _|]; last by left.
    right; exists x => //; case: pc2=> [m1_infty|[z]].
      by rewrite m1_infty ltnn in m1_lt.
    rewrite inE => /eqP -> [t x_to_t m1_def].
    by exists t => //; rewrite s2_def rank_catl // -rank_lt -m1_def.
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

Definition is_subscc (A : {set V}) := {in A &, forall x y, gconnect x y}.

Lemma is_subscc1 x (A : {set V}) : x \in A ->
  (forall y, y \in A -> gconnect x y /\ gconnect y x) -> is_subscc A.
Admitted.

Lemma rank_in x s : x \in s -> rank x s <= size s.
Proof.
by move=> x_s; rewrite rankE x_s (leq_trans (index_size _ _)) ?size_rev.
Qed.

(* Lemma add_black_gwf e x : x \in grays e -> *)
(*   wf_env e -> wf_graph e -> wf_graph (add_blacks x e). *)
(* Proof. *)
(* move=> x_gray e_wf e_gwf; split. *)
(* - move=> y; rewrite !inE => /predU1P [|y_black]; last first. *)

Lemma grays_add_blacks e x : grays (add_blacks x e) = grays e :\ x.
Proof. by apply/setP=> y; rewrite !inE /= negb_or andbA. Qed.

Lemma whites_add_blacks e x : whites (add_blacks x e) = whites e :\ x.
Proof.
by apply/setP=> y; rewrite !inE; case: (_ == _) (_ \in _) (_ \in _) => [] [].
Qed.

Lemma dfs1_is_correct dfs' (x : V) e :
  (dfs'_correct dfs' [set y in successors x] (add_stack x e)) ->
  dfs1_correct (dfs1 dfs') x e.
Proof.
rewrite /dfs1 /dfs1_correct /dfs'_correct; case: (dfs' _ _) => m1 e1.
move=> post_dfs'; set m := rank x _.
move=> x_white [access_to_x e_wf e_gwf Nbw black_sccs].
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
have x_stack : x \in stack e1 by rewrite s_def mem_cat mem_head orbT.
have x_grays : x \in grays e1 by rewrite keep_gray grays_add_stack ?setU11.
have sx_subscc : is_subscc [set y in rcons s x].
  apply: (@is_subscc1 x); first by rewrite inE mem_rcons mem_head.
  move=> y; rewrite !inE mem_rcons in_cons => /predU1P [->//|y_s]; split.
    apply: (@wf_grays_to_stack e1) => //; first by rewrite s_def mem_cat y_s.
    rewrite s_def rank_catl ?mem_head // rank_catr //=; last first.
       by rewrite -(@uniq_catLR _ _ s) ?mem_cat ?y_s // -?s_def wf_stack_uniq.
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
  rewrite !rank_cons eqxx (negPf neq_zx) /= (leq_trans (rank_in _)) //.
  rewrite -(@uniq_catLR _ _ (rcons s x)) ?mem_rcons ?mem_head //.
    by rewrite cat_rcons -s_def wf_stack_uniq.
  by rewrite mem_cat mem_rcons mem_head.
case: ltnP => [m1_small|m1_big] //=; rewrite !inE eqxx /=; split=> //.
  have [x1 rank_x1 x_to_x1] : exists2 x1,
    rank x1 (stack e1) = m1 & gconnect x x1.
    case: pc2 m1_small => [->|]; first by rewrite /m ltnNge rank_le.
    move=> [y]; rewrite inE => /(@connect1 _ edge) x_to_y.
    move=> [x1 y_to_x1 rank_x1 _]; exists x1 => //.
    by rewrite (connect_trans x_to_y).
  have [x' [rank_x' x'_gray x_to_x' ]] : exists x',
    [/\ rank x' (stack e1) < rank x (stack e1), x' \in grays e1 & gconnect x x'].
    move: m1_small; rewrite -{}rank_x1 => rank_x1.
    have x1_stack : x1 \in stack e1.
      by rewrite -rank_lt (leq_trans rank_x1) // rank_le.
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
        rewrite (mem_scc _ y_scc) // inE /= x_to_x' /=.
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
split=> //.
- split=> //.
  + apply: add_sccs_wf=> //.
    have : uniq (stack e1) by apply: wf_stack_uniq.
    rewrite s_def => uniq_s1; rewrite index_cat.
    rewrite (uniq_catLR uniq_s1) ?mem_cat ?mem_head ?orbT //= eqxx addn0.
    by rewrite take_cat ltnn subnn take0 cats0.
  +

Abort.


(* Definition wf_stack e := *)
(*   [/\ wf_color e, *)
(*       uniq (stack e), *)
(*       forall x, x \in grays e -> forall y, y \in stack e -> *)
(*           (rank x (stack e) <= rank y (stack e)) -> gconnect x y & *)
(*       forall y, y \in stack e -> exists2 x, x \in grays e & *)
(*           (rank x (stack e) <= rank y (stack e)) && gconnect y x *)
(*   ]. *)




(* Lemma dfs1_is_correct (dfs' : {set V} -> env -> nat * env) (x : V) e : *)
(*   (dfs'_correct dfs' [set y in successors x] (add_stack x e)) -> *)
(*   dfs1_correct (dfs1 dfs') x e. *)
(* Proof. *)
(* rewrite /dfs1_correct /dfs1 /=. *)
(* rewrite /dfs'_correct. *)
(* case: (dfs' _ _) => m e' /= dfs_is_correct. *)
(* case: leqP => [rank_small|rank_big] /=; case: e' => b' s' sccs' in dfs_is_correct *. *)
(*   move=> x_white []; split. *)
(*   - split. *)
(*     + split. *)
(*       * *)
(* Admitted. *)


Theorem tarjan_is_correct : forall n, n >= #|V| ->
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
