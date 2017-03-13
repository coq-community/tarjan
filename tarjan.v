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

Lemma rank_cat x s s' : x \in s' -> rank x (s ++ s') = rank x s'.
Proof.
by move=> x_s; rewrite !rankE rev_cat mem_cat x_s orbT index_cat mem_rev x_s.
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

Definition gsccs := [set [set y in V | gconnect x y && gconnect y x] | x in V].


Definition wf_env e :=
  [/\ [set x in stack e] = grays e :|: (blacks e :\: \bigcup_(scc in sccs e) scc),
   \bigcup_(scc in sccs e) scc \subset blacks e &
   uniq (stack e)].

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

Lemma grays_sccsF x e : wf_env e -> x \in grays e -> x \in \bigcup_(scc in sccs e) scc = false.
Proof. by move=> /colorP []. Qed.

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

Lemma wf_stack_uniq e : wf_env e -> uniq (stack e).
Proof. by case. Qed.
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

Definition wf_graph e :=
  [/\ noblack_to_white e,
   forall x, x \in grays e -> forall y, y \in stack e ->
     (rank x (stack e) <= rank y (stack e)) -> gconnect x y &
   forall y, y \in stack e -> exists x, [/\ x \in grays e,
     (rank x (stack e) <= rank y (stack e)) & gconnect y x]
  ].

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

Definition pre_dfs (roots : {set V}) (e : env) :=
  [/\ access_to e roots, wf_env e, wf_graph e & sccs e = black_gsccs e].

Lemma add_stack_gwf e w : 
  access_to e [set w] -> wf_env e -> w \in whites e -> wf_graph e -> 
  wf_graph (add_stack w e).
Proof.
move=> grays_to e_wf w_white [Nbw gs sg]; split.
- move=> y /Nbw; rewrite whites_add_stack.
  rewrite ![[disjoint successors _ & _]]disjoint_sym.
  by apply/disjoint_trans/subsetDl.
- rewrite grays_add_stack //= => x; rewrite rank_cons !inE.
  move=> /orP[/eqP->|/andP[xNb xs]] y; rewrite in_cons=> /orP[/eqP->|/=ys];
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
[/\ [/\ wf_env e', wf_graph e' & (sccs e' = black_gsccs e')],

   [/\ 
    exists2 s, stack e' = s ++ stack e & s \subset (blacks e'),
    (* exists x, let: (new, old) := split_after x (stack e') in *)
    (*       (old == stack e) /\ (new \subset blacks e'), *)
    blacks e \subset blacks e'  & sccs e \subset sccs e' ]&

   [/\
    (* roots :&: whites e \subset blacks e', *)
    (* roots \subset blacks e' :|: grays e', *)
    forall x, x \in roots -> m <= rank x (stack e'),
    m = infty \/ exists2 x, x \in roots & rank_of_reachable m x (stack e') &
    forall y, y \in xedges (stack e') (stack e) -> m <= rank y (stack e')
   ]
  ].

Definition dfs1_correct (dfs1 : V -> env -> nat * env) x e :=
  let (m, e') := dfs1 x e in 
  (x \in whites e) -> pre_dfs [set x] e ->
  post_dfs [set x] e e' m.

Definition dfs'_correct (dfs' : {set V} -> env -> nat * env) roots e :=
  let (m, e') := dfs' roots e in
  pre_dfs roots e ->
  (roots \subset blacks e' :|: grays e') /\ post_dfs roots e e' m.

Lemma pre_dfs'_rootsD1 roots z e : pre_dfs roots e -> pre_dfs (roots :\ z) e.
Proof.
move=> [to_roots e_wf e_gwf black_sccs]; split=> //.
by move=> x x_gray y; rewrite inE => /andP[??]; rewrite to_roots.
Qed.

Lemma rank_le x (s : seq V) : rank x s <= infty.
Admitted.
Hint Resolve rank_le.

Lemma rank_lt x (s : seq V) : x \in s -> rank x s < infty.
Admitted.
Hint Resolve rank_lt.

Lemma rank_infty x (s : seq V) : x \notin s -> rank x s = infty.
Admitted.

Lemma dfs'_is_correct dfs1 dfsrec' (roots : {set V}) e :
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots -> dfs'_correct dfsrec' (roots :\ x) e) ->
  dfs'_correct (dfs' dfs1 dfsrec') roots e.
Proof.
move=> dfs1_is_correct dfs'_is_correct; rewrite /dfs'_correct /dfs'.
case: pickP => [x|no_roots]; last first.
  move=> [gto_roots e_wf e_gwf black_sccs]; split.
    by apply/subsetP=> x; rewrite !inE no_roots.
  split=> //; first by split=> //; first by exists [::] => //; apply/subsetP.
  split=> //; first by move=> x; rewrite no_roots.
    by left.
  by move=> y; rewrite inE => /andP[_ /existsP [x /and3P[->]]].
move=> x_root; case: ifPn=> [x_stack|xNstack].
  have := dfs'_is_correct _ x_root.
  rewrite /dfs'_correct; case: (dfsrec' _ _) => [m2 e'].
  move=> e'_correct [to_roots e_wf e_gwf black_sccs].
  case: e'_correct; first exact: pre_dfs'_rootsD1.
  move=> change_color [invariants monotony [pc1 pc2 pc3]].
  split=> //.
    rewrite -(setD1K x_root) subUset change_color sub1set !inE.
    have [//|xNblack /=] := boolP (x \in blacks _).
    by have [[s ->]] := monotony; rewrite mem_cat x_stack orbT.
  split=> //; split=> //.
  - move=> y y_root; have [->|neq_yx]:= eqVneq y x; last first.
      by rewrite geq_min pc1 ?orbT // !inE neq_yx.
    by have [[s -> _ _ _]] := monotony; rewrite rank_cat // geq_min leqnn.
  - right; case: (leqP (rank x (stack e)) m2) => [rx_small|/ltnW rx_big].
      rewrite (minn_idPl _) //.
      exists x => //; exists x; rewrite ?inE ?connect0 //.
      by have [[s ->]] := monotony; rewrite rank_cat.
    rewrite (minn_idPr _) //.
    case: pc2 rx_big=> [->|[y]]; first by rewrite leqNgt rank_lt.
    rewrite !inE => /andP[neq_yx y_roots [z y_to_z m_def]].
    by move=> m_small; exists y => //; exists z.
  - by move=> y y_xedge; rewrite (@leq_trans m2) ?pc3 // geq_min leqnn orbT.
case: ifPn=> [x_black|xNblack] //=.
  have := dfs'_is_correct _ x_root.
  rewrite /dfs'_correct; case: (dfsrec' _ _) => [m2 e'].
  move=> e'_correct [to_roots e_wf e_gwf black_sccs].
  case: e'_correct; first exact: pre_dfs'_rootsD1.
  move=> change_color [invariants monotony [pc1 pc2 pc3]].
  split=> //.
    rewrite -(setD1K x_root) subUset change_color sub1set !inE.
    by have [_ /subsetP blacks_mono _] := monotony; rewrite blacks_mono.
  split=> //; split=> //.
  - move=> y y_root; have [->{y y_root}|neq_yx]:= eqVneq y x; last first.
      by rewrite geq_min pc1 ?orbT // !inE neq_yx.
    have m2_rank: m2 <= infty by case: pc2=> [->|[?? [??->]]].
    rewrite rank_infty //.
    
  - 
    
   rewrite 
 
    have [//|xNblack /=] := boolP (x \in blacks _).
    by have [[s ->]] := monotony; rewrite mem_cat x_stack orbT.
    

set m1 := rank x _; case: (leqP m1 m2) => [rx_small|/ltnW rx_big].
      rewrite (minn_idPl _) //.
      by move=> y y_xedge; rewrite (leq_trans rx_small) // pc3.
    
      admit.
    
      
    
    
    

  - right; case: pc2=> [->|[y]]; last first.
      (* rewrite (minn_idPl _) //. *)
      rewrite !inE => /andP[neq_yx y_roots [z y_to_z m_def]].
      exists y => //. exists z=> //; rewrite -m_def.

move=> y y_roots z z_to_y. /eqP[].
    
      
   
   


    exists (last 
     
    
  rewrite /pre_dfs /post_dfs //=.


Admitted.


Lemma 



(* Definition wf_stack e := *)
(*   [/\ wf_color e, *)
(*       uniq (stack e), *)
(*       forall x, x \in grays e -> forall y, y \in stack e -> *)
(*           (rank x (stack e) <= rank y (stack e)) -> gconnect x y & *)
(*       forall y, y \in stack e -> exists2 x, x \in grays e & *)
(*           (rank x (stack e) <= rank y (stack e)) && gconnect y x *)
(*   ]. *)




Lemma dfs1_is_correct (dfs' : {set V} -> env -> nat * env) (x : V) e :
  (dfs'_correct dfs' [set y in successors x] (add_stack x e)) ->
  dfs1_correct (dfs1 dfs') x e.
Proof.
rewrite /dfs1_correct /dfs1 /=.
rewrite /dfs'_correct.
case: (dfs' _ _) => m e' /= dfs_is_correct.
case: leqP => [rank_small|rank_big] /=; case: e' => b' s' sccs' in dfs_is_correct *.
  move=> x_white []; split.
  - split.
    + split.
      *
Admitted.


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
