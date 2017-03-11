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
       let: (m2, e2) := dfs' roots' e1 in (min m1 m2, e2).

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

Definition wf_graph (roots : {set V}) e :=
  [/\ noblack_to_white e,
   forall x, x \in roots -> forall y, y \in grays e -> gconnect y x,
   forall x, x \in grays e -> forall y, y \in stack e ->
     (rank x (stack e) <= rank y (stack e)) -> gconnect x y &
   forall y, y \in stack e -> exists2 x, x \in grays e &
     (rank x (stack e) <= rank y (stack e)) /\ gconnect y x
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

Lemma add_stack_gwf roots e w : uniq (stack e) -> w \in whites e ->
  wf_graph roots e -> wf_graph roots (add_stack w e).
Proof.
move=> s_uniq w_white [Nbw rg gs sg]; split.
- move=> y /Nbw; rewrite whites_add_stack.
  rewrite ![[disjoint successors _ & _]]disjoint_sym.
  by apply/disjoint_trans/subsetDl.
- admit.
- rewrite grays_add_stack //=.
  move=> x; rewrite rank_cons !inE.
  move=> /orP[/eqP->|/andP[xNb xs]] y; rewrite in_cons=> /orP[/eqP->|/=ys];
  rewrite ?rank_cons ?eqxx ?(@whites_stackF w) ?xs ?ys ?(andbF, andbT) //=.
  + by rewrite leqNgt rank_small // ys.
  + move=> _.
  + admit.
  + by apply: gs; rewrite ?inE ?xNb.
  (* - rewrite leqNgt rank_small //. xs.    apply: gs=> //=. *)
  (*   move=> /orP[/eqP->|ys]. *)
  (*     rewrite eqxx /=. *)
(* move=> y yg z zs ryz. *)
(*   rewrite -[in X in X -> _](setD1K x_white). *)
Abort.


(* Definition wf_stack e := *)
(*   [/\ wf_color e, *)
(*       uniq (stack e), *)
(*       forall x, x \in grays e -> forall y, y \in stack e -> *)
(*           (rank x (stack e) <= rank y (stack e)) -> gconnect x y & *)
(*       forall y, y \in stack e -> exists2 x, x \in grays e & *)
(*           (rank x (stack e) <= rank y (stack e)) && gconnect y x *)
(*   ]. *)



Definition black_gsccs e := [set scc in gsccs | scc \subset blacks e].

Definition xedges (new old : seq V) :=
  [set y in old | [exists x in new, (x \notin old) && edge x y]].

Definition pre_dfs (roots : {set V}) (e e' : env) (m : nat) :=
  [/\ (forall x, x \in roots -> forall y, y \in grays e -> gconnect y x),
    wf_env e, wf_graph roots e & sccs e == black_gsccs e].

Definition dfs_correct (roots : {set V}) (e e' : env) (m : nat) :=
  [/\ (forall x, x \in roots -> forall y, y \in grays e -> gconnect y x),
    wf_env e, wf_graph roots e & sccs e == black_gsccs e]

  ->

  [/\ [/\ wf_env e', wf_graph roots e & (sccs e' == black_gsccs e')],

   [/\ exists x, let: (new, old) := split_after x (stack e) in
          (old == stack e) /\ (new \subset blacks e),
    blacks e \subset blacks e'  & sccs e \subset sccs e' ],

   (roots :&: whites e \subset blacks e') &

   [/\ roots \subset blacks e' :|: grays e',
    forall x, x \in roots -> m <= rank x (stack e'),
    forall x, x \in roots -> forall y, y \in gconnect x ->
         m != rank y (stack e') -> (m = infty) &
    forall y, y \in xedges (stack e') (stack e) -> m <= rank y (stack e')
   ]
  ].

Definition dfs1_correct (dfs1 : V -> env -> nat * env) x e :=
  let (m, e') := dfs1 x e in (x \in whites e) -> dfs_correct (set1 x) e e' m.

Definition dfs'_correct (dfs' : {set V} -> env -> nat * env) roots e :=
  let (m, e') := dfs' roots e in dfs_correct roots e e' m.

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

Lemma dfs'_is_correct dfs1 subdfs' (roots : {set V}) e :
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots -> dfs'_correct subdfs' (roots :\ x) e) ->
  dfs'_correct (dfs' dfs1 subdfs') roots e.
Proof.
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
