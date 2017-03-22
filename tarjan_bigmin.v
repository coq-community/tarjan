From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop finset finfun perm fingraph path div.
Require Import bigmin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section extra_div.

Lemma ltn_div2r p m n : p > 0 -> m %/ p < n %/ p -> m < n.
Proof.
move=> p_gt0 lt_div; rewrite (divn_eq m p) (divn_eq n p).
rewrite -(subnKC lt_div) mulnDl mulSn -!addnA addnCA ltn_add2l.
by rewrite (leq_trans (ltn_pmod _ _)) // leq_addr.
Qed.

Lemma ltn_mod2r p m n : p > 0 -> m %/ p = n %/ p -> m %% p < n %% p -> m < n.
Proof.
move=> p_gt0 eq_div lt_mod; rewrite (divn_eq m p) (divn_eq n p).
by rewrite {}eq_div ltn_add2l in lt_mod *.
Qed.

End extra_div.

Section extra_seq.

Lemma take_subseq (T : eqType) n (s : seq T) : subseq (take n s) s.
Proof. by rewrite -[X in subseq _ X](cat_take_drop n) prefix_subseq. Qed.

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

End extra_seq.

Section extra_fintype.

Lemma subset_cover (T: finType) (sccs sccs' : {set {set T}}) :
  sccs \subset sccs' -> cover sccs \subset cover sccs'.
Proof.
move=> /subsetP subsccs; apply/subsetP=> x /bigcupP [scc /subsccs].
by move=> scc' x_in; apply/bigcupP; exists scc.
Qed.

End extra_fintype.

Section tarjan.

Variable (V : finType) (successors : V -> seq V).
Notation edge := (grel successors).
Notation gconnect := (connect edge).
Notation infty := #|V|.

(*************************************************)
(* Connected components of the graph, abstractly *)
(*************************************************)

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

Definition cover_gsccs := cover_partition gsccs_partition.

Lemma trivIset_gsccs : trivIset gsccs.
Proof. by case/and3P: gsccs_partition. Qed.
Hint Resolve trivIset_gsccs.

Notation scc_of := (pblock gsccs).

Lemma mem_scc x y : x \in scc_of y = gbiconnect y x.
Proof.
by rewrite pblock_equivalence_partition // => ?*; apply: gbiconnect_equiv.
Qed.

Definition def_scc scc x := @def_pblock _ _ scc x trivIset_gsccs.

Definition is_subscc (A : {set V}) :=
  A != set0 /\ {in A &, forall x y, gconnect x y}.

Lemma is_subscc_in_scc (A : {set V}) :
  is_subscc A -> exists2 scc, scc \in gsccs & A \subset scc.
Proof.
move=> []; have [->|[x xA]] := set_0Vmem A; first by rewrite eqxx.
move=> AN0 A_sub; exists (scc_of x); first by rewrite pblock_mem ?cover_gsccs.
by apply/subsetP => y yA; rewrite mem_scc /= !A_sub //.
Qed.

Lemma is_subscc1 x (A : {set V}) : x \in A ->
  (forall y, y \in A -> gconnect x y /\ gconnect y x) -> is_subscc A.
Proof.
move=> xA AP; split; first by apply: contraTneq xA => ->; rewrite inE.
by move=> y z /AP [xy yx] /AP [xz zx]; rewrite (connect_trans yx).
Qed.

(**********************************************************)
(*               Tarjan 72 algorithm,                     *)
(* rewritten in a functional style by JJ Levy & Ran Chen  *)
(**********************************************************)

Definition split_after (T :eqType) (x : T) (s : seq T) :=
  let i := index x s in (rcons (take i s) x, drop i.+1 s).

Fixpoint rank (x : V) stack : nat :=
  if stack isn't y :: s then infty
  else if (x == y) && (x \notin s) then size s else rank x s.

Record env := Env {blacks : {set V}; stack : seq V; sccs : {set {set V}}}.

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
         if [|| x \in stack e | x \in blacks e] then (rank x (stack e), e)
         else dfs1 x e in
       let: (m2, e2) := dfs' roots' e1 in (minn m1 m2, e2).

Fixpoint tarjan_rec n : {set V} -> env -> nat * env :=
  if n is n.+1 then dfs' (dfs1 (tarjan_rec n)) (tarjan_rec n)
  else fun r e => (infty, e).

Let N := #|V| * #|V|.+1 + #|V|.
Definition e0 := (Env set0 [::] set0).
Definition tarjan := sccs (tarjan_rec N setT e0).2.

(**************************************************************)
(* Well formed environements and operations on environements. *)
(**************************************************************)

Section other_colors.

Notation grays_def := (fun e => [set x in stack e] :\: blacks e).
Fact gray_key : unit. Proof tt.
Definition grays := locked_with gray_key grays_def.
Lemma graysE : grays = grays_def. Proof. exact: unlock. Qed.

Notation whites_def := (fun e => ~: (grays e :|: blacks e)).
Fact white_key : unit. Proof tt.
Definition whites := locked_with white_key whites_def.
Lemma whitesE : whites = whites_def. Proof. exact: unlock. Qed.

End other_colors.

Record wf_env e := WfEnv {
   wf_stack : stack e =i grays e :|: (blacks e :\: cover (sccs e));
   wf_sccs : cover (sccs e) \subset blacks e;
   wf_uniq : uniq (stack e)
}.
Hint Resolve wf_sccs.
Hint Resolve wf_uniq.

Inductive color4_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| Color4Gray of x \in grays e : color4_spec x e false true false true false
| Color4Sccs of x \in cover (sccs e) :
                       color4_spec x e true false true false false
| Color4White of x \in whites e : color4_spec x e false false false false true
| Color4BlackStack of x \in blacks e & x \in stack e :
                        color4_spec x e true true false false false.

Lemma color4P x e : wf_env e ->
                   color4_spec x e (x \in blacks e) (x \in stack e)
                              (x \in cover (sccs e))
                              (x \in grays e) (x \in whites e).
Proof.
move=> [/(_ x) s_def /subsetP /(_ x) /implyP].
move: s_def; rewrite whitesE graysE !inE.
case x_black: (_ \in blacks _) => /=;
case x_stack : (_ \in stack _) => /=;
case x_sccs : (_ \in cover _) => //=; do ?by constructor.
  by constructor=> //; rewrite graysE !inE x_black.
by constructor; rewrite whitesE graysE !inE x_black x_stack.
Qed.

Lemma grays0 : grays e0 = set0.
Proof. by apply/setP=> x; rewrite graysE !inE /=. Qed.

Lemma cover0 : cover set0 = set0 :> {set V}.
Proof.
by apply/setP=> x; rewrite !inE; apply/negP=> /bigcupP[?]; rewrite inE.
Qed.

Lemma whites_blacksF x e : x \in whites e -> x \in blacks e = false.
Proof. by rewrite whitesE graysE !inE; case: (x \in blacks _). Qed.

Lemma whites_stackF x e : x \in whites e -> x \in stack e = false.
Proof.
by rewrite whitesE graysE !inE andbC; case: (x \in stack _); rewrite //= orNb.
Qed.

Lemma whites_graysF x e : x \in whites e -> x \in grays e = false.
Proof. by rewrite whitesE !inE; case: (x \in grays e). Qed.

Lemma grays_stack x e : x \in grays e -> x \in stack e.
Proof. by rewrite graysE !inE andbC; case: (x \in stack _). Qed.

Lemma stack_whitesF x e : x \in stack e -> x \in whites e = false.
Proof. by rewrite whitesE graysE !inE => ->; case: (_ \in _). Qed.

Lemma stack_sccsF x e : wf_env e -> x \in stack e ->
  x \in cover (sccs e) = false.
Proof. by case/color4P. Qed.

Lemma blacks_whitesF x e : x \in blacks e -> x \in whites e = false.
Proof. by rewrite whitesE graysE !inE => ->. Qed.

Lemma grays_blacksF x e : wf_env e -> x \in grays e ->
   x \in blacks e = false.
Proof. by case/color4P. Qed.

Lemma grays_sccsF x e : wf_env e -> x \in grays e ->
   x \in cover (sccs e) = false.
Proof. by case/color4P. Qed.

Lemma sccs_stackF x e : wf_env e ->
  x \in cover (sccs e) -> x \in stack e = false.
Proof. by case/color4P. Qed.

Lemma sccs_blacks x e : wf_env e -> x \in cover (sccs e) -> x \in blacks e.
Proof. by case/color4P. Qed.

Inductive color3_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| Color3Gray of x \in grays e : color3_spec x e false true false true false
| Color3Black of x \in blacks e : color3_spec x e true (x \in stack e)
                                             (x \in cover (sccs e)) false false
| Color3White of x \in whites e : color3_spec x e false false false false true.

Lemma color3P x e : wf_env e ->
  color3_spec x e (x \in blacks e) (x \in stack e)
                  (x \in cover (sccs e)) (x \in grays e) (x \in whites e).
Proof.
move=> e_wf; have: x \in blacks e :|: grays e :|: whites e.
  by rewrite !inE; case: color4P.
rewrite !inE; case xb : (_ \in blacks e);
case xg: (_ \in grays e); case xw : (_ \in whites e)=> //=;
by [constructor|case: color4P xb xg xw => //; do ?constructor].
Qed.

Inductive stack3_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| Stack3Stack of x \in stack e : stack3_spec x e (x \in blacks e) true false
                                             (x \in grays e) false
| Stack3Sccs of x \in cover (sccs e) : stack3_spec x e true false true false false
| Stack3White of x \in whites e : stack3_spec x e false false false false true.

Lemma stack3P x e : wf_env e ->
  stack3_spec x e (x \in blacks e) (x \in stack e)
                  (x \in cover (sccs e)) (x \in grays e) (x \in whites e).
Proof.
move=> e_wf; have: x \in [set y in stack e] :|: cover (sccs e) :|: whites e.
  by rewrite !inE; case: color4P.
rewrite !inE; case: color4P => //= [xg|xsccs|xw|xb xs] _; do ?by constructor.
  by have := Stack3Stack (grays_stack xg); case: color4P xg.
by have := Stack3Stack xs; case: color4P xs xb.
Qed.

Lemma whites_add_stack x e : whites (add_stack x e) = whites e :\ x.
Proof.
apply/setP=> y; rewrite whitesE graysE !inE /=.
by case: (_ \in _) (_ \in _) (_ == _) => [] [] [].
Qed.

Lemma grays_add_stack x e : x \in whites e ->
  grays (add_stack x e) = x |: grays e.
Proof.
move=> x_whites; apply/setP=> y; move: x_whites; rewrite whitesE graysE !inE.
by case: eqP => [->|]; case: (_ \in _) (_ \in _)=> [] [].
Qed.

Lemma stack_add_stack x e : stack (add_stack x e) = x :: stack e.
Proof. by []. Qed.

Lemma grays_add_blacks e x : grays (add_blacks x e) = grays e :\ x.
Proof. by apply/setP=> y; rewrite graysE !inE /= negb_or andbA. Qed.

Lemma whites_add_blacks e x : whites (add_blacks x e) = whites e :\ x.
Proof.
rewrite whitesE grays_add_blacks /=; apply/setP=> y; rewrite !inE.
by case: (_ == _) (_ \in _) (_ \in _) => [] [].
Qed.

Lemma grays_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  uniq (stack e) -> s \subset blacks e -> x \in grays e ->
  grays (add_sccs x e) = grays e :\ x.
Proof.
move=> /= se_uniq sb x_gray; rewrite /add_sccs graysE /=.
case: splitP sb se_uniq; first by rewrite grays_stack.
move=> s s' sb sxs'_uniq.
apply/setP=> y; rewrite !inE mem_cat mem_rcons in_cons.
have [->|] //= := altP eqP; rewrite orbC ![(y \notin _) && _]andbC.
have [|yNs' neq_yx] //= := boolP (y \in s').
by have [y_s|] //= := boolP (y \in s); rewrite (subsetP sb).
Qed.

Lemma add_stack_ewf x e : x \in whites e -> wf_env e -> wf_env (add_stack x e).
Proof.
move=> x_white e_wf; split=> /=; do ?
  by [exact: wf_sccs|rewrite whites_stackF ?wf_uniq].
move=> y; rewrite grays_add_stack // !inE.
by case: (_ == _) color4P => [] [].
Qed.

Lemma add_blacks_ewf x e : x \in grays e -> wf_env e -> wf_env (add_blacks x e).
Proof.
move=> x_gray e_wf; split => //=; last 2 first.
- by rewrite subsetU // wf_sccs // orbT.
- exact: wf_uniq.
move=> y; rewrite grays_add_blacks !inE.
have [->|] := altP (y =P x); case: color4P => //.
by case: color4P x_gray.
Qed.

Lemma whites_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  x \in grays e -> uniq (stack e) -> s \subset blacks e ->
  whites (add_sccs x e) = whites e.
Proof.
move=> /= x_gray se_uniq sb; rewrite whitesE grays_add_sccs //=.
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

Lemma add_sccs_wf x e :
  take (index x (stack e)) (stack e) \subset blacks e ->
  x \in grays e -> wf_env e -> wf_env (add_sccs x e).
Proof.
move=> new_blacks x_gray e_wf.
have [s_def /subsetP sccs_blacks s_uniq] := e_wf.
split => //=; last first.
- by rewrite (subseq_uniq (drop_subseq _ _)).
- apply/subsetP=> y; rewrite !inE.
  rewrite /cover bigcup_setU inE big_set1 !inE /= => /orP[|/sccs_blacks->];
    last by rewrite !orbT.
  by rewrite mem_rcons !inE; case: eqP => //= _ /(subsetP new_blacks).
move=> y; rewrite !inE /cover bigcup_setU inE big_set1 !inE !negb_or.
rewrite graysE ?inE //.
have [->|neq_xy] //= := altP (y =P x); rewrite ?(andbT, andbF).
  case: splitP new_blacks s_uniq => //=; first by rewrite grays_stack.
  move=> s1 s2 s1x_blacks s_uniq; rewrite grays_sccsF // andbT.
  by rewrite (uniq_catRL s_uniq) // mem_cat mem_rcons mem_head.
case: color4P; rewrite ?(andbT, andbF, orbT, orbF) //=.
  by move=> y_sccs; apply: contraTF y_sccs => /mem_drop; case: color4P.
move=> y_blacks; case: splitP s_uniq; first by rewrite grays_stack.
by move=> s1 s2 s_uniq y_in; apply: uniq_catRL.
Qed.

(***************)
(* Rank Theory *)
(***************)

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

Lemma rank_small x s : uniq s -> (rank x s < size s) = (x \in s).
Proof.
move=> s_uniq; rewrite rankE; case: (boolP (x \in s)) => [xNs|_].
  by rewrite -size_rev index_mem mem_rev.
apply: negbTE; rewrite -ltnNge ltnS cardE uniq_leq_size //.
by move=> y; rewrite mem_enum.
Qed.

Arguments rank : simpl never.

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

Lemma rank_mem x s : x \in s -> rank x s < size s.
Proof. by move=> x_s; rewrite rankE x_s -size_rev index_mem mem_rev. Qed.

Lemma rank_le_head s z x : x \notin s -> z \in s ->
  rank z (x :: s) < rank x (x :: s).
Proof.
by move=> xNs z_s; rewrite !rank_cons z_s andbF eqxx xNs /= rank_mem.
Qed.

Lemma ord_rank x s : uniq s -> @inord #|V| (rank x s) = rank x s :> nat.
Proof. by move=> s_uniq; rewrite inordK // ltnS rank_le. Qed.

(********************)
(*   Main Proof !   *)
(********************)

Definition noblack_to_white e :=
  forall x, x \in blacks e -> [disjoint successors x & whites e].

Inductive wf_graph e := WfGraph {
  wf_grays_to_stack : {in grays e & stack e, forall x y,
         (rank x (stack e) <= rank y (stack e)) -> gconnect x y};
  wf_stack_to_grays : forall y, y \in stack e ->
                      exists x, [/\ x \in grays e,
     (rank x (stack e) <= rank y (stack e)) & gconnect y x]
  }.

Definition access_to e (roots : {set V}) :=
  {in grays e & roots, forall x y, gconnect x y}.

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
  rewrite grays_add_stack //= => x y; rewrite rank_cons !inE.
  move=> /orP[/eqP->|xg] /orP[/eqP->|/=ys];
  rewrite ?rank_cons ?eqxx ?(@whites_stackF w) ?xs ?ys ?(andbF, andbT) //=.
  + by rewrite leqNgt rank_small ?wf_uniq // ys.
  + by move=> _; rewrite grays_to ?inE.
  + by rewrite grays_stack // andbF; apply: gs.
move=> y; rewrite inE => /predU1P [->|].
  by exists w; rewrite ?grays_add_stack ?inE ?eqxx.
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
move=> x y; rewrite grays_add_stack // !inE => /predU1P [->|].
  by move=> y_succ_w; rewrite connect1.
move=> /grays_to x_to_y y_succ_w.
by rewrite (connect_trans _ (connect1 y_succ_w)) // x_to_y ?inE.
Qed.

(* Definition xedges (new old : seq V) := *)
(*   [set y in old | [exists x in new, (x \notin old) && edge x y]]. *)

Definition wedge e := [rel x y | (x \in whites e) && edge x y].
Definition wreach e x := [set y in connect (wedge e) x].

Lemma mem_wreach e x : x \in wreach e x.
Proof. by rewrite !inE connect0. Qed.

Lemma Nwreach e x : x \notin whites e -> wreach e x = [set x].
Proof.
move=> xNwhite; apply/eqP; rewrite eqEsubset sub1set mem_wreach andbT.
apply/subsetP=> y; rewrite !inE => /connectP [].
by move=> [|z p] /=; rewrite ?(negPf xNwhite) // => _ ->.
Qed.

Definition subenv e1 e2 :=
  [&&  grays e1 == grays e2,
       blacks e1 \subset blacks e2,
       sccs e1 \subset sccs e2 &
       [exists n : 'I_infty.+1, stack e1 == drop n (stack e2)]].

Lemma subenv_grays e1 e2 : subenv e1 e2 -> grays e2 = grays e1.
Proof. by move=> /and4P [/eqP]. Qed.

Lemma subenv_blacks e1 e2 : subenv e1 e2 -> blacks e1 \subset blacks e2.
Proof. by move=> /and4P []. Qed.

Lemma subenv_sccs e1 e2 : subenv e1 e2 -> sccs e1 \subset sccs e2.
Proof. by move=> /and4P []. Qed.

Lemma subenvN_subproof e1 e2 : subenv e1 e2 ->
  {n : nat | stack e1 = drop n (stack e2)}.
Proof. by move=> /and4P [_ _ _ /existsP /sigW[n /eqP]]; exists n. Qed.

Definition subenvN e1 e2 :=
  if subenv e1 e2 =P true isn't ReflectT e12 then 0
  else projT1 (subenvN_subproof e12).

Lemma subenv_drop e2 e1 : subenv e1 e2 ->
  stack e1 = drop (subenvN e1 e2) (stack e2).
Proof. by rewrite /subenvN; case: eqP => // ??; case: subenvN_subproof. Qed.

Lemma subenv_take e1 e2 : wf_env e2 -> subenv e1 e2 ->
  take (subenvN e1 e2) (stack e2) \subset blacks e2.
Proof.
set n := subenvN e1 e2; move=> e2_wf e12; apply/subsetP=> x x_p2.
suff: (x \in stack e2) && (x \notin grays e2) by case: color4P.
rewrite (mem_take x_p2) (subenv_grays e12) /=.
apply: contraTN isT => /grays_stack.
have := wf_uniq e2_wf; rewrite -[stack e2](cat_take_drop n) => s12_uniq.
by rewrite (subenv_drop e12) (uniq_catRL s12_uniq) ?x_p2 // mem_cat x_p2.
Qed.

Lemma uniq_ex_drop (s1 s2 : seq V) :
   uniq s2 -> (exists s, s2 = s ++ s1) ->
   exists n : 'I_infty.+1, s1 = drop n s2.
Proof.
move=> s2_uniq [s s2_def]; exists (inord (size s)).
rewrite s2_def inordK ?drop_cat ?ltnn ?subnn ?drop0 // ltnS.
rewrite -(card_uniqP _) ?max_card //.
by move: s2_uniq; rewrite s2_def cat_uniq => /andP[].
Qed.

Lemma subenv_stackP e1 e2 : wf_env e2 -> subenv e1 e2 ->
  exists2 s, stack e2 = s ++ stack e1 & s \subset (blacks e2).
Proof.
move=> e2_wf e12; pose n := subenvN e1 e2; exists (take n (stack e2)).
  by rewrite (subenv_drop e12) // cat_take_drop.
by rewrite subenv_take.
Qed.

Lemma subenv_whites e1 e2 : subenv e1 e2 -> whites e2 \subset whites e1.
Proof.
by move=> e12; rewrite whitesE setCS (subenv_grays e12) setUS ?subenv_blacks.
Qed.

Lemma new_whites e1 e2 : wf_env e2 -> subenv e1 e2 ->
   whites e1 :\: whites e2 = blacks e2 :\: blacks e1.
Proof.
move=> e2_wf e12; rewrite whitesE -(subenv_grays e12) setDE setCK setIC -setDE.
rewrite setDUl setDE setCU setIA setICr set0I set0U.
rewrite setDUr (setIidPr _) // [_ :\: grays _](setDidPl _) ?subsetDl //.
by apply/pred0P => y /=; case: color4P.
Qed.

Lemma subenv_refl : reflexive subenv.
Proof.
move=> e; rewrite /subenv eqxx !subxx /=.
by apply/existsP; exists ord0; rewrite drop0.
Qed.
Hint Resolve subenv_refl.

Lemma subenvee e : subenv e e. Proof. exact: subenv_refl. Qed.
Hint Resolve subenvee.

Lemma subenv_trans e2 e1 e3 : wf_env e2 -> wf_env e3 ->
  subenv e1 e2 -> subenv e2 e3 -> subenv e1 e3.
Proof.
move=> e2_wf e3_wf e12 e23; rewrite /subenv.
rewrite (subenv_grays e23) (subenv_grays e12) eqxx.
rewrite (subset_trans (subenv_blacks e12)) ?subenv_blacks //.
rewrite (subset_trans (subenv_sccs e12)) ?subenv_sccs //=.
apply/'exists_eqP; apply: uniq_ex_drop; first exact: wf_uniq.
case: (subenv_stackP _ e23) => // s2 -> _.
case: (subenv_stackP _ e12) => // s1 -> _.
by exists (s2 ++ s1); rewrite catA.
Qed.

Definition post_dfs (roots : {set V}) (e e' : env) (m : nat) :=
[/\ [/\ wf_env e', wf_graph e', noblack_to_white e'
      & sccs e' = black_gsccs e'],

   subenv e e',

   whites e' = whites e :\: \bigcup_(x in roots) wreach e x
   &
   m = \min_(y in \bigcup_(x in roots) wreach e x)
         @inord #|V| (rank y (stack e'))
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

Lemma path_xset_xedge g x y (s : pred V) :
  connect g x y -> x \in s -> y \notin s ->
  exists x' y', [/\ x' \in s, y' \notin s,
                    connect [rel u v | [&& u \in s, v \in s & g u v]] x x',
                    g x' y' & connect g y' y].
Proof.
move=> /connectP [p path_xp ->] xs yNs.
pose Ns := [pred x | x \notin s]; pose n := find Ns p.
do [have /= /orP[/negPf->//|pNs] : has Ns (x :: p)] in xs *.
  by apply/hasP; exists (last x p); rewrite ?mem_last.
have n_small : n < size p by rewrite -has_find.
exists (nth x (x :: p) n), (nth x p n); apply/and5P.
rewrite [_ \notin s](@nth_find _ _ Ns) ?(pathP _ _) //=.
have := path_xp; rewrite -{1 5}[p](cat_take_drop n) (drop_nth x) ?cat_path //=.
move=> /and3P [gx1 gx2 gx3].
rewrite [connect g _ _](appP connectP idP) ?andbT /=; last first.
  by exists (drop n.+1 p) => //; rewrite -cat_rcons last_cat last_rcons.
have [->/=|n_gt0] := posnP n; first by rewrite xs connect0.
rewrite -[n]prednK//= [X in X && _]negbFE //=; last first.
  by apply: (@before_find _ _ Ns); rewrite prednK.
apply/connectP; exists (take n p); last first.
  by rewrite (last_nth x) size_take n_small -[n]prednK /= ?nth_take ?prednK.
apply/(pathP x)=> i itnp /=; rewrite (pathP x _) // andbT.
have := itnp; rewrite size_take n_small => iltn.
rewrite nth_take // -[_ && _]negbK negb_and.
rewrite [X in _ || X](@before_find _ _ Ns) // orbF.
case: i => [|i] in iltn {itnp} *; first by rewrite /= xs.
by rewrite /= nth_take 1?ltnW // [X in ~~ X](@before_find _ _ Ns) //= ltnW.
Qed.

Lemma dfs'_is_correct dfs1 dfsrec' (roots : {set V}) e :
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots -> forall e1, whites e1 \subset whites e ->
         dfs'_correct dfsrec' (roots :\ x) e1) ->
  dfs'_correct (dfs' dfs1 dfsrec') roots e.
Proof.
move=> dfs1_is_correct dfs'_is_correct; rewrite /dfs'_correct /dfs'.
case: pickP => [x|no_roots]; last first.
  have roots0 : roots = set0 by apply/setP=> y; rewrite no_roots inE.
  move=> [gto_roots e_wf e_gwf black_sccs]; split=> //.
    by apply/subsetP=> x; rewrite !inE no_roots.
  split=> //.
    by rewrite roots0 big_set0 setD0.
  by rewrite roots0 !big_set0.
move=> x_root; have := dfs'_is_correct _ x_root; rewrite /dfs'_correct.
move=> dfsrec'_correct pre.
have [to_roots e_wf e_gwf Nbw black_sccs] := pre.
have e_uniq := @wf_uniq _ e_wf.
case: ifPn=> [x_sVb|xNsVb].
  move: dfsrec'_correct => /(_ _ (subxx _)); case: (dfsrec' _ _) => [m2 e1].
  case; first exact: (pre_dfs_subroots (subD1set _ _)).
  move=> change_color [[e1_wf e1_gwf Nbw1 sccs_e1]
       [sube1] toNwhite m2_min].
  have [//|s1 s1_def sb] := subenv_stackP _ sube1.
  have := wf_uniq e1_wf.
  split=> //.
  - rewrite -(setD1K x_root) subUset change_color sub1set !inE.
    case: color3P => // /(subsetP (subenv_whites sube1)).
    by case: color4P x_sVb.
  split=> //.
  - rewrite -(setD1K x_root) big_setU1 ?setD11 //=.
    rewrite -setDDl toNwhite Nwreach; last by case: color4P x_sVb.
    rewrite [whites e :\ _](setDidPl _) //.
    apply/pred0P=> y //=; rewrite inE andbC.
    by case: eqP => //->; case: color4P x_sVb. (* to simplify *)
  - rewrite -(setD1K x_root) big_setU1 ?setD11 // bigmin_setU /= m2_min.
    congr (minn _ _); rewrite Nwreach; last by case: color4P x_sVb.
    rewrite big_set1 ord_rank // s1_def.
    case: (boolP (_ \in stack e)) x_sVb => /= [/rank_catl->|xNs x_black] //.
    rewrite !rank_infty // -s1_def; case: color4P xNs x_black => //.
    by move=> /(subsetP (subset_cover (subenv_sccs sube1))); case: color4P.
have := dfs1_is_correct _ x_root; rewrite /dfs1_correct.
case: (dfs1 _ _) => [m1 e1] post_dfs1.
move: dfsrec'_correct => /(_ e1).
case: (dfsrec' _ _) => [m2 e2] post_dfs' {dfs1_is_correct dfs'_is_correct}.
have x_white : x \in whites e by case: color4P xNsVb.
have := post_dfs1 x_white (pre_dfs_subroots _ pre).
rewrite sub1set x_root => /(_ isT) {post_dfs1}.
case=> [x_black [[e1_wf e1_gwf Nbw1 sccs_e1] sube1 whites1 m1_min]].
have [//|s1 s1_def s1b] := subenv_stackP _ sube1.
have e1_uniq := wf_uniq e1_wf.
rewrite big_set1 in whites1 m1_min.
case: post_dfs'.
- by rewrite subenv_whites.
- split=> // y z; rewrite graysE !inE s1_def mem_cat.
  case: (y \in s1) (subsetP s1b y) => //= [->//|_ /andP[yNb ys]].
  move=> /andP[_ z_roots]; rewrite to_roots // graysE !inE.
  rewrite ys andbT; apply: contraNN yNb; apply/subsetP.
  by rewrite subenv_blacks.
move=> rootsDx_subset [[e2_wf e2_gwf Nbw2 sccs_e2] sube2 whites2 m2_min].
have [//|s2 s2_def s2b] := subenv_stackP _ sube2.
have e2_uniq := wf_uniq e2_wf.
have split_wreach : \bigcup_(y in roots) wreach e y =
     wreach e x :|: \bigcup_(y in roots :\ x) wreach e1 y.
  rewrite -{1}(setD1K x_root) big_setU1 ?setD11 //=; apply/setP => y.
  rewrite !in_setU; have [//|/=Nxy] := boolP (_ \in wreach _ _).
  apply/bigcupP/bigcupP=> - [] z z_roots zy; exists z => //; last first.
    rewrite !inE in zy *; apply: connect_sub zy => u v /= /andP [uw uv].
    by rewrite connect1 //= uv andbT; apply: subsetP uw; rewrite subenv_whites.
  have [->|neq_yz] := altP (y =P z); first by rewrite mem_wreach.
  have [|notout] := pickP [pred t |
    [&& t \notin whites e1, y \in wreach e t  & t \in wreach e1 z]].
    move=> t /= /and3P []; rewrite whites1 inE negb_and negbK.
    move=> /orP [xt ty _|tNw].
      by rewrite !inE /= in Nxy xt ty; rewrite (connect_trans xt) in Nxy.
    by rewrite Nwreach // inE => /eqP->.
  apply: contraTT isT => yNwreach; rewrite !inE in zy *.
  have [x' [y' []]] := path_xset_xedge zy (mem_wreach e1 z) yNwreach.
  rewrite !inE => x'_wreach y'_wreach zx' /andP[x'white x'y'] y'y.
  have /= <- := notout x'; rewrite !inE x'_wreach andbT.
  rewrite (connect_trans _ y'y) ?connect1 /= ?x'white // andbT.
  apply: contra y'_wreach=> x'white1.
  by rewrite (connect_trans x'_wreach) ?connect1 //= x'white1.
split.
  rewrite -(setD1K x_root) subUset rootsDx_subset andbT sub1set.
  by rewrite inE (subsetP (subenv_blacks sube2)).
split => //; first exact: subenv_trans sube2.
- by rewrite whites2 whites1 split_wreach setDDl.
- rewrite m1_min m2_min split_wreach bigmin_setU /=.
  congr (minn (val _) _); apply: eq_bigr => y xy; apply/val_inj=> /=.
  rewrite !ord_rank //.
  have /orP[ys|ysccs] : (y \in stack e1) || (y \in cover (sccs e1)).
  + suff: y \notin whites e1 by case: color4P.
    by rewrite whites1 inE xy.
  + by rewrite s2_def rank_catl.
  + rewrite !rank_infty ?sccs_stackF //.
    by apply: subsetP ysccs; rewrite subset_cover ?subenv_sccs.
Qed.

Lemma dfs1_is_correct dfs' (x : V) e :
  (dfs'_correct dfs' [set y | edge x y] (add_stack x e)) ->
  dfs1_correct (dfs1 dfs') x e.
Proof.
rewrite /dfs1 /dfs1_correct /dfs'_correct; case: (dfs' _ _) => m1 e1.
move=> post_dfs'; set m := rank x _.
move=> x_white [access_to_x e_wf e_gwf Nbw black_sccs].
have e_uniq := @wf_uniq _ e_wf.
case: post_dfs' => //=.
  split => //; do?[exact: add_stack_ewf|exact: add_stack_gwf]; last first.
     move=> y /Nbw; rewrite whites_add_stack.
     rewrite ![[disjoint successors _ & _]]disjoint_sym.
     by apply/disjoint_trans/subsetDl.
  move=> y z; rewrite grays_add_stack // => /setU1P [->|y_gray];
    rewrite inE => /(@connect1 _ edge) //.
  by apply/connect_trans/access_to_x; rewrite ?set11.
move=> succ_bVg [[e1_wf e1_gwf Nbw1 black_sccs1] sube1 whites1 m_min].
have [//|s s_def sb] := subenv_stackP _ sube1.
set s2 := rcons s x.
have e1_uniq := @wf_uniq _ e1_wf.
have xe_uniq : uniq (x :: stack e).
  by have := e1_uniq; rewrite s_def cat_uniq => /and3P [].
have x_stack : x \in stack e1 by rewrite s_def mem_cat mem_head orbT.
have x_grays : x \in grays e1.
   by rewrite (subenv_grays sube1) grays_add_stack ?setU11.
have rkx : rank x (x :: stack e) = rank x (stack e1).
  by rewrite s_def rank_catl ?mem_head.
have sx_subscc : is_subscc [set y in rcons s x].
  apply: (@is_subscc1 x); first by rewrite inE mem_rcons mem_head.
  move=> y; rewrite !inE mem_rcons in_cons => /predU1P [->//|y_s]; split.
    apply: (@wf_grays_to_stack e1) => //; first by rewrite s_def mem_cat y_s.
    rewrite -rkx s_def rank_catr //=; last first.
       by rewrite -(@uniq_catLR _ _ s) ?mem_cat ?y_s // -?s_def //.
    rewrite rankE mem_head (leq_trans (index_size _ _)) //.
    by rewrite size_rev leq_addr.
  have [] := @wf_stack_to_grays _ e1_gwf y; first by rewrite s_def mem_cat y_s.
  move=> z [z_gray rank_z] /connect_trans; apply.
  rewrite (@wf_grays_to_stack e1) // s_def.
  have := z_gray; rewrite graysE !(inE, s_def) mem_cat.
  case: (boolP (z \in s)) => [/(subsetP sb)->//|_ /= /andP [_ z_xe]].
  rewrite !rank_catl ?mem_head //.
  move: z_xe; rewrite in_cons.
  have [->//|neq_zx /= z_s] := altP eqP.
  rewrite ltnW // rank_le_head //.
  rewrite -(@uniq_catLR _ _ (rcons s x)) ?mem_rcons ?mem_head //.
    by rewrite cat_rcons -s_def wf_uniq.
  by rewrite mem_cat mem_rcons mem_head.
have wreachex : wreach e x = x |: \bigcup_(y in [set y in successors x])
                          wreach (add_stack x e) y.
  apply/eqP; rewrite eqEsubset subUset sub1set mem_wreach /=.
  apply/andP; split; last first.
    apply/bigcupsP => y; rewrite inE => xy; apply/subsetP=> z; rewrite !inE.
    move=> /(@connect_sub _ _ (wedge e)) /(connect_trans _)-> //=.
      by rewrite connect1 //= x_white.
    move=> u v; rewrite /= whites_add_stack !inE -andbA => /and3P[_ uw uv].
    by rewrite connect1 //= uw.
  apply/subsetP=> y; rewrite !inE.
  move=> /connectP [_] /shortenP [p exp /andP[xNp _] _ -> {y}].
  case: p => [|y p /=] //= in exp xNp *; first by rewrite eqxx.
  move: exp xNp; rewrite in_cons -andbA => /and3P[_ xy eyp] /norP[neq_xy xNp].
  apply/orP; right; apply/bigcupP; exists y; rewrite ?inE //=.
  suff /path_connect : path (wedge (add_stack x e)) y p.
     by apply; rewrite /= mem_last.
  elim: p => [|z p ihp] //= in y {xy} neq_xy eyp xNp *.
  move: eyp xNp; rewrite in_cons -andbA => /and3P[yw yz ezp] /norP[neq_yz xNp].
  by rewrite whites_add_stack !inE eq_sym neq_xy yw yz /= ihp.
have m2_min : minn m m1 = \min_(y in wreach e x) @inord #|V| (rank y (stack e1)).
  by rewrite wreachex bigmin_setU big_set1 //= /m rkx ord_rank // m_min.
case: ltnP => [m1_small|m1_big] //=; rewrite !inE eqxx /=; split=> //.
  rewrite (minn_idPr _) 1?ltnW// in m2_min.
  have [x1 rank_x1 x_to_x1] : exists2 x1,
    rank x1 (stack e1) = m1 & gconnect x x1.
      have [] := @eq_bigmin_cond _ _ (pred_of_set (wreach e x))
                          (fun y => @inord #|V| (rank y (stack e1))).
        by apply/card_gt0P; exists x; rewrite mem_wreach.
      move=> y; rewrite !inE=> xy /(congr1 val)/=.
      rewrite -m2_min ord_rank // => m1_eq; exists y => //.
      by apply: connect_sub xy => u v /= /andP [_]; apply: connect1.
  have [x' [rank_x' x'_gray x_to_x' ]] : exists x',
    [/\ rank x' (stack e1) < rank x (stack e1), x' \in grays e1 & gconnect x x'].
    move: m1_small; rewrite -{}rank_x1 => rank_x1.
    have x1_stack : x1 \in stack e1.
      by rewrite -rank_lt ?(leq_trans rank_x1) // rank_le.
    have [z [z_gray rank_z y_to_z]] := wf_stack_to_grays e1_gwf x1_stack.
    exists z; split=> //; rewrite 2?inE ?z_gray ?andbT.
    - by rewrite (leq_ltn_trans rank_z) // (leq_trans rank_x1) /m ?rkx.
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
      - by rewrite (leq_trans _ rank_x) 1?ltnW // rkx.
      - by rewrite (connect_trans y_to_x).
    + move=> y; rewrite !inE whites_add_blacks.
      move=> /predU1P [->{y}|y_black]; last first.
        apply/pred0P=> z /=; rewrite 2!inE.
        have /pred0P /(_ z) /= := Nbw1 _ y_black.
        by apply: contraFF=> /and3P[->_->].
      apply/pred0P=> z /=; rewrite 2!inE.
      have /subsetP /(_ z) := succ_bVg.
      rewrite 2!inE => /implyP.
      by case: (_ \in successors _) (_ == _) color4P => [] [] [].
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
      by case: color4P x'_gray.
  - apply/and4P; split => //=.
    + rewrite grays_add_blacks (subenv_grays sube1) grays_add_stack ?setU1K //.
      by rewrite whites_graysF.
    + by rewrite (subset_trans (subenv_blacks sube1)) // subsetUr.
    + by rewrite -[sccs e]/(sccs (add_stack x e)) subenv_sccs.
    + apply/'exists_eqP/uniq_ex_drop; rewrite // s_def /=.
      by exists (rcons s x); rewrite cat_rcons.
  - rewrite whites_add_blacks big_set1 wreachex whites1 whites_add_stack.
    by rewrite !setDDl setUA setUAC setUid.
  - by rewrite m2_min; congr val; apply: eq_bigl=> y; rewrite /= big_set1.
move: m2_min; rewrite (minn_idPl _) // /m rkx => rkx_min.
have rkx_le y : y \in wreach e x -> rank y (stack e1) >= rank x (stack e1).
  by move=> xy; rewrite rkx_min -ord_rank // geq_bigmin_cond.
have scc_max : scc_of x \subset [set y in s2].
  apply/subsetP=> y; rewrite inE=> y_sccx; apply: contraTT isT => yNs2.
  have xy : gconnect x y by have := y_sccx; rewrite mem_scc /= => /andP[].
  have x_s2 : x \in s2 by rewrite mem_rcons mem_head.
  have [x' [y' [x'_s2 y'Ns xx's2 x'y' y'y]]] := path_xset_xedge xy x_s2 yNs2.
  have xx' : gconnect x x'.
    by apply: connect_sub xx's2 => u v /and3P[_ _]; apply: connect1.
  apply: contraNN y'Ns => _.
  have /or3P[] : [|| y' \in whites e1, y' \in cover (sccs e1)
                   | y' \in stack e1] by case: color4P.
  - move: x'_s2; rewrite mem_rcons in_cons => /predU1P [eq_x'x|x_s].
      have /subsetP /(_ y') := succ_bVg.
      by rewrite 2!inE -eq_x'x => /(_ x'y'); case: color4P.
    have /(_ x') := Nbw1; rewrite (subsetP sb) => // /(_ isT).
    by move=> /pred0P /(_ y') /=; rewrite [_ \in _]x'y' /= => ->.
  - move=> /bigcupP [scc'].
    rewrite black_sccs1 inE => /andP[scc'_gsccs scc'_black].
    move=> /def_scc - /(_ scc'_gsccs) eq_scc'; rewrite -eq_scc' in scc'_black.
    have : x \in scc_of y'.
      have:= y_sccx; rewrite !mem_scc /= andbC => /andP[yx _].
      by rewrite (connect_trans y'y) //= (connect_trans xx') //= connect1.
    by move=> /(subsetP scc'_black); case: color4P x_grays.
  - rewrite s_def -cat_rcons mem_cat => /orP[//|y'_stack].
    have xNstack: x \notin stack e.
      rewrite -(@uniq_catLR _ x s2) ?mem_cat ?x_s2 //.
      by rewrite cat_rcons -s_def wf_uniq.
    have x'Nstack: x' \notin stack e.
      rewrite -(@uniq_catLR _ x' s2) ?mem_cat ?x'_s2 //.
      by rewrite cat_rcons -s_def wf_uniq.
    have s2_whites: {subset s2 <= whites e}.
      move=> z z_s2; have: z \notin cover (sccs e).
        apply/negP=> /(subsetP (subset_cover (subenv_sccs sube1))).
        have: z \in stack e1 by rewrite s_def -cat_rcons mem_cat z_s2.
        by case: color4P.
      case: stack3P => //.
      have us2e : uniq (s2 ++ stack e) by rewrite cat_rcons -s_def.
      by rewrite (uniq_catRL us2e) ?mem_cat ?z_s2.
    suff /rkx_le : y' \in wreach e x.
      rewrite s_def !rank_catl ?mem_head ?in_cons ?y'_stack ?orbT //=.
      by rewrite leqNgt rank_le_head.
    rewrite !inE (@connect_trans _ _ x') //; last first.
       by rewrite connect1 /= ?s2_whites.
    apply: connect_sub xx's2 => u v /= /and3P[/s2_whites uw _ uv].
    by rewrite connect1 /= ?uw.
have g1Nx : grays e1 :\ x = grays e.
  by rewrite (subenv_grays sube1) grays_add_stack // setU1K // whites_graysF.
have take_s : take (index x (stack e1)) (stack e1) = s.
  rewrite s_def index_cat /= eqxx addn0.
  rewrite (@uniq_catLR _ _ _ (x :: stack e)) -?s_def ?wf_uniq //.
  by rewrite mem_head /= ?s_def take_cat ltnn subnn take0 cats0.
have drop_s : drop (index x (stack e1)).+1 (stack e1) = stack e.
  rewrite s_def index_cat /= eqxx addn0.
  rewrite (@uniq_catLR _ _ _ (x :: stack e)) -?s_def ?wf_uniq //.
  rewrite mem_head /= ?s_def drop_cat ltnNge leqW //.
  by rewrite subSn // subnn //= drop0.
split=> //.
- split=> //.
  + by apply: add_sccs_wf=> //; rewrite take_s //.
  + split=> //; rewrite ?grays_add_sccs ?stack_add_sccs ?take_s ?drop_s// ?g1Nx.
      exact: wf_grays_to_stack.
      exact: wf_stack_to_grays.
  + move=> y; rewrite !inE whites_add_sccs ?take_s //.
    move=> /predU1P [->|/Nbw1//]; apply/pred0P=> z //=.
    rewrite whitesE !inE; have /subsetP /(_ z) := succ_bVg.
    by rewrite 2!inE => /implyP; rewrite -negb_imply orbC => ->.
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
- rewrite /subenv grays_add_sccs ?take_s ?sb ?g1Nx ?eqxx /= ?drop_s //=.
  rewrite (subset_trans (subenv_blacks sube1)) ?subsetUr //=.
  rewrite (subset_trans (subenv_sccs sube1)) ?subsetUr //=.
  by apply/'exists_eqP; exists ord0; rewrite drop0.
- rewrite whites_add_sccs ?take_s ?sb //.
  by rewrite whites1 whites_add_stack big_set1 wreachex setDDl.
- rewrite big_set1 /= drop_s; apply/eqP; rewrite eqn_leq leq_ord andbT.
  rewrite -[#|V|]/(val ord_max); apply/bigmin_geqP => y /= /rkx_le.
  apply: contraTT; rewrite -!ltnNge ord_rank// rank_lt // => y_stack.
  rewrite !s_def !rank_catl ?mem_head ?in_cons ?y_stack ?orbT //=.
  by rewrite rank_le_head //; case: color4P x_white.
Qed.

Theorem tarjan_rec_terminates n (roots : {set V}) e :
  n >= #|whites e| * #|V|.+1 + #|roots| ->
  dfs'_correct (tarjan_rec n) roots e.
Proof.
move=> n_ge; wlog ->: e n roots {n_ge} / roots = set0 => [noroot|]; last first.
  have := @dfs'_is_correct (dfs1 (tarjan_rec 0)) (tarjan_rec 0) set0 e.
  rewrite /tarjan_rec /dfs'_correct /dfs' /=.
  case: n=> [|n /=]; case: pickP => [x|_/=]; rewrite ?inE //;
  by apply => ?; rewrite inE.
have [V0|VN0] := posnP #|V|.
  have := max_card (mem roots).
  by rewrite V0 leqn0 cards_eq0 => /eqP /noroot; apply.
elim: n => [|n IHn] in roots e n_ge *.
  move: n_ge; rewrite leqn0 addn_eq0 cards_eq0.
  by move=> /andP [_ /eqP/noroot]; apply.
move=> pre; rewrite /dfs'_correct /=.
apply: dfs'_is_correct => //= x x_root.
  move=> x_white; apply: dfs1_is_correct => //; apply: IHn.
  rewrite whites_add_stack cardsDS ?sub1set // cards1 subn1.
  rewrite -ltnS (leq_trans _ n_ge) //.
  rewrite (@ltn_div2r #|V|.+1) ?divnMDl ?divn_small ?addn0 ?ltnS ?max_card //=.
  by rewrite prednK //; apply/card_gt0P; exists x.
move=> e1 whites_e1; apply: IHn; rewrite -ltnS (leq_trans _ n_ge) //.
have /subset_leq_card := whites_e1.
rewrite leq_eqVlt => /predU1P [->|lt_wh]; last first.
  by rewrite (@ltn_div2r #|V|.+1) ?divnMDl ?divn_small ?addn0 ?ltnS ?max_card.
by rewrite ltn_add2l [X in _ < X](cardsD1 x) x_root.
Qed.

Lemma tarjan_rec_is_correct :
  tarjan_rec N setT e0 = (infty, Env setT [::] gsccs).
Proof.
have := @tarjan_rec_terminates N setT e0; rewrite /dfs'_correct.
case: tarjan_rec => [m e] [].
- by rewrite ?leq_add ?leq_mul ?max_card.
- split=> //.
  + by move=> x; rewrite grays0 inE.
  + split=> //; rewrite /= ?cover0 ?grays0 ?set0D ?setU0 //.
    by move=> ?; rewrite inE.
  + by move=> x; rewrite inE.
  + apply/setP=> y; rewrite !inE /= subset0 andbC; case: eqP => //= ->.
    by have /and3P [_ _ /negPf->]:= gsccs_partition.
rewrite subTset => /eqP blackse [[[stack_wf _ _] _ _]] sccse e0e whitese ->.
have := subenv_grays e0e; rewrite grays0 => grayse.
rewrite grayse setU0 in blackse; rewrite /black_gsccs /= blackse in sccse.
have {sccse}sccse: sccs e = gsccs.
  by apply/setP=> scc; rewrite sccse inE subsetT andbT.
have stacke : stack e = [::].
  have := stack_wf; rewrite grayse blackse sccse cover_gsccs set0U setDv.
  by case: stack => // x s /(_ x); rewrite !inE eqxx.
congr (_, _); last by case: (e) blackse sccse stacke => //= *; congr Env.
by rewrite big1=> // x _; apply/val_inj; rewrite stacke /= ord_rank ?rank_infty.
Qed.

Theorem tarjan_correct : tarjan = gsccs.
Proof. by rewrite /tarjan tarjan_rec_is_correct. Qed.

End tarjan.
