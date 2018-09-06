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

Lemma set_last_default (T : eqType) y0 x0 (s : seq T) :
   size s > 0 -> last x0 s = last y0 s.
Proof.
by move=> s_gt0; rewrite -!nth_last; apply/set_nth_default; rewrite ?prednK.
Qed.

Lemma last_take (T : eqType) (x : T) n s :
  last x (take n s) = if n == 0 then x
                      else if n <= size s then nth x s n.-1 else last x s.
Proof.
elim: n s => [|n ihn] [|y s] //= in x *; rewrite {}ihn ltnS; case: n => //=.
by move=> n; case: ltnP => // n_lt; apply/set_nth_default.
Qed.

Lemma last_drop (T : eqType) (x : T) n s :
  last x (drop n s) = if n < size s then last x s else x.
Proof.
case: ltnP => sn; last by rewrite drop_oversize.
rewrite -[s in RHS](cat_take_drop n) last_cat.
by rewrite (@set_last_default _ x) ?size_drop ?subn_gt0.
Qed.

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

Lemma disjoint1s (T: finType) (A : pred T) (x : T) :
   [disjoint [set x] & A] = (x \notin A).
Proof.
apply/pred0P/idP=> [/(_ x)/=|]; first by rewrite inE eqxx /= => ->.
by move=> xNA y; rewrite !inE; case: eqP => //= ->; apply/negbTE.
Qed.

Lemma disjoints1 (T: finType) (A : pred T) (x : T) :
   [disjoint A & [set x]] = (x \notin A).
Proof. by rewrite disjoint_sym disjoint1s. Qed.

End extra_fintype.

Section extra_path.
Variable (V : finType).

Definition relto (a : pred V) (g : rel V) := [rel x y | (y \in a) && g x y].
Definition relfrom (a : pred V) (g : rel V) := [rel x y | (x \in a) && g x y].

Lemma connect_rev (g : rel V) :
  connect g =2 (fun x => connect (fun x => g^~ x) ^~ x).
Proof.
move=> x y; apply/connectP/connectP=> [] [p gp ->];
[exists (rev (belast x p))|exists (rev (belast y p))]; rewrite ?rev_path //;
by case: (lastP p) => //= ??; rewrite belast_rcons rev_cons last_rcons.
Qed.

Lemma path_to a g z p : path (relto a g) z p = (path g z p) && (all a p).
Proof.
apply/(pathP z)/idP => [fgi|/andP[/pathP gi] /allP ga]; last first.
  by move=> i i_lt /=; rewrite gi ?andbT ?[_ \in _]ga // mem_nth.
rewrite (appP (pathP z) idP) //=; last by move=> i /fgi /= /andP[_ ->].
by apply/(all_nthP z) => i /fgi /andP [].
Qed.

Lemma path_from a g z p :
  path (relfrom a g) z p = (path g z p) && (all a (belast z p)).
Proof. by rewrite -rev_path path_to all_rev rev_path. Qed.


Lemma connect_to (a : pred V) (g : rel V) x z : connect g x z ->
  exists y, [/\ (y \in a) ==> (x == y) && (x \in a),
                 connect g x y & connect (relto a g) y z].
Proof.
move=> /connectP [p gxp ->].
pose P := [pred i | let y := nth x (x :: p) i in
  [&& connect g x y & connect (relto a g) y (last x p)]].
have [] := @ex_minnP P.
  by exists (size p); rewrite /= nth_last (path_connect gxp) //= mem_last.
move=> i /= /andP[g1 g2] i_min; exists (nth x (x :: p) i); split=> //.
case: i => [|i] //= in g1 g2 i_min *; first by rewrite eqxx /= implybb.
have i_lt : i < size p.
  by rewrite i_min // !nth_last /= (path_connect gxp) //= mem_last.
have [<-/=|neq_xpi /=] := altP eqP; first by rewrite implybb.
have := i_min i; rewrite ltnn => /contraNF /(_ isT) <-; apply/implyP=> axpi.
rewrite (connect_trans _ g2) ?andbT //; last first.
  by rewrite connect1 //= [_ \in _]axpi /= (pathP x _).
by rewrite (path_connect gxp) //= mem_nth //= ltnW.
Qed.

Lemma connect_from (a : pred V) (g : rel V) x z : connect g x z ->
  exists y, [/\ (y \in a) ==> (z == y) && (z \in a),
                connect (relfrom a g) x y & connect g y z].
Proof.
rewrite connect_rev => cgxz; have [y [ayaz]]//= := connect_to a cgxz.
by exists y; split; rewrite // connect_rev.
Qed.

Lemma connect1l (g : rel V) x z :
  connect g x z -> z != x -> exists2 y, g x y & connect g y z.
Proof.
move=> /connectP [[|y p] //= xyp ->]; first by rewrite eqxx.
by move: xyp=> /andP[]; exists y => //; apply/connectP; exists p.
Qed.

Lemma connect1r (g : rel V) x z :
  connect g x z -> z != x -> exists2 y, connect g x y & g y z.
Proof.
move=> xz zNx; move: xz; rewrite connect_rev => /connect1l.
by rewrite eq_sym => /(_ zNx) [y]; exists y; rewrite // connect_rev.
Qed.

Section Diconnect.

Variable r : rel V.

(* x is diconnected to y *)
Definition diconnect x y  :=  connect r x y && connect r y x.

Lemma diconnect0 : reflexive diconnect.
Proof. by move=> x; apply/andP. Qed.

Lemma diconnect_sym : symmetric diconnect.
Proof. by move=> x y; apply/andP/andP=> [] []. Qed.

Lemma diconnect_trans : transitive diconnect.
Proof.
move=> x y z /andP[Cyx Cxy] /andP[Cxz Czx].
by rewrite /diconnect (connect_trans Cyx) ?(connect_trans Czx).
Qed.
Hint Resolve diconnect0 diconnect_sym diconnect_trans.

Lemma diconnect_equiv : equivalence_rel diconnect.
Proof. by apply/equivalence_relP; split; last apply/sym_left_transitive. Qed.

(*************************************************)
(* Connected components of the graph, abstractly *)
(*************************************************)

Definition sccs := equivalence_partition diconnect setT.

Lemma sccs_partition : partition sccs setT.
Proof. by apply: equivalence_partitionP => ?*; apply: diconnect_equiv. Qed.

Definition cover_sccs := cover_partition sccs_partition.

Lemma trivIset_sccs : trivIset sccs.
Proof. by case/and3P: sccs_partition. Qed.
Hint Resolve trivIset_sccs.

Notation scc_of := (pblock sccs).

Lemma mem_scc x y : x \in scc_of y = diconnect y x.
Proof.
by rewrite pblock_equivalence_partition // => ?*; apply: diconnect_equiv.
Qed.

Definition def_scc scc x := @def_pblock _ _ scc x trivIset_sccs.

Definition is_subscc (A : {set V}) := A != set0 /\
                                      {in A &, forall x y, connect r x y}.

Lemma is_subscc_in_scc (A : {set V}) :
  is_subscc A -> exists2 scc, scc \in sccs & A \subset scc.
Proof.
move=> []; have [->|[x xA]] := set_0Vmem A; first by rewrite eqxx.
move=> AN0 A_sub; exists (scc_of x); first by rewrite pblock_mem ?cover_sccs.
by apply/subsetP => y yA; rewrite mem_scc /diconnect !A_sub.
Qed.

Lemma is_subscc1 x (A : {set V}) : x \in A ->
  (forall y, y \in A -> connect r x y /\ connect r y x) -> is_subscc A.
Proof.
move=> xA AP; split; first by apply: contraTneq xA => ->; rewrite inE.
by move=> y z /AP [xy yx] /AP [xz zx]; rewrite (connect_trans yx).
Qed.

End Diconnect.

Lemma eq_diconnect r1 r2 : r1 =2 r2 -> diconnect r1 =2 diconnect r2.
Proof.
by move=> r1Er2 x y; rewrite /diconnect !(eq_connect r1Er2).
Qed.

Section Relto.

Variable r : rel V.

Local Notation "x -[]-> y" :=
  (connect r x y) (at level 10, format "x  -[]->  y") .

Local Notation connect_to s :=  (connect (rel_of_simpl_rel (relto s r))).

Local Notation "x -[ s ]-> y" := (connect_to s x y)
  (at level 10, format "x  -[ s ]->  y").

Local Notation "x =[]= y" := (diconnect r x y) 
  (at level 10, format "x  =[]=  y").

Local Notation diconnect_to a := (diconnect (rel_of_simpl_rel (relto a r))).

Local Notation "x =[ a ]= y" := (diconnect (rel_of_simpl_rel (relto a r)) x y) 
  (at level 10, format "x  =[ a ]=  y").

Lemma connect_to1 (a : pred V) x y : y \in a -> r x y -> x -[a]-> y.
Proof. by move=> ay Rxy; rewrite connect1 //= ay. Qed.

Lemma sub_connect_to (a b : pred V) : 
  a \subset b -> subrel (connect_to a) (connect_to b).
Proof.
move=> /subsetP sub_ab; apply: connect_sub => x y.
by move=> /andP[/sub_ab ??]; apply: connect_to1.
Qed.

Lemma connect_toW a : subrel (connect_to a) (connect r).
Proof. by apply/(@sub_connect_to _ predT)/subsetP. Qed.

Lemma sub_diconnect_to (a b : pred V) : 
  a \subset b -> subrel (diconnect_to a) (diconnect_to b).
Proof. 
by move=> subab ?? /andP[??]; rewrite /diconnect !(sub_connect_to subab).
Qed.

Lemma eq_diconnect_to (a b : pred V) x y : a =i b -> x =[a]= y = x =[b]= y.
Proof. by move=> eq_ab; apply: eq_diconnect=> x1 y1; rewrite /= eq_ab. Qed.

Lemma reltoT : relto predT r = r :> rel _. Proof. by []. Qed.

Lemma connect_to_forced (a : pred V) x y :
 (forall z, z != x -> x -[]-> z ->  z -[]-> y -> a z) ->
  x -[]-> y ->  x -[a]-> y.
Proof.
move=> Hf /connectP[p {p}/shortenP[p Hp Up _ Hy]].
apply/connectP.
elim: p {-2 4}x Hy Up Hp (connect0 (relto a r) x) =>
   [z /=-> _ _ Hz| z p IH /= z1 Hy /and3P[H1 H2 H3] /andP[Rxy Pp] Hz1].
  by exists [::].
move: H1; rewrite inE negb_or => /andP[xDz H1].
have Az : a z.
  apply: Hf; first by rewrite eq_sym.
    apply: connect_trans (connect_toW Hz1) (connect1 Rxy).
    by apply/connectP; exists p.
have Raz : x -[a]-> z.
 by apply: connect_trans Hz1 (connect_to1 Az Rxy).
have Uxp : uniq (x :: p) by rewrite /= H1.
have [p1 H1p1 H2p1] := IH _ Hy Uxp Pp Raz.
by exists (z :: p1); rewrite //= [_ \in _]Az Rxy.
Qed.

Lemma reltoI a b : relto (predI a b) r =2 relto a (relto b r).
Proof. by move=> x y; rewrite /= andbA. Qed.

End Relto.

End extra_path.



