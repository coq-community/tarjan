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
move=> x y; apply/connectP/connectP=> [] [p gp ->].
  exists (rev (belast x p)); rewrite ?rev_path //.
  by case: (lastP p) => //= ??; rewrite belast_rcons rev_cons last_rcons.
exists (rev (belast y p)); rewrite ?rev_path //.
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
  exists y , [/\ (y \in a) ==> (x == y) && (x \in a),
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

End extra_path.
