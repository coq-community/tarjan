From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop finset finfun perm fingraph path div.
Require Import bigmin extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tarjan.

Variable (V : finType) (successors : V -> seq V).
Notation edge := (grel successors).
Notation gconnect := (connect edge).
Notation infty := #|V|.+1.

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

Record env := Env {black : {set V}; stack : seq V; sccs : {set {set V}};
                   sn : nat; num: {ffun V -> nat}}.

Definition set_infty (s : pred V) f :=
  [ffun x => if s x then infty else f x].

Definition add_stack x e :=
  Env (black e) (x :: stack e) (sccs e) (sn e).+1
      (finfun [eta num e with x |-> sn e]).
Definition add_black x e :=
  Env (x |: black e) (stack e) (sccs e) (sn e) (num e).
Definition add_sccs x e :=
   let (s2, s3) := split_after x (stack e) in
   Env (x |: black e) s3 ([set y in s2] |: sccs e)
       (sn e) (set_infty (mem s2) (num e)).

Definition dfs1 (dfs : {set V} -> env -> nat * env) (x : V) e :=
    let: (m1, e1) := dfs [set y in successors x] (add_stack x e) in
    if m1 >= sn e then (infty, add_sccs x e1) else (m1, add_black x e1).

Definition dfs dfs1 dfs (roots : {set V}) e :=
  if [pick x in roots] isn't Some x then (infty, e)
  else let roots' := roots :\ x in
       let: (m1, e1) := if num e x != 0 then (num e x, e) else dfs1 x e in
       let: (m2, e2) := dfs roots' e1 in (minn m1 m2, e2).

Fixpoint tarjan_rec n : {set V} -> env -> nat * env :=
  if n is n.+1 then dfs (dfs1 (tarjan_rec n)) (tarjan_rec n)
  else fun r e => (infty, e).

Let N := #|V| * #|V|.+1 + #|V|.
Definition e0 := (Env set0 [::] set0 1 [ffun _ => 0]).
Definition tarjan := sccs (tarjan_rec N setT e0).2.

(**************************************************************)
(* Well formed environements and operations on environements. *)
(**************************************************************)

Section other_colors.

Notation gray_def := (fun e => [set x in stack e] :\: black e).
Fact gray_key : unit. Proof tt.
Definition gray := locked_with gray_key gray_def.
Lemma grayE : gray = gray_def. Proof. exact: unlock. Qed.

Notation whites_def := (fun e => ~: (gray e :|: black e)).
Fact white_key : unit. Proof tt.
Definition whites := locked_with white_key whites_def.
Lemma whitesE : whites = whites_def. Proof. exact: unlock. Qed.

End other_colors.

Lemma gray0 : gray e0 = set0.
Proof. by apply/setP=> x; rewrite grayE !inE /=. Qed.

Lemma cover0 : cover set0 = set0 :> {set V}.
Proof.
by apply/setP=> x; rewrite !inE; apply/negP=> /bigcupP[?]; rewrite inE.
Qed.

Lemma whites_blackF x e : x \in whites e -> x \in black e = false.
Proof. by rewrite whitesE grayE !inE; case: (x \in black _). Qed.

Lemma whites_stackF x e : x \in whites e -> x \in stack e = false.
Proof.
by rewrite whitesE grayE !inE andbC; case: (x \in stack _); rewrite //= orNb.
Qed.

Lemma whites_grayF x e : x \in whites e -> x \in gray e = false.
Proof. by rewrite whitesE !inE; case: (x \in gray e). Qed.

Lemma gray_stack x e : x \in gray e -> x \in stack e.
Proof. by rewrite grayE !inE andbC; case: (x \in stack _). Qed.

Lemma stack_whitesF x e : x \in stack e -> x \in whites e = false.
Proof. by rewrite whitesE grayE !inE => ->; case: (_ \in _). Qed.

Lemma black_whitesF x e : x \in black e -> x \in whites e = false.
Proof. by rewrite whitesE grayE !inE => ->. Qed.

Lemma whites_add_stack x e : whites (add_stack x e) = whites e :\ x.
Proof.
apply/setP=> y; rewrite whitesE grayE !inE /=.
by case: (_ \in _) (_ \in _) (_ == _) => [] [] [].
Qed.

Lemma gray_add_stack x e : x \in whites e ->
  gray (add_stack x e) = x |: gray e.
Proof.
move=> x_whites; apply/setP=> y; move: x_whites; rewrite whitesE grayE !inE.
by case: eqP => [->|]; case: (_ \in _) (_ \in _)=> [] [].
Qed.

Lemma stack_add_stack x e : stack (add_stack x e) = x :: stack e.
Proof. by []. Qed.

Lemma gray_add_black e x : gray (add_black x e) = gray e :\ x.
Proof. by apply/setP=> y; rewrite grayE !inE /= negb_or andbA. Qed.

Lemma whites_add_black e x : whites (add_black x e) = whites e :\ x.
Proof.
rewrite whitesE gray_add_black /=; apply/setP=> y; rewrite !inE.
by case: (_ == _) (_ \in _) (_ \in _) => [] [].
Qed.

Lemma gray_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  uniq (stack e) -> s \subset black e -> x \in gray e ->
  gray (add_sccs x e) = gray e :\ x.
Proof.
move=> /= se_uniq sb x_gray; rewrite /add_sccs grayE /=.
case: splitP sb se_uniq; first by rewrite gray_stack.
move=> s s' sb sxs'_uniq.
apply/setP=> y; rewrite !inE mem_cat mem_rcons in_cons.
have [->|] //= := altP eqP; rewrite orbC ![(y \notin _) && _]andbC.
have [|yNs' neq_yx] //= := boolP (y \in s').
by have [y_s|] //= := boolP (y \in s); rewrite (subsetP sb).
Qed.

Lemma whites_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  x \in gray e -> uniq (stack e) -> s \subset black e ->
  whites (add_sccs x e) = whites e.
Proof.
move=> /= x_gray se_uniq sb; rewrite whitesE gray_add_sccs //=.
by rewrite setUCA setUA setD1K.
Qed.

Lemma black_add_sccs e x : black (add_sccs x e) = x |: black e.
Proof. by []. Qed.

Lemma sccs_add_sccs e x :
  let s := take (index x (stack e)) (stack e) in
  sccs (add_sccs x e) = [set y in rcons s x] |: sccs e.
Proof. by []. Qed.

Lemma stack_add_sccs e x :
  let s := drop (index x (stack e)).+1 (stack e) in
  stack (add_sccs x e) = s.
Proof. by []. Qed.

(*******************)
(* Well formed env *)
(*******************)

Record wf_color e := WfEnv {
   wf_stack : stack e =i gray e :|: (black e :\: cover (sccs e));
   wf_sccs  : cover (sccs e) \subset black e;
   wf_uniq  : uniq (stack e);
}.
Hint Resolve wf_sccs.
Hint Resolve wf_uniq.

Inductive color4_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| Color4Gray of x \in gray e : color4_spec x e false true false true false
| Color4Sccs of x \in cover (sccs e) :
                       color4_spec x e true false true false false
| Color4White of x \in whites e : color4_spec x e false false false false true
| Color4BlackStack of x \in black e & x \in stack e :
                        color4_spec x e true true false false false.

Lemma color4P x e : wf_color e ->
                   color4_spec x e (x \in black e) (x \in stack e)
                              (x \in cover (sccs e))
                              (x \in gray e) (x \in whites e).
Proof.
move=> [/(_ x) s_def /subsetP /(_ x) /implyP].
move: s_def; rewrite whitesE grayE !inE.
case x_black: (_ \in black _) => /=;
case x_stack : (_ \in stack _) => /=;
case x_sccs : (_ \in cover _) => //=; do ?by constructor.
  by constructor=> //; rewrite grayE !inE x_black.
by constructor; rewrite whitesE grayE !inE x_black x_stack.
Qed.

Lemma stack_sccsF x e : wf_color e -> x \in stack e ->
  x \in cover (sccs e) = false.
Proof. by case/color4P. Qed.

Lemma gray_blackF x e : wf_color e -> x \in gray e ->
   x \in black e = false.
Proof. by case/color4P. Qed.

Lemma gray_sccsF x e : wf_color e -> x \in gray e ->
   x \in cover (sccs e) = false.
Proof. by case/color4P. Qed.

Lemma sccs_stackF x e : wf_color e ->
  x \in cover (sccs e) -> x \in stack e = false.
Proof. by case/color4P. Qed.

Lemma sccs_black x e : wf_color e -> x \in cover (sccs e) -> x \in black e.
Proof. by case/color4P. Qed.

Lemma add_stack_cwf x e : x \in whites e -> wf_color e -> wf_color (add_stack x e).
Proof.
move=> x_white e_wf; split=> /=; do ?
  by [exact: wf_sccs|rewrite whites_stackF ?wf_uniq].
move=> y; rewrite gray_add_stack // !inE.
by case: (_ == _) color4P => [] [].
Qed.

Lemma add_black_cwf x e : x \in gray e -> wf_color e -> wf_color (add_black x e).
Proof.
move=> x_gray e_wf; split => //=; last 2 first.
- by rewrite subsetU // wf_sccs // orbT.
- exact: wf_uniq.
move=> y; rewrite gray_add_black !inE.
have [->|] := altP (y =P x); case: color4P => //.
by case: color4P x_gray.
Qed.

Lemma add_sccs_wf x e :
  take (index x (stack e)) (stack e) \subset black e ->
  x \in gray e -> wf_color e -> wf_color (add_sccs x e).
Proof.
move=> new_black x_gray e_wf.
have [s_def /subsetP sccs_black s_uniq] := e_wf.
split => //=; last first.
- by rewrite (subseq_uniq (drop_subseq _ _)).
- apply/subsetP=> y; rewrite !inE.
  rewrite /cover bigcup_setU inE big_set1 !inE /= => /orP[|/sccs_black->];
    last by rewrite !orbT.
  by rewrite mem_rcons !inE; case: eqP => //= _ /(subsetP new_black).
move=> y; rewrite !inE /cover bigcup_setU inE big_set1 !inE !negb_or.
rewrite grayE ?inE //.
have [->|neq_xy] //= := altP (y =P x); rewrite ?(andbT, andbF).
  case: splitP new_black s_uniq => //=; first by rewrite gray_stack.
  move=> s1 s2 s1x_black s_uniq; rewrite gray_sccsF // andbT.
  by rewrite (uniq_catRL s_uniq) // mem_cat mem_rcons mem_head.
case: color4P; rewrite ?(andbT, andbF, orbT, orbF) //=.
  by move=> y_sccs; apply: contraTF y_sccs => /mem_drop; case: color4P.
move=> y_black; case: splitP s_uniq; first by rewrite gray_stack.
by move=> s1 s2 s_uniq y_in; apply: uniq_catRL.
Qed.

Inductive stack_spec x e : bool -> bool -> bool -> bool -> bool -> Type :=
| StackWhite of x \in whites e : stack_spec x e true false false false false
| StackStack of x \in stack e :
                       stack_spec x e false true false (x \in gray e) (x \in black e)
| StackSccs  of x \in cover (sccs e) :
                        stack_spec x e false false true false true.

Lemma stackP x e : wf_color e ->
  stack_spec x e (x \in whites e) (x \in stack e) (x \in cover (sccs e))
                              (x \in gray e) (x \in black e).
Proof.
move=> e_cwf; set xb := x \in black _; set xg := x \in gray e.
case: color4P => //.
- by move=> /gray_stack; constructor.
- by rewrite /xg /xb; case: color4P => //; constructor.
- by rewrite /xg /xb; case: color4P => //; constructor.
- by constructor.
Qed.

Lemma set_infty_eq0 (P : pred V) f x : (forall x, P x -> f x != 0) ->
  (set_infty P f x == 0) = (f x == 0).
Proof. by move=> /(_ x); rewrite ffunE; case: P => // /(_ isT)/negPf->. Qed.

Lemma set_infty_eq_infty (P : pred V) f x :
  (set_infty P f x == infty) = P x || (f x == infty).
Proof. by rewrite ffunE; case: P => //; rewrite eqxx. Qed.

Lemma set_infty_infty (P : pred V) f x : P x -> set_infty P f x = infty.
Proof. by rewrite ffunE/=; case: (P _). Qed.

Lemma set_infty_id (P : pred V) f x : ~~ P x -> set_infty P f x = f x.
Proof. by rewrite ffunE/=; case: (P _). Qed.


(*******************)
(* Well formed env *)
(*******************)

Notation precedes x y e := (index x (stack e) <= index y (stack e)).
Local Notation "x '<[' e ']=' y" := (precedes x y e)
  (at level 10, format "x  '<[' e ]=  y").

Record wf_num e := WfNum {
   wf_num0      : forall x, (num e x == 0) = (x \in whites e);
   wf_num_infty : forall x, (num e x == infty) = (x \in cover (sccs e));
   wf_num_lt    : forall x, num e x != infty -> num e x < sn e;
   wf_sn        : sn e = #|gray e :|: black e|.+1;
   wf_num_stack : {in stack e &, forall x y,  (num e x <= num e y) = (y <[e]= x)}
}.

Lemma leq_num_infty e x :  wf_num e -> (num e x) <= infty.
Proof.
move=> [_ _ /(_ x)]; case: eqP => [->|_ nLs snE _] //.
by rewrite -ltnS (leq_trans (nLs _)) // snE ltnS (leq_trans (max_card _)).
Qed.

Lemma ord_num x e : wf_num e -> @inord infty (num e x) = num e x :> nat.
Proof. by move=> e_n; rewrite inordK // ltnS leq_num_infty. Qed.

Lemma num_inftyP e x : 
  wf_num e ->
  reflect (num e x = infty) (x \in cover (sccs e)).
Proof. by case => _ <- _ _ _; apply/eqP. Qed.

Lemma sn_small e : wf_num e -> sn e <= infty.
Proof. by move=> e_nwf; rewrite wf_sn// ltnS max_card. Qed.

Lemma num_stackP e x : wf_color e -> wf_num e ->
   (x \in stack e) = (0 < num e x < sn e).
Proof.
move=> e_cwf e_nwf; symmetry; rewrite lt0n wf_num0//; case: stackP => //=.
  by move=> x_stack; rewrite wf_num_lt // wf_num_infty//; case: stackP x_stack.
by rewrite -wf_num_infty => // /eqP->; rewrite ltnNge sn_small.
Qed.

Lemma add_stack_nwf x e : x \in whites e -> wf_color e ->
  wf_num e -> wf_num (add_stack x e).
Proof.
move=> x_w wf_c wf_e.
have [nEw nEc nLs snE pE] := wf_e.
split => [y|y|y||y z]; rewrite ?ffunE ?inE /=.
- rewrite whites_add_stack; case: (y =P x) => [->|/eqP yDx]; rewrite !inE.
    by rewrite snE eqxx.
  by rewrite nEw (negPf yDx).
- case: (y =P x) => [->|//].
  rewrite eqn_leq snE [#|V|.+1 <= _]leqNgt !ltnS.
  rewrite -(cardsC (gray e :|: black e)) (@cardsD1 _ x (~: _)) !inE.
  case: color4P x_w => //= x_w.
  by rewrite addnS ltnS leq_addr andbF.
- by case: (y == x) => // nE; rewrite ltnS ltnW // nLs.
- rewrite gray_add_stack // snE.
  rewrite [in RHS](cardD1 x) !inE eqxx /=; congr (_.+2).
  apply: eq_card => z; rewrite !inE.
  by case: (z =P x) => //= ->; case: color4P x_w.
- rewrite ![_ == x]eq_sym.
  do 2 case: eqP => //=.
  * by rewrite leqnn.
  * by rewrite leqNgt num_stackP => // _ _ _ /andP[_ ->].
  * by rewrite num_stackP => // _ _ /andP[_ nLs1]; rewrite ltnW.
  * by move=> *; apply: pE.
Qed.

Lemma add_black_nwf x e : x \in gray e -> wf_color e ->
   wf_num e -> wf_num (add_black x e).
Proof.
move=> x_g wf_c wf_e.
have [nEw nEc nLs snE pE] := wf_e.
split => //= [y|].
  by rewrite whites_add_black !inE nEw; case: eqP => // ->; case: color4P x_g.
by rewrite gray_add_black setUA /= [_ :|: [set x]]setUC setD1K.
Qed.

Lemma add_sccs_nwf x e :
   take (index x (stack e)) (stack e) \subset black e ->
   x \in gray e -> wf_color e ->
   wf_num e -> wf_num (add_sccs x e).
Proof.
move=> tsb x_g wf_c wf_n.
have [nEw nEc nLs snE pE] := wf_n.
split => [y|y|y||y z]; rewrite ?ffunE ?(inE) /=.
- rewrite whites_add_sccs ?wf_uniq // mem_rcons inE.
  case: (y =P x)=> [->|_] /=; first by case: color4P x_g.
  case: (boolP (_ \in _))=> [/(subsetP tsb)|_].
    by case: color4P x_g.
  exact: nEw.
- set r := rcons _ _.
  rewrite [cover _]bigcup_setU /= inE.
  rewrite big_set1 inE.
  by case:  (_ \in _); [rewrite eqxx | exact: nEc].
- case: (boolP (_ \in _)); rewrite ?eqxx => // _; exact: nLs.
- by rewrite gray_add_sccs ?wf_uniq // setUA /= [_ :|: [set x]]setUC setD1K.
- case: (splitP (gray_stack x_g)) tsb pE (wf_uniq wf_c) =>
    l1 l2 tsb pE Ul yIl2 zIl2.
  have yNIr : y \notin rcons l1 x by rewrite -(uniq_catRL Ul) // mem_cat orbC yIl2.
  have zNIr : z \notin rcons l1 x by rewrite -(uniq_catRL Ul) // mem_cat orbC zIl2.
  rewrite (negPf yNIr) (negPf zNIr) pE ?(mem_cat, yIl2, zIl2, orbT) //.
  by rewrite !index_cat !ifN // leq_add2l.
Qed.

Lemma stack_neq_infty e x : wf_color e -> wf_num e ->
   x \in stack e -> (num e) x != infty.
Proof. by move=> e_cwf e_nwf x_stack; rewrite wf_num_infty// stack_sccsF. Qed.

Definition noblack_to_white e :=
  forall x, x \in black e -> [disjoint successors x & whites e].

Record wf_graph e := WfGraph {
  wf_gray_to_stack : {in gray e & stack e, forall x y,
         (num e x <= num e y) -> gconnect x y};
  wf_stack_to_gray : forall y, y \in stack e ->
                      exists x, [/\ x \in gray e,
     (num e x <= num e y) & gconnect y x]
  }.

Definition access_to e (roots : {set V}) :=
  {in gray e & roots, forall x y, gconnect x y}.

Definition black_gsccs e := [set scc in gsccs | scc \subset black e].

Record invariants (e : env) := Invariants {
  inv_wf_color : wf_color e;
  inv_wf_num   : wf_num e;
  inv_wf_graph : wf_graph e;
  wf_noblack_towhite : noblack_to_white e;
  inv_sccs : sccs e = black_gsccs e;
}.

Record pre_dfs (roots : {set V}) (e : env) := PreDfs {
  pre_access_to : access_to e roots;
  pre_invariants : invariants e
}.

Lemma add_stack_gwf e w :
  access_to e [set w] -> wf_color e -> wf_num e -> w \in whites e -> wf_graph e ->
  wf_graph (add_stack w e).
Proof.
move=> gray_to e_cwf e_nwf w_white [gs sg]; split.
  rewrite gray_add_stack //= => x y. rewrite !ffunE !inE /=.
  have [-> _|neq_xw /= x_gray] := altP eqP;
  have [-> _|neq_yw /= y_stack]// := altP eqP.
  - by rewrite leqNgt wf_num_lt// stack_neq_infty.
  - by move=> _; rewrite gray_to ?inE.
  - exact: gs.
move=> y; rewrite inE => /predU1P [->|].
  by exists w; rewrite ?gray_add_stack ?inE ?eqxx.
move=> y_stack; have /sg [x [x_gray le_xy y_to_x]] := y_stack.
exists x; split=> //; first by rewrite gray_add_stack // inE x_gray orbT.
rewrite /= !ffunE/= !ifN//; apply: contraTneq w_white => <-;
by case: color4P y_stack x_gray.
Qed.

Lemma add_stack_pre e w :
  access_to e [set w] -> wf_color e -> w \in whites e -> wf_graph e ->
  access_to (add_stack w e) [set x in successors w].
Proof.
move=> gray_to e_wf w_white e_gwf.
move=> x y; rewrite gray_add_stack // !inE => /predU1P [->|].
  by move=> y_succ_w; rewrite connect1.
move=> /gray_to x_to_y y_succ_w.
by rewrite (connect_trans _ (connect1 y_succ_w)) // x_to_y ?inE.
Qed.

Lemma nth_belast (z : V) p i :
  nth z (belast z p) i = if i < size p then nth z (z :: p) i else z.
Proof.
rewrite lastI nth_rcons size_belast; have [i_lt|i_ge] //= := ltnP.
by rewrite nth_default // size_belast.
Qed.

Lemma nth_belast_small (z : V) p i : i < size p ->
  nth z (belast z p) i = nth z (z :: p) i.
Proof. by move=> i_lt; rewrite nth_belast i_lt. Qed.

Notation wedge e := (relfrom (pred_of_set (whites e)) edge).
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
  [&&  gray e1 == gray e2,
       black e1 \subset black e2,
       sccs e1 \subset sccs e2,
       [forall x in stack e1, num e2 x == num e1 x] &
       [exists n : 'I_infty, stack e1 == drop n (stack e2)]].

Lemma subenv_gray e1 e2 : subenv e1 e2 -> gray e2 = gray e1.
Proof. by move=> /and4P [/eqP]. Qed.

Lemma subenv_black e1 e2 : subenv e1 e2 -> black e1 \subset black e2.
Proof. by move=> /and4P []. Qed.

Lemma subenv_sccs e1 e2 : subenv e1 e2 -> sccs e1 \subset sccs e2.
Proof. by move=> /and4P []. Qed.

Lemma subenv_num e1 e2 : subenv e1 e2 ->
  {in stack e1, forall x, num e2 x = num e1 x}.
Proof. by case/and5P=> _ _ _ /forall_inP H _ x *; apply/eqP/H. Qed.

Lemma subenv_sn e1 e2 : 
  wf_num e1 -> wf_num e2 -> subenv e1 e2 -> sn e1 <= sn e2.
Proof.
move=> /wf_sn-> /wf_sn-> /and5P[/eqP<-] H _ _ _.
by rewrite ltnS; apply/subset_leq_card/setUS.
Qed.

Lemma subenvN_subproof e1 e2 : subenv e1 e2 ->
  {n : nat | stack e1 = drop n (stack e2)}.
Proof. by move=> /and5P [_ _ _ _ /existsP /sigW[n /eqP]]; exists n. Qed.

Definition subenvN e1 e2 :=
  if subenv e1 e2 =P true isn't ReflectT e12 then 0
  else projT1 (subenvN_subproof e12).

Lemma subenv_drop e2 e1 : subenv e1 e2 ->
  stack e1 = drop (subenvN e1 e2) (stack e2).
Proof. by rewrite /subenvN; case: eqP => // ??; case: subenvN_subproof. Qed.

Lemma subenv_take e1 e2 : wf_color e2 -> subenv e1 e2 ->
  take (subenvN e1 e2) (stack e2) \subset black e2.
Proof.
set n := subenvN e1 e2; move=> e2_wf e12; apply/subsetP=> x x_p2.
suff: (x \in stack e2) && (x \notin gray e2) by case: color4P.
rewrite (mem_take x_p2) (subenv_gray e12) /=.
apply: contraTN isT => /gray_stack.
have := wf_uniq e2_wf; rewrite -[stack e2](cat_take_drop n) => s12_uniq.
by rewrite (subenv_drop e12) (uniq_catRL s12_uniq) ?x_p2 // mem_cat x_p2.
Qed.

Lemma uniq_ex_drop (s1 s2 : seq V) :
   uniq s2 -> (exists s, s2 = s ++ s1) ->
   exists n : 'I_infty, s1 = drop n s2.
Proof.
move=> s2_uniq [s s2_def]; exists (inord (size s)).
rewrite s2_def inordK ?drop_cat ?ltnn ?subnn ?drop0 // ltnS.
rewrite -(card_uniqP _) ?max_card //.
by move: s2_uniq; rewrite s2_def cat_uniq => /andP[].
Qed.

Lemma subenv_stackP e1 e2 : wf_color e2 -> subenv e1 e2 ->
  exists2 s, stack e2 = s ++ stack e1 & s \subset (black e2).
Proof.
move=> e2_wf e12; pose n := subenvN e1 e2; exists (take n (stack e2)).
  by rewrite (subenv_drop e12) // cat_take_drop.
by rewrite subenv_take.
Qed.

Lemma subenv_whites e1 e2 : subenv e1 e2 -> whites e2 \subset whites e1.
Proof.
by move=> e12; rewrite whitesE setCS (subenv_gray e12) setUS ?subenv_black.
Qed.

Lemma new_whites e1 e2 : wf_color e2 -> subenv e1 e2 ->
   whites e1 :\: whites e2 = black e2 :\: black e1.
Proof.
move=> e2_wf e12; rewrite whitesE -(subenv_gray e12) setDE setCK setIC -setDE.
rewrite setDUl setDE setCU setIA setICr set0I set0U.
rewrite setDUr (setIidPr _) // [_ :\: gray _](setDidPl _) ?subsetDl //.
by apply/pred0P => y /=; case: color4P.
Qed.

Lemma subenv_refl : reflexive subenv.
Proof.
move=> e; rewrite /subenv eqxx !subxx /=.
apply/andP; split; first by apply/forall_inP=> *.
by apply/existsP; exists ord0; rewrite drop0.
Qed.
Hint Resolve subenv_refl.

Lemma subenvee e : subenv e e. Proof. exact: subenv_refl. Qed.
Hint Resolve subenvee.

Lemma subenv_trans e2 e1 e3 : wf_color e2 -> wf_color e3 ->
  subenv e1 e2 -> subenv e2 e3 -> subenv e1 e3.
Proof.
move=> e2_wf e3_wf e12 e23; rewrite /subenv.
rewrite (subenv_gray e23) (subenv_gray e12) eqxx.
rewrite (subset_trans (subenv_black e12)) ?subenv_black //.
rewrite (subset_trans (subenv_sccs e12)) ?subenv_sccs //=.
apply/andP; split.
  apply/forall_inP=> x xIse1; apply/eqP.
  rewrite -(subenv_num e12) // (subenv_num e23) //.
  by case: (subenv_stackP e2_wf e12) => l -> _; rewrite mem_cat xIse1 orbT.
apply/'exists_eqP; apply: uniq_ex_drop; first exact: wf_uniq.
case: (subenv_stackP _ e23) => // s2 -> _.
case: (subenv_stackP _ e12) => // s1 -> _.
by exists (s2 ++ s1); rewrite catA.
Qed.

Lemma subenv_gray_le e1 e2 x y : subenv (add_stack x e1) e2 ->
   wf_color e2 -> wf_num e2 -> y \in gray e2 -> num e2 y <= num e2 x.
Proof.
move=> subxe12 e2_cwf e2_nwf y_gray.
case: (@subenv_stackP (add_stack x e1) e2) => // s s_def sb.
rewrite wf_num_stack //; last 2 first.
- by case: color4P y_gray.
- by rewrite s_def mem_cat /= mem_head orbT.
rewrite s_def !index_cat.
rewrite !ifN /=; first by rewrite leq_add2l eqxx; case: ifPn => //=.
   by apply: contraTN y_gray => /(subsetP sb); case: color4P.
have := wf_uniq e2_cwf; rewrite s_def => /(@uniq_catRL _ x).
by rewrite mem_cat mem_head orbT -s_def wf_uniq// => <-.
Qed.

Lemma subenv_stack_gt e1 e2 x y : subenv e1 e2 ->
   wf_num e1 -> wf_color e1 -> wf_color e2 -> wf_num e2 -> x \in stack e1 ->
   y \in stack e2 -> y \notin stack e1 -> num e2 x < num e2 y.
Proof.
move=> sube12 e1_nwf e1_cwf e2_cwf e2_nwf x_stack1 y_stack2 yNstack1.
case: (@subenv_stackP e1 e2) => // s s_def _.
rewrite ltnNge wf_num_stack //; last first.
  by rewrite s_def mem_cat x_stack1 orbT.
rewrite s_def !index_cat; have ys : y \in s.
  by have := y_stack2; rewrite s_def mem_cat (negPf yNstack1) orbF.
rewrite ifN; last first.
  have := wf_uniq e2_cwf; rewrite s_def => /(@uniq_catRL _ x).
  by rewrite mem_cat x_stack1 orbT -s_def wf_uniq// => <-.
by rewrite ifT// -ltnNge (@leq_trans (size s))// ?index_mem// leq_addr.
Qed.

Record post_dfs (roots : {set V}) (e e' : env) (m : nat) := PostDfs {
  post_invariants : invariants e';
  post_subenv : subenv e e';
  post_whites : whites e' = whites e :\: \bigcup_(x in roots) wreach e x;
  post_num : m = \min_(y in \bigcup_(x in roots) wreach e x)
                      @inord infty (num e' y);
}.

Definition dfs1_correct (dfs1 : V -> env -> nat * env) x e :=
  (x \in whites e) -> pre_dfs [set x] e ->
  let (m, e') := dfs1 x e in post_dfs [set x] e e' m.

Definition dfs_correct (dfs : {set V} -> env -> nat * env) roots e :=
  pre_dfs roots e -> let (m, e') := dfs roots e in post_dfs roots e e' m.

Lemma pre_dfs_subroots (roots roots' : {set V}) e : roots' \subset roots ->
  pre_dfs roots e -> pre_dfs roots' e.
Proof.
move=> sub_roots [to_roots [e_wf e_gwf black_sccs Nbw]]; split=> //.
by move=> x x_gray y y_roots'; rewrite to_roots //; apply: subsetP y_roots'.
Qed.

Lemma subND1 (T : finType) (A : {set T}) (x : T) : x \notin A -> A :\ x = A.
Proof. by move=> xNA; rewrite (setDidPl _) ?disjoints1. Qed.

Lemma dfs_is_correct dfs1 dfsrec (roots : {set V}) e :
  (forall x, x \in roots -> dfs1_correct dfs1 x e) ->
  (forall x, x \in roots -> forall e1, whites e1 \subset whites e ->
         dfs_correct dfsrec (roots :\ x) e1) ->
  dfs_correct (dfs dfs1 dfsrec) roots e.
Proof.
move=> dfs1_is_correct dfs_is_correct; rewrite /dfs_correct /dfs.
case: pickP => [x|no_roots]; last first.
  have roots0 : roots = set0 by apply/setP=> y; rewrite no_roots inE.
  move=> [gto_roots [e_wf e_gwf black_sccs]].
  by split; rewrite ?roots0 ?big_set0 ?setD0.
move=> x_root; have := dfs_is_correct _ x_root; rewrite /dfs_correct.
move=> dfsrec_correct pre.
have [to_roots [e_wf e_gwf Nbw black_sccs]] := pre.
have e_uniq := @wf_uniq _ e_wf.
rewrite wf_num0 //; have [xw|xNw]/= := boolP (x \in _); last first.
  move: dfsrec_correct => /(_ _ (subxx _)).
  case: (dfsrec _ _) => [m2 e1].
  case; first exact: (pre_dfs_subroots (subD1set _ _)).
  move=> [e1_wf e1_nwf e1_gwf Nbw1 sccs_e1] sube1 whites1 m2_min.
  have [//|s1 s1_def sb] := subenv_stackP _ sube1.
  have e1_uniq := wf_uniq e1_wf.
  split=> //.
    rewrite -(setD1K x_root) big_setU1 ?setD11 //=.
    by rewrite -setDDl whites1 Nwreach ?(subND1 xNw).
  rewrite -(setD1K x_root) big_setU1 ?setD11 // bigmin_setU /= m2_min.
  congr (minn _ _); rewrite Nwreach // big_set1 ord_num //.
  case: stackP xNw => // [x_stack|x_sccs] _; first exact/esym/subenv_num.
    rewrite ?(num_inftyP _ _ _) //.
    by apply: (subsetP (subset_cover (subenv_sccs _))) x_sccs.
have := dfs1_is_correct _ x_root; rewrite /dfs1_correct.
case: (dfs1 _ _) => [m1 e1] post_dfs1.
move: dfsrec_correct => /(_ e1).
case: (dfsrec _ _) => [m2 e2] post_dfs {dfs1_is_correct dfs_is_correct}.
have := post_dfs1 xw (pre_dfs_subroots _ pre).
rewrite sub1set x_root => /(_ isT) {post_dfs1}.
case=> [[e1_wf e1_cwf e1_gwf Nbw1 sccs_e1] sube1 whites1 m1_min].
have [//|s1 s1_def s1b] := subenv_stackP _ sube1.
have e1_uniq := wf_uniq e1_wf.
rewrite big_set1 in whites1 m1_min.
case: post_dfs.
- by rewrite subenv_whites.
- split=> // y z; rewrite grayE !inE s1_def mem_cat.
  case: (y \in s1) (subsetP s1b y) => //= [->//|_ /andP[yNb ys]].
  move=> /andP[_ z_roots]; rewrite to_roots // grayE !inE.
  rewrite ys andbT; apply: contraNN yNb; apply/subsetP.
  by rewrite subenv_black.
move=> [e2_wf e2_cwf e2_gwf Nbw2 sccs_e2] sube2 whites2 m2_min.
have [//|s2 s2_def s2b] := subenv_stackP _ sube2.
have e2_uniq := wf_uniq e2_wf.
have split_wreach : \bigcup_(y in roots) wreach e y =
     wreach e x :|: \bigcup_(y in roots :\ x) wreach e1 y.
  rewrite -{1}(setD1K x_root) big_setU1 ?setD11 //=; apply/setP => y.
  rewrite !in_setU; have [//|/=Nxy] := boolP (_ \in wreach _ _).
  apply/bigcupP/bigcupP=> - [] z z_roots zy; exists z => //; last first.
    rewrite !inE in zy *; apply: connect_sub zy => u v /= /andP [uw uv].
    by rewrite connect1 //= uv andbT; apply: subsetP uw; rewrite subenv_whites.
  apply: contraTT isT => Nzy; move: zy; rewrite !inE in  Nxy Nzy *.
  move=> /(connect_from (predC (connect (wedge e) x))) /= [t] /= [xtxy zt ty].
  move: zt; rewrite (@eq_connect _ _ (wedge e1)); last first.
    by move=> u v /=; rewrite !inE /= whites1 !inE andbA.
  case: (altP eqP) xtxy => /= [<-|neq_yt]; first by rewrite (negPf Nzy).
  by rewrite implybF negbK => /connect_trans /(_ ty); rewrite (negPf Nxy).
split => //; first exact: subenv_trans sube2.
  by rewrite whites2 whites1 split_wreach setDDl.
rewrite m1_min m2_min split_wreach bigmin_setU /=.
congr (minn (val _) _); apply: eq_bigr => y xy; apply/val_inj=> /=.
rewrite !ord_num //.
have /orP[ys|ysccs] : (y \in stack e1) || (y \in cover (sccs e1)).
+ suff: y \notin whites e1 by case: color4P.
  by rewrite whites1 inE xy.
+ exact/esym/subenv_num.
rewrite ?(num_inftyP _ _ _) //.
by apply: (subsetP (subset_cover (subenv_sccs _))) ysccs.
Qed.

Lemma dfs1_is_correct dfs (x : V) e :
  (dfs_correct dfs [set y | edge x y] (add_stack x e)) ->
  dfs1_correct (dfs1 dfs) x e.
Proof.
rewrite /dfs1 /dfs1_correct /dfs_correct; case: (dfs _ _) => m1 e1.
move=> post_dfs; set m := sn e.
move=> x_white [access_to_x [e_wf e_cwf e_gwf Nbw black_sccs]].
have e_uniq := @wf_uniq _ e_wf.
case: post_dfs => //=.
  split => //.
    move=> y z; rewrite gray_add_stack // => /setU1P [->|y_gray];
    rewrite inE => /(@connect1 _ edge) //.
    by apply/connect_trans/access_to_x; rewrite ?set11.
    split=> //; do?[exact: add_stack_cwf|exact: add_stack_gwf|exact: add_stack_nwf].
  move=> y /Nbw; rewrite whites_add_stack.
  rewrite ![[disjoint successors _ & _]]disjoint_sym.
  by apply/disjoint_trans/subsetDl.
move=> [e1_wf e1_cwf e1_gwf Nbw1 black_sccs1] sube1 whites1 m_min.
have [//|s s_def sb] := subenv_stackP _ sube1.
set s2 := rcons s x.
have e1_uniq := @wf_uniq _ e1_wf.
have xe_uniq : uniq (x :: stack e).
  by have := e1_uniq; rewrite s_def cat_uniq => /and3P [].
have x_stack : x \in stack e1 by rewrite s_def mem_cat mem_head orbT.
have x_gray : x \in gray e1.
   by rewrite (subenv_gray sube1) gray_add_stack ?setU11.
have sx_subscc : is_subscc [set y in rcons s x].
  apply: (@is_subscc1 x); first by rewrite inE mem_rcons mem_head.
  move=> y; rewrite !inE mem_rcons in_cons => /predU1P [->//|y_s]; split.
    apply: (@wf_gray_to_stack e1) => //; first by rewrite s_def mem_cat y_s.
    rewrite wf_num_stack //s_def; last by rewrite mem_cat y_s.
    rewrite !index_cat y_s ifN.
      by rewrite (leq_trans (index_size _ _) (leq_addr _ _)).
    by apply/negP=> /(subsetP sb); case: color4P x_gray.    
  have [] := @wf_stack_to_gray _ e1_gwf y; first by rewrite s_def mem_cat y_s.
  move=> z [z_gray rank_z] /connect_trans; apply.
  by rewrite (@wf_gray_to_stack e1) //; rewrite (subenv_gray_le sube1).
have wreachex : wreach e x = x |: \bigcup_(y in [set y in successors x])
                          wreach (add_stack x e) y.
  rewrite /wreach whites_add_stack.
  apply/eqP; rewrite eqEsubset subUset sub1set mem_wreach /=.
  apply/andP; split; last first.
    apply/bigcupsP => y; rewrite inE => xy; apply/subsetP=> z; rewrite !inE.
    move=> /connectP [p]; rewrite path_from => /andP[yp pw]->.
    apply/connectP; exists (y :: p); rewrite // path_from /= xy yp topredE /=.
    by rewrite x_white (sub_all _ pw) // => t; rewrite topredE inE => /andP[].
  apply/subsetP=> y; rewrite !inE.
  move=> /connectP [_] /shortenP [p exp /andP[xNp _] _ -> {y}].
  case: p => [|y p /=] //= in exp xNp *; first by rewrite eqxx.
  move: exp xNp; rewrite in_cons -andbA => /and3P[_ xy eyp] /norP[neq_xy xNp].
  apply/orP; right; apply/bigcupP; exists y; rewrite ?inE //=; apply/connectP.
  exists p => //; elim: p => [|z p ihp] //= in y {xy} neq_xy eyp xNp *.
  move: eyp xNp; rewrite in_cons -andbA => /and3P[yw yz ezp] /norP[neq_yz xNp].
  by rewrite !inE eq_sym neq_xy yw yz /= ihp.
have m2_min : minn m m1 = \min_(y in wreach e x) @inord infty (num e1 y).
  rewrite wreachex bigmin_setU big_set1 //= /m -m_min; congr (minn _ _).
  rewrite (subenv_num sube1) ?mem_head//= ffunE/= eqxx.
  by rewrite inordK// ltnS sn_small.
have succ_whiteF z : z \in successors x -> z \in whites e1 = false.
  move=> z_successor; apply/negbTE.
  rewrite whites1 whites_add_stack !inE !negb_and !negbK.
  by rewrite (appP bigcupP idP) //; exists z; rewrite !inE.
case: ltnP => [m1_small|m1_big] //=.
  rewrite (minn_idPr _) 1?ltnW// in m2_min.
  have [x1 num_x1 x_to_x1] : exists2 x1, num e1 x1 = m1 & gconnect x x1.
      have [] := @eq_bigmin_cond _ _ (pred_of_set (wreach e x))
                          (fun y => @inord infty (num e1 y)).
        by apply/card_gt0P; exists x; rewrite mem_wreach.
      move=> y; rewrite !inE=> xy /(congr1 val)/=.
      rewrite -m2_min ord_num // => m1_eq; exists y => //.
      by apply: connect_sub xy => u v /= /andP [_]; apply: connect1.
  have [x' [num_x' x'_gray x_to_x' ]] : exists x',
    [/\ num e1 x' < num e1 x, x' \in gray e1 & gconnect x x'].
    (* move: m1_small; rewrite -{}num_x1 => num_x1. *)
    have x1_stack : x1 \in stack e1.
      rewrite num_stackP// num_x1 (leq_trans m1_small) ?andbT.
        rewrite m2_min (_ : 1 = @inord infty 1); last by rewrite inordK.
        apply/bigmin_geqP => i.
        rewrite ord_num // inordK//= lt0n wf_num0//.
        rewrite wreachex !inE => /predU1P[->|].
          by case: color4P x_stack. (* TODO: add this to ssrdone *)
        by rewrite whites1 inE => ->.
      apply: leq_trans (subenv_sn _ _ sube1); rewrite ?leqW //.
      by apply: add_stack_nwf.
    have [z [z_gray num_z y_to_z]] := wf_stack_to_gray e1_gwf x1_stack.
    exists z; split=> //; rewrite 2?inE ?z_gray ?andbT.
    - rewrite (leq_ltn_trans num_z)// num_x1 (leq_trans m1_small)// /m.
      by rewrite (subenv_num sube1) ?mem_head //= ffunE/= eqxx. (* lemma *)
    - by rewrite (connect_trans x_to_x1).
  have neq_x'x : x' != x by apply: contraTneq num_x' => ->; rewrite -ltnNge.
  split=> //.
  - split=> //; first exact: add_black_cwf.
    + split => //.
      * move=> y /=.
        by rewrite whites_add_black wf_num0// subND1//; case: color4P x_gray.
      * by move=> y /=; rewrite wf_num_infty.
      * by move=> y /= /wf_num_lt; apply.
      * by rewrite /= gray_add_black wf_sn// setUCA setUA setD1K.
      * by move=> y z /= y_stack z_stack; rewrite wf_num_stack.
    + split => //.
        move=> y z /=; rewrite gray_add_black => y_gray z_stack.
        apply: wf_gray_to_stack => //; apply: subsetP y_gray.
        by rewrite subD1set.
      move=> y /= y_stack; rewrite gray_add_black.
      have [z] // := wf_stack_to_gray e1_gwf y_stack.
      have [->{z} [_ rank_x y_to_x]|] := eqVneq z x; last first.
        move=> neq_zx [z_gray rank_z y_to_z].
        by exists z; split=> //; rewrite 2!inE neq_zx.
      exists x'; split; rewrite 2?inE ?x'_gray ?andbT //.
      - by rewrite (leq_trans _ rank_x) 1?ltnW // rkx.
      - by rewrite (connect_trans y_to_x).
    + move=> y; rewrite !inE whites_add_black.
      move=> /predU1P [->{y}|y_black]; last first.
        apply/pred0P=> z /=; rewrite 2!inE.
        have /pred0P /(_ z) /= := Nbw1 _ y_black.
        by apply: contraFF=> /and3P[->_->].
      apply/pred0P=> z /=; rewrite 2!inE.
      by have [/succ_whiteF->|]:= boolP (z \in successors x); rewrite ?andbF.
    + rewrite /= black_sccs1; apply/setP=> scc; rewrite !inE /=.
      have [scc_gsccs|] //= := boolP (scc \in gsccs).
      apply/idP/idP; first by move=> /subset_trans; apply; rewrite subsetU1.
      move=> /subsetP scc_sub; apply/subsetP => y y_scc.
      have /setU1P [eq_yx|//] := scc_sub y y_scc.
      rewrite eq_yx in y_scc.
      have x'_scc : (x' \in scc).
        rewrite -(def_scc _ y_scc) // mem_scc /= x_to_x' /=.
        by rewrite (wf_gray_to_stack e1_gwf) // ltnW.
      have /scc_sub := x'_scc.
      rewrite !inE (negPf neq_x'x) /=.
      by case: color4P x'_gray.
  - apply/and5P; split => //=.
    + rewrite gray_add_black (subenv_gray sube1) gray_add_stack ?setU1K //.
      by rewrite whites_grayF.
    + by rewrite (subset_trans (subenv_black sube1)) // subsetUr.
    + by rewrite -[sccs e]/(sccs (add_stack x e)) subenv_sccs.
    + apply/forall_inP => y y_stack; apply/eqP.
      rewrite (subenv_num sube1)/= ?in_cons ?y_stack ?orbT// ffunE/=.
      by rewrite ifN//; apply: contraTneq xe_uniq => <- /=; rewrite y_stack.
    + apply/'exists_eqP/uniq_ex_drop; rewrite // s_def /=.
      by exists (rcons s x); rewrite cat_rcons.
  - rewrite whites_add_black big_set1 wreachex whites1 whites_add_stack.
    by rewrite !setDDl setUA setUAC setUid.
  - by rewrite m2_min; congr val; apply: eq_bigl=> y; rewrite /= big_set1.
(* post conditions *)
move: m2_min; rewrite (minn_idPl _) // => sn_min.
have numx_le y : y \in wreach e x -> num e1 y >= num e1 x.
  move=> xy; rewrite (@leq_trans m) //; last first.
    by rewrite sn_min -ord_num// geq_bigmin_cond.
  by rewrite (subenv_num sube1) ?mem_head//= ffunE/= eqxx. (*TODO: lemma*)
have scc_max : scc_of x \subset [set y in s2].
  apply/subsetP=> y; rewrite inE=> y_sccx; apply: contraTT isT => yNs2.
  have xy : gconnect x y by have := y_sccx; rewrite mem_scc /= => /andP[].
  have x_s2 : x \in s2 by rewrite mem_rcons mem_head.
  have /(connect_from (mem s2)) /= [y' []] := xy.
  rewrite (negPf yNs2) andbF implybF => [y'Ns2].
  have neq_y'x : y' != x by apply: contraNneq y'Ns2 => ->.
  move=> /connect1r [] // x' xx's2 /= /andP [x'_s2 x'y'] y'y.
  have xx' : gconnect x x'.
    by apply: connect_sub xx's2 => u v /= /andP[_]; apply: connect1.
  have /or3P[] : [|| y' \in whites e1, y' \in cover (sccs e1)
                   | y' \in stack e1] by case: color4P.
  - move: x'_s2; rewrite mem_rcons in_cons => /predU1P [eq_x'x|x_s].
      by rewrite succ_whiteF -?eq_x'x.
    have /(_ x') := Nbw1; rewrite (subsetP sb) => // /(_ isT).
    by move=> /pred0P /(_ y') /=; rewrite [_ \in _]x'y' /= => ->.
  - move=> /bigcupP [scc'].
    rewrite black_sccs1 inE => /andP[scc'_gsccs scc'_black].
    move=> /def_scc - /(_ scc'_gsccs) eq_scc'; rewrite -eq_scc' in scc'_black.
    have : x \in scc_of y'.
      have:= y_sccx; rewrite !mem_scc /= andbC => /andP[yx _].
      by rewrite (connect_trans y'y) //= (connect_trans xx') //= connect1.
    by move=> /(subsetP scc'_black); case: color4P x_gray.
  - rewrite s_def -cat_rcons mem_cat (negPf y'Ns2) /= => y'_stack.
    have xNstack: x \notin stack e.
      rewrite -(@uniq_catLR _ x s2) ?mem_cat ?x_s2 //.
      by rewrite cat_rcons -s_def wf_uniq.
    have x'Nstack: x' \notin stack e.
      rewrite -(@uniq_catLR _ x' s2) ?mem_cat ?x'_s2 //.
      by rewrite cat_rcons -s_def wf_uniq.
    have s2_whites: {subset s2 <= whites e}.
      move=> z z_s2; have: z \notin cover (sccs e).
        apply/negP=> /(subsetP (subset_cover (subenv_sccs sube1))).
        suff: z \in stack e1 by case: color4P.
        by rewrite s_def -cat_rcons mem_cat z_s2.
      wlog: / z \in stack e by case: color4P; do ?[exact|move=>?].
      have us2e : uniq (s2 ++ stack e) by rewrite cat_rcons -s_def.
      by rewrite (uniq_catRL us2e) ?mem_cat ?z_s2.
    suff /numx_le : y' \in wreach e x.
      rewrite !(subenv_num sube1) ?mem_head//?in_cons ?y'_stack ?orbT//=.
      rewrite !ffunE/= eqxx (negPf neq_y'x) leqNgt wf_num_lt//.
      by rewrite wf_num_infty//; case: color4P y'_stack.
    rewrite !inE (@connect_trans _ _ x') //; last first.
       by rewrite connect1 /= ?s2_whites.
    apply: connect_sub xx's2 => u v /= /andP[/s2_whites uw uv].
    by rewrite connect1 /= ?uw.
have g1Nx : gray e1 :\ x = gray e.
  by rewrite (subenv_gray sube1) gray_add_stack // setU1K // whites_grayF.
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
  + split=> //=. (* TODO: generalize *)
    * move=> y; rewrite whites_add_sccs// ?take_s//.
      rewrite set_infty_eq0 ?wf_num0//= => z; rewrite mem_rcons in_cons wf_num0//.
      by move=> /predU1P[->|/(subsetP sb)]; case: color4P x_stack.
    * move=> y; rewrite !take_s.
      rewrite /cover big_setU1/= -/(cover _).
        by rewrite set_infty_eq_infty wf_num_infty// !inE.
      suff: ~~ ([set y0 in rcons s x] \subset cover (sccs e1)).
        apply: contra => sx_in.
        by rewrite /cover (big_setD1 _ sx_in) /= subsetUl.
      apply: contraTN isT => /subsetP /(_ x); rewrite inE mem_rcons in_cons eqxx/=.
      by case: color4P x_gray => //= ??; apply.
    * move=> y /=; rewrite !take_s set_infty_eq_infty/= negb_or => /andP[ysx nNinfty].
      by rewrite set_infty_id ?ysx// wf_num_lt.
    * by rewrite gray_add_sccs// ?take_s// setUCA setUA setD1K // wf_sn.
    * rewrite drop_s take_s// => z t z_stack t_stack.
      rewrite !set_infty_id/=; last 2 first.
      - move: e1_uniq; rewrite s_def stack_add_stack -cat_rcons.
        by move=>/uniq_catRL<- //; rewrite mem_cat orbC t_stack.
      - move: e1_uniq; rewrite s_def stack_add_stack -cat_rcons.
        by move=>/uniq_catRL<- //; rewrite mem_cat orbC z_stack.
      rewrite !(subenv_num sube1) ?ffunE/=;
        do ?by rewrite in_cons ?t_stack ?z_stack orbT.
      rewrite !ifN ?wf_num_stack//.
      - move: xe_uniq; rewrite /= andbC => /andP[_].
        by apply: contra => /eqP<-.
      - move: xe_uniq; rewrite /= andbC => /andP[_].
        by apply: contra => /eqP<-.
  + split=> //=; rewrite ?gray_add_sccs ?stack_add_sccs ?take_s ?drop_s// ?g1Nx.
    * move=> y z y_g z_s; rewrite !ffunE; rewrite !ifN /=; last 2 first.
      - case: (splitP x_stack) take_s drop_s e1_uniq 
           => l1 l2 -> -> /uniq_catRL<-//.
        by rewrite mem_cat orbC z_s.
      - rewrite mem_rcons inE negb_or.
        case: eqP y_g => [->|_ y_g /=]; first by case: color4P x_white.
        apply/negP =>/(subsetP sb)=> y_b.
        by move: y_g; rewrite -g1Nx !inE andbC; case: color4P y_b.
      - apply: wf_gray_to_stack => //.
          by move: y_g; rewrite -g1Nx !inE; case/andP.
        by rewrite s_def mem_cat stack_add_stack inE z_s !orbT.
     * move=> y y_s; rewrite !ffunE /= ifN; last first.
         case: (splitP x_stack) take_s drop_s e1_uniq 
             => l1 l2 -> -> /uniq_catRL<-//.
         by rewrite mem_cat orbC y_s.
       have y_s1 : y \in stack e1.
         by rewrite s_def stack_add_stack mem_cat !inE y_s !orbT.
       have [z [z_g zLy yCz]] := wf_stack_to_gray e1_gwf y_s1.
       have zDx : z != x.
         apply: contraTneq zLy => ->.
         rewrite wf_num_stack // -ltnNge.
         move: e1_uniq; rewrite s_def !index_cat => uC.
         rewrite !ifN ?stack_add_stack /= ?eqxx ?addn0 //; last 2 first.
         - by rewrite -(uniq_catRL uC) stack_add_stack 
                      ?(mem_cat, inE, y_s, orbT).
         - by rewrite -(uniq_catRL uC) stack_add_stack 
                      ?(mem_cat, inE, eqxx, orbT).
         case: eqP y_s => [<-| _] /=; first by case: color4P x_white.
         by rewrite addnC ltnS leq_addl.
       exists z; split => //; first by rewrite -g1Nx !inE zDx.
       rewrite !ffunE ifN //= mem_rcons !inE (negPf zDx) /=.
       by apply/negP=> /(subsetP sb); case: color4P z_g.
  + move=> y; rewrite !inE whites_add_sccs ?take_s //.
    move=> /predU1P [->|/Nbw1//]; apply/pred0P=> z //=.
    by have [/succ_whiteF->|] := boolP (z \in successors x).
  + rewrite sccs_add_sccs take_s //=; apply/setP=> scc.
    rewrite !inE black_add_sccs ?take_s//= black_sccs1 !inE.
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
- rewrite /= /subenv gray_add_sccs ?take_s ?sb ?g1Nx ?eqxx /= ?drop_s //=.
  rewrite (subset_trans (subenv_black sube1)) ?subsetUr //=.
  rewrite (subset_trans (subenv_sccs sube1)) ?subsetUr //=.
  apply/andP; split.
    rewrite take_s.
    apply/forall_inP => y y_s.
    have yNIr : y \notin rcons s x.
      move: e1_uniq; rewrite s_def -cat_rcons => /uniq_catRL<-//.
      by rewrite mem_cat y_s orbT.
    have /(subenv_num sube1) : y \in stack (add_stack x e).
      by rewrite inE y_s orbT.
    rewrite !ffunE /= !ifN => [->||] //.
    by apply: contra yNIr => /eqP->; rewrite mem_rcons inE eqxx.
  by apply/'exists_eqP; exists ord0; rewrite drop0.
- rewrite whites_add_sccs ?take_s ?sb //.
  by rewrite whites1 whites_add_stack big_set1 wreachex setDDl.
- rewrite big_set1 /= take_s; apply/eqP; rewrite eqn_leq leq_ord andbT.
  rewrite [X in X <= _](_ : infty = @inord infty infty); last by rewrite inordK.
  apply/bigmin_geqP => y /= He.
  rewrite !ffunE /=.
  case: (boolP (_ \in _)) => [|yNIs] //.
  have y_s : y \notin stack e1.
    apply/negP=> y_s.
    have := numx_le _ He.
    rewrite wf_num_stack // s_def.
    rewrite -cat_rcons !index_cat (negPf yNIs) size_rcons ifT; last first.
      by rewrite mem_rcons !inE eqxx.
    rewrite -cats1 index_cat ifN /= ?eqxx ?addn0.
      by rewrite leqNgt addSn ltnS leq_addr.
    have := e1_uniq.
    by rewrite s_def -cat_rcons cat_uniq rcons_uniq -andbA => /and3P[].
  have nxP : 0 < num e1 x.
    by move: x_stack; rewrite num_stackP=> // /andP[].
  case: (@color4P y _ e1_wf) y_s (numx_le _ He) => //.
    by rewrite -wf_num_infty // => /eqP->.
  rewrite -wf_num0 // => /eqP->; rewrite leqNgt.
  by move: x_stack; rewrite num_stackP=> // /andP[->].
Qed.

Theorem tarjan_rec_terminates n (roots : {set V}) e :
  n >= #|whites e| * #|V|.+1 + #|roots| ->
  dfs_correct (tarjan_rec n) roots e.
Proof.
move=> n_ge; wlog ->: e n roots {n_ge} / roots = set0 => [noroot|]; last first.
  have := @dfs_is_correct (dfs1 (tarjan_rec 0)) (tarjan_rec 0) set0 e.
  rewrite /tarjan_rec /dfs_correct /dfs /=.
  case: n=> [|n /=]; case: pickP => [x|_/=]; rewrite ?inE //;
  by apply => ?; rewrite inE.
have [V0|VN0] := posnP #|V|.
  have := max_card (mem roots).
  by rewrite V0 leqn0 cards_eq0 => /eqP /noroot; apply.
elim: n => [|n IHn] in roots e n_ge *.
  move: n_ge; rewrite leqn0 addn_eq0 cards_eq0.
  by move=> /andP [_ /eqP/noroot]; apply.
move=> pre; rewrite /dfs_correct /=.
apply: dfs_is_correct => //= x x_root.
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
  tarjan_rec N setT e0 = (infty, Env setT [::] gsccs infty [ffun _ => infty]).
Proof.
have := @tarjan_rec_terminates N setT e0; rewrite /dfs_correct.
case: tarjan_rec => [m e] [].
- by rewrite ?leq_add ?leq_mul ?max_card.
- do ![split=> //; rewrite /= ?cover0 ?gray0 ?set0D ?setU0 //];
    do ?by[do [move=> ?|move/setP=> ?]; rewrite ?gray0 inE].
  + by move=> x; rewrite ffunE whitesE gray0 !inE eqxx.
  + by move=> x; rewrite ffunE inE eq_sym.
  + by move=> x; rewrite ffunE.
  + by rewrite cards0.
  apply/setP=> y; rewrite !inE /= subset0 andbC; case: eqP => //= ->.
  by have /and3P [_ _ /negPf->]:= gsccs_partition.
move=> [[stack_wf _ _ e_nwf] _ _] sccse /subenv_gray graye.
rewrite (eqP _ : \bigcup_(x in _) _ = setT) ?setDT => [whe ->|]; last first.
  rewrite -subTset; apply/subsetP=> y _; apply/bigcupP.
  by exists y; rewrite ?mem_wreach.
have blacke : black e = setT.
  move/eqP: whe; rewrite whitesE graye gray0 set0U.
  by rewrite -subset0 subCset setC0 subTset => /eqP.
rewrite /black_gsccs blacke ?graye ?gray0 ?setTD ?set0U// in sccse stack_wf.
have {sccse}sccse: sccs e = gsccs.
  by apply/setP=> scc; rewrite sccse inE subsetT andbT.
have stacke : stack e = [::].
  have := stack_wf; rewrite sccse cover_gsccs setCT.
  by case: stack => // x s /(_ x); rewrite !inE eqxx.
have sne : sn e = infty.
  by rewrite wf_sn// graye blacke gray0 set0U cardsT.
have nume : num e = [ffun _ => infty].
  apply/ffunP => x; rewrite ffunE; apply/eqP; rewrite wf_num_infty//.
  by rewrite sccse cover_gsccs.
congr (_, _); last first.
  by case: (e) blacke sccse stacke sne nume => //= *; congr Env.
rewrite big1 // => x _; apply/val_inj; rewrite /= ord_num//.
by apply/eqP; rewrite wf_num_infty // sccse cover_gsccs.
Qed.

Theorem tarjan_correct : tarjan = gsccs.
Proof. by rewrite /tarjan tarjan_rec_is_correct. Qed.

End tarjan.
