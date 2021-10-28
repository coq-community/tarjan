From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop finset finfun perm fingraph path div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\min_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \min_ i '/  '  F ']'").
Reserved Notation "\min_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \min_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \min_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\min_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \min_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \min_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\min_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \min_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\min_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\min_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \min_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \min_ ( i  <  n )  F ']'").
Reserved Notation "\min_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \min_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\min_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \min_ ( i  'in'  A ) '/  '  F ']'").
Lemma ord_minn_le n (i j : 'I_n) : minn i j < n.
Proof. by rewrite gtn_min ltn_ord. Qed.
Definition ord_minn {n} (i j : 'I_n) := Ordinal (ord_minn_le i j).

Section ord_min.
Variable (n : nat).
Notation T := (ord_max : 'I_n.+1).
Notation min := (@ord_minn n.+1).

Lemma minTo : left_id T min.
Proof. by move=> i; apply/val_inj; rewrite /= (minn_idPr _) ?leq_ord. Qed.

Lemma minoT : right_id T min.
Proof. by move=> i; apply/val_inj; rewrite /= (minn_idPl _) ?leq_ord. Qed.

Lemma minoA : associative min.
Proof. by move=> ???; apply/val_inj/minnA. Qed.

Lemma minoC : commutative min.
Proof. by move=> ??; apply/val_inj/minnC. Qed.

Canonical ord_minn_monoid := Monoid.Law minoA minTo minoT.
Canonical ord_minn_comoid := Monoid.ComLaw minoC.

End ord_min.

Notation "\min_ ( i <- r | P ) F" :=
  (\big[ord_minn/ord_max]_(i <- r | P%B) F%N) : nat_scope.
Notation "\min_ ( i <- r ) F" :=
  (\big[ord_minn/ord_max]_(i <- r) F%N) : nat_scope.
Notation "\min_ ( i | P ) F" :=
  (\big[ord_minn/ord_max]_(i | P%B) F%N) : nat_scope.
Notation "\min_ i F" :=
  (\big[ord_minn/ord_max]_i F%N) : nat_scope.
Notation "\min_ ( i : I | P ) F" :=
  (\big[ord_minn/ord_max]_(i : I | P%B) F%N) (only parsing) : nat_scope.
Notation "\min_ ( i : I ) F" :=
  (\big[ord_minn/ord_max]_(i : I) F%N) (only parsing) : nat_scope.
Notation "\min_ ( m <= i < n | P ) F" :=
 (\big[ord_minn/ord_max]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\min_ ( m <= i < n ) F" :=
 (\big[ord_minn/ord_max]_(m <= i < n) F%N) : nat_scope.
Notation "\min_ ( i < n | P ) F" :=
 (\big[ord_minn/ord_max]_(i < n | P%B) F%N) : nat_scope.
Notation "\min_ ( i < n ) F" :=
 (\big[ord_minn/ord_max]_(i < n) F%N) : nat_scope.
Notation "\min_ ( i 'in' A | P ) F" :=
 (\big[ord_minn/ord_max]_(i in A | P%B) F%N) : nat_scope.
Notation "\min_ ( i 'in' A ) F" :=
 (\big[ord_minn/ord_max]_(i in A) F%N) : nat_scope.

Section extra_bigmin.

Variables (n : nat) (I : finType).
Implicit Type (F : I -> 'I_n.+1).

Lemma geq_bigmin_cond (P : pred I) F i0 :
  P i0 -> F i0 >= \min_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigD1 i0) //= geq_minl. Qed.
Arguments geq_bigmin_cond [P F].

Lemma geq_bigmin F (i0 : I) : F i0 >= \min_i F i.
Proof. exact: geq_bigmin_cond. Qed.

Lemma bigmin_geqP (P : pred I) (m : 'I_n.+1) F :
  reflect (forall i, P i -> F i >= m) (\min_(i | P i) F i >= m).
Proof.
apply: (iffP idP) => leFm => [i Pi|].
  by apply: leq_trans leFm _; apply: geq_bigmin_cond.
by elim/big_ind: _; rewrite ?leq_ord // => m1 m2; rewrite leq_min => ->.
Qed.

Lemma bigmin_inf i0 (P : pred I) (m : 'I_n.+1) F :
  P i0 -> m >= F i0 -> m >= \min_(i | P i) F i.
Proof.
by move=> Pi0 le_m_Fi0; apply: leq_trans (geq_bigmin_cond i0 Pi0) _.
Qed.

Lemma bigmin_eq_arg i0 (P : pred I) F :
  P i0 -> \min_(i | P i) F i = F [arg min_(i < i0 | P i) F i].
Proof.
move=> Pi0; case: arg_minnP => //= i Pi minFi.
by apply/val_inj/eqP; rewrite eqn_leq geq_bigmin_cond //=; apply/bigmin_geqP.
Qed.

Lemma eq_bigmin_cond (A : pred I) F :
  #|A| > 0 -> {i0 | i0 \in A & \min_(i in A) F i = F i0}.
Proof.
case: (pickP A) => [i0 Ai0 _ | ]; last by move/eq_card0->.
by exists [arg min_(i < i0 in A) F i]; [case: arg_minnP | apply: bigmin_eq_arg].
Qed.

Lemma eq_bigmin F : #|I| > 0 -> {i0 : I | \min_i F i = F i0}.
Proof. by case/(eq_bigmin_cond F) => x _ ->; exists x. Qed.

Lemma bigmin_setU (A B : {set I}) F :
  \min_(i in (A :|: B)) F i =
  ord_minn (\min_(i in A) F i) (\min_(i in B) F i).
Proof.
have d : [disjoint A :\: B & B] by rewrite -setI_eq0 setIDAC setDIl setDv setI0.
rewrite (eq_bigl [predU (A :\: B) & B]) ?bigU//=; last first.
  by move=> y; rewrite !inE; case: (_ \in _) (_ \in _) => [] [].
symmetry; rewrite (big_setID B) /= [X in ord_minn X _]minoC -minoA.
congr (ord_minn _ _); apply: val_inj; rewrite /= (minn_idPr _)//.
by apply/bigmin_geqP=> i; rewrite inE => /andP[iA iB]; rewrite (bigmin_inf iB).
Qed.

End extra_bigmin.

Arguments geq_bigmin_cond [n I P F].
Arguments geq_bigmin [n I F].
(* Arguments bigmin_geqP [n I P m F]. *)
Arguments bigmin_inf [n I] i0 [P m F].
Arguments bigmin_eq_arg [n I] i0 [P F].

Section bigmin_bigcup.

Variables (n : nat) (I J : finType).

Lemma bigmin_bigcup (A : pred I) (B : I -> {set J}) F :
  \min_(j in \bigcup_(i in A) B i) F j =
  \min_(i in A) \min_(j in B i) F j :> 'I_n.+1.
Proof.
elim/big_rec2: (RHS); first by rewrite big_set0.
by move=> i B0 m iA <-; rewrite bigmin_setU.
Qed.

End bigmin_bigcup.

