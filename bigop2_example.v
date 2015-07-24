From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From MathComp Require Import div bigop ssralg finset fingroup zmodp poly ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Import Num.Theory.

Variable R : realFieldType.

Record dist (A : finType) := mkDist {
  pmf :> A -> R ;
  pmf0 : forall a, 0 <= pmf a ;
  pmf1 : \sum_(a in A) pmf a = 1 }.

Definition dist_of {A : finType} := fun phT : phant (Finite.sort A) => dist A.

Notation "{ 'dist' T }" := (dist_of (Phant T))
  (at level 0, format "{ 'dist'  T }") : proba_scope.

Local Open Scope proba_scope.

Section probability.

Variable A : finType.
Variable P : dist A.

Definition Pr (E : {set A}) := \sum_(a in E) P a.

End probability.

Module ProdDist.

Section local.

Variables A B : finType.
Variable P1 : dist A.
Variable P2 : dist B.

Definition f := fun ab => P1 ab.1 * P2 ab.2.

Lemma f0 a : 0 <= f a.
Proof.
rewrite /f.
apply mulr_ge0.
apply pmf0.
apply pmf0.
Qed.

Lemma f1 : \sum_ab f ab = 1.
Proof.
rewrite /f.
rewrite -(pair_big xpredT xpredT (fun a b => P1 a * P2 b)) /=.
rewrite -(pmf1 P1).
apply eq_bigr => a _.
rewrite -big_distrr /=.
rewrite pmf1.
rewrite mulr1.
done.
Qed.

Definition d : {dist A * B} := mkDist f0 f1.

End local.

End ProdDist.

Local Notation "P1 `x P2" := (ProdDist.d P1 P2) (at level 9).

From MathComp Require Import tuple finfun.

Local Notation "t \_ i" := (tnth t i) (at level 9).

Module TupleDist.

Section local.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

Definition f (t : n.-tuple A) := \prod_(i < n) P t \_ i.

Lemma f0 t : 0 <= f t.
Proof.
rewrite /f.
apply prodr_ge0.
move=> i _.
apply pmf0.
Qed.

Lemma f1 : \sum_t f t = 1.
Proof.
rewrite /f.
transitivity (\sum_(f : {ffun 'I_n -> A}) \prod_(i < n) P (f i)).
  rewrite (reindex_onto (fun f : {ffun 'I_n -> A} => [tuple f i | i < n])
                        (fun t => [ffun i : 'I_n => t \_ i])) /=; last first.
    move=> t _.
    apply eq_from_tnth => i.
    rewrite tnth_mktuple.
    rewrite ffunE.
    done.
   apply eq_big.
     move=> f.
     apply/eqP/ffunP => /= i.
     rewrite ffunE.
     by rewrite tnth_mktuple.
   move=> f /eqP Hf.
   apply eq_bigr => i _.
   by rewrite tnth_mktuple.
rewrite -(@bigA_distr_bigA _ _ _ _ _ _ _ (fun (i : 'I_n) (a : A) => P a)) /=.
rewrite big_const_ord.
rewrite pmf1.
elim: n => // m.
by rewrite iterSr mulr1.
Qed.

Definition d : {dist n.-tuple A} := mkDist f0 f1.

End local.

End TupleDist.

Notation "P `^ n" := (TupleDist.d P n) (at level 9).
