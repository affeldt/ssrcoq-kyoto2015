From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(* move and apply with views *)

Goal forall (P Q : Prop), (P -> Q) -> P -> Q.
Proof.
move=> P Q PQ.
move/PQ.
Undo 1.
move=> tmp. move: (PQ tmp). move=> {tmp}.
done.
Qed.

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
move=> P Q PQ.
move/PQ.
Undo 1.
move/(iffLR PQ).
done.
Qed.

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
move=> P Q PQ p.
apply/PQ.
Undo.
apply/(iffLR PQ).
done.
Qed.

(* taken from the map 2012 summer scool *)
Lemma exo18 : forall (P : nat -> Prop) (Q : Prop),
  (P 0 -> Q)->
  (forall n, P n.+1 -> P n) ->
  P 4 -> Q.
Proof.
(* use move and move/ only *)
Abort.

Goal forall P : bool, P -> P.
Set Printing Coercions.
rewrite /is_true.
Unset Printing Coercions.
Abort.

(* views and reflection *)

Goal forall (P Q : bool), P && Q -> Q.
Proof.
move=> P Q.
move/andP.
case.
Undo 2.
case/andP.
done.
Qed.

Goal forall (P Q : bool), P && Q -> Q.
move=> P Q.
move/(elimTF andP).
Undo 1.
case: (@andP P Q) => //.
Abort.

Goal forall P Q : bool, P || Q -> Q || P.
move=> P Q.
case/orP.
Undo 1.
case/orP => [H1 | H2].
  by rewrite H1 orbT.
by rewrite H2.
Qed.

(* use views only: move, case, with /orP, /andP and /(_ t) *)

Lemma exo19 (b b1 b2 : bool) : (b1 -> b) -> (b2 -> b) -> b1 || b2 -> b.
Proof.
Abort.

(* taken from the map 2012 summer school *)
Lemma exo20 (Q : nat -> Prop) (p1 p2 : nat -> bool) x :
  ((forall y, Q y -> p1 y /\ p2 y) /\ Q x) -> p1 x && p2 x.
Proof.
Abort.

(* taken from the map 2012 summer school *)
Lemma exo21 (Q : nat -> Prop) (p1 p2 : nat -> bool) x :
  ((forall y, Q y -> p1 y \/ p2 y) /\ Q x) -> p1 x || p2 x.
Proof.
Abort.

Check (@eq_refl _ 2).
Print eqn.

Goal forall n m, eqn n m -> n = m.
move=> n m.
move/eqP.
done.
Qed.
