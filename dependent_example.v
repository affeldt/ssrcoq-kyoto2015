From Ssreflect Require Import ssreflect.

(* from the JFR tutorial *)
Lemma exo8 (P : nat -> Prop) : ~ (exists x, P x) ->
  forall x, ~ P x.
Proof.
Abort

(* from the JFR tutorial *)
Lemma exo9 (A : Prop) (P : nat -> Prop) :
  (exists x, A -> P x) -> (forall x, ~ P x) -> ~ A.
Proof.
Abort.

Lemma exo10 :
  (exists P : nat -> Prop, forall n, P n) ->
  forall n, exists P : nat -> Prop , P n.
Proof.
Abort.

(* NB: borrowed from https://www.lri.fr/~paulin/MathInfo/ (TP 2) *)

Section relations.

Variable X : Set.
Let rel := X -> X -> Prop.

Lemma exo11 (R : rel) :
  (exists x, forall y, R x y) -> forall y, exists x, R x y.
Proof.
Abort.

Let relfun (R : rel) := forall x y y', R x y /\ R x y' -> y = y'.
Let inj (R : rel) := forall x x' y, R x y /\ R x' y -> x = x'.
Let sur (R : rel) := forall y, exists x, R x y.
Let inv (R : rel) : rel := fun x y => R y x.
Let tot (R : rel) := forall x, exists y, R x y.

Lemma exo12 R : inj R -> relfun (inv R) .
Proof.
Abort.

Lemma exo13 R : relfun R -> inj (inv R) .
Proof.
Abort.

Lemma exo14 R : tot R -> sur (inv R).
Proof.
Abort.

End relations.

From Ssreflect Require Import ssrfun ssrbool eqtype ssrnat seq.
From MathComp Require Import path.

Definition ordered : seq nat -> bool := sorted ltn.

Inductive map :=
| mkMap : forall s : seq (nat * bool), ordered (unzip1 s) -> map.

Inductive int (n : nat) :=
| mkInt : forall s : seq bool, size s = n -> int n.
