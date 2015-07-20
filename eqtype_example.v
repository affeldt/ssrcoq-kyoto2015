Module Overloading_of_notations.

Record myeq := Myeq {
  carrier : Set ;
  myequality : carrier -> carrier -> bool }.

About myequality.
(* take as a first argument a complete instance of a record myeq *)

Notation "a '===' b" := (myequality _ a b) (at level 70).

Fail Check (true === false).

Require Bool.

Print Bool.eqb.

Check (Myeq bool Bool.eqb : myeq).

(* register an instance of myeq for booleans as canonical: *)

Canonical Structure myeq_bool := Myeq bool Bool.eqb.

(* => Coq will insert Bool.eqb automatically based on type information *)

Check (true === false).
Unset Printing Notations.
Check (true === false).
Set Printing Notations.
Eval compute in (true === false).

(* the same with natural numbers *)

Fail Check (O === 1).

Require Arith.

Check EqNat.beq_nat.

(* exo22: register an instance of myeq for natual numbers as canonical
and check that one can still use the notation "==" *)

End Overloading_of_notations.

Module Eqtype_example.

(* overloading of notation + equivalence with Leibniz equality *)

Record myeq := Eqtype {
  carrier : Set ;
  myequality : carrier -> carrier -> bool ;
  Hmyequality : forall x y : carrier, myequality x y = true <-> x = y }.

Notation "a '===' b" := (myequality _ a b) (at level 70).

Canonical Structure eqtypenat := Eqtype _ _ EqNat.beq_nat_true_iff.

Canonical Structure eqtypebool := Eqtype _ _ Bool.eqb_true_iff.

Check O : nat.
Check (O : carrier _).

Coercion is_true : bool >-> Sortclass.

From Ssreflect Require Import ssreflect.

Goal forall x y : bool, x === y -> x = y.
move=> x y.
by move/Bool.eqb_true_iff.
Undo 1.
move/Hmyequality.
done.
Qed.

Goal forall x y : nat, x === y -> x = y.
move=> x y.
Fail by move/Bool.eqb_true_iff.
by move/EqNat.beq_nat_true_iff.
Undo 1.
move/Hmyequality.
done.
Qed.

(* -> we have the same proof for booleans and natural numbers *)

End Eqtype_example.

Module unicity_of_identity_proofs.

(* in Coq, two proofs of the same Prop facts can be considered as equal
   (proof-irrelevance is admissible in Coq) *)
Variable H1 : O < 3.
Variable H2 : O < 3.
Goal H1 = H2.
Fail reflexivity.
Require ProofIrrelevance.
now apply ProofIrrelevance.proof_irrelevance.
Qed.

(* in Coq, we can prove the unicity of equality proofs when the type has a decidable
  equality, so that proof-irrelevance does not need to be admitted; for example, in the
  case of booleans: *)

Lemma eq_symK : forall (A : Type) (a b : A) (e : a = b), eq_sym (eq_sym e) = e.
Proof.
intros A a b e.
destruct e.
simpl.
reflexivity.
Qed.

Lemma buip : forall (b1 b2 : bool) (p1 p2 : (b1 = b2 : Prop)), p1 = p2.
Proof.
intros b1 b2 p1 p2.
(*destruct p1.
Fail destruct p2.*)
pose (fun b (e : b1 = b) =>
        match Bool.bool_dec b1 b with
          | left H => H
          | right _ => e end) as test_against_b1.
cutrewrite (p1 = test_against_b1 b2 p1).
  cutrewrite (p2 = test_against_b1 b2 p2).
    unfold test_against_b1.
    destruct p1.
    destruct b1; simpl; reflexivity.
  destruct p2.
  unfold test_against_b1.
  destruct b1; simpl; reflexivity.
destruct p1.
unfold test_against_b1.
destruct b1; simpl; reflexivity.
Qed.

Variable lt : nat -> nat -> bool.
Check (lt 0 3) : bool.
Variable H1' : lt O 3 = true.
Variable H2' : lt O 3 = true.

Goal H1' = H2'.
Fail reflexivity.
apply buip.
Abort.

End unicity_of_identity_proofs.
