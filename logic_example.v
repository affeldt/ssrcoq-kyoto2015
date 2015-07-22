Module minimal_Gallina_introduction.

Variable x : Prop.
Variables A B : Prop.
Variable t2 : Prop.

Check A -> B : Prop.
(* NB: holds thanks to the rule Prod-Prop *)

Check (fun y => y -> y) : Prop -> Prop.
Definition t1_oops := fun y => y -> y.
Check t1_oops.
Definition t1 := fun y : Prop => y -> y.
Check t1.
Check (t1 t2) : Prop.

Check (Prop -> Prop) -> B.
(* NB: Prop -> Prop has type a sort -> ok *)
Fail Check (fun y : Prop => y -> y) -> B.
(* NB: (fun y : Prop => y -> y) has type Prop -> Prop, which is not a sort -> NG *)

End minimal_Gallina_introduction.

From Ssreflect Require Import ssreflect.

Module propositions_as_types_example.

Lemma hilbertS (A B C : Prop) :
  (A -> B -> C) -> (A -> B) -> A -> C.
Show Proof.
move=> H1.
Show Proof. (* observe the effect of move=> on the proof-term *)
move=> H2.
move=> H3.
Show Proof.
cut B. (* NB: this is a traditional Coq tactic, seldom used in practice but corresponds well to modus ponens *)
Show Proof.
cut A.
Show Proof.
assumption.
assumption.
Show Proof.
cut A.
assumption.
assumption.
Show Proof.
Qed.

Definition hilbertS_proof :=
  fun (A B C : Prop) (H1 : A -> B -> C) (H2 : A -> B) (H3 : A) =>
    (fun H : B => (fun H0 : A => H1 H0) H3 H) ((fun H : A => H2 H) H3).

Lemma hilbertS_direct_proof (A B C : Prop) :
  (A -> B -> C) -> (A -> B) -> A -> C.
exact (hilbertS_proof A B C).
Qed.

Lemma hilbertS_in_practice (A B C : Prop) :
  (A -> B -> C) -> (A -> B) -> A -> C.
move=> H1.
move=> H2.
move=> H3.
apply H1.
exact H3.
apply H2.
exact H3.
Show Proof.
Qed.

Definition hilbertS_in_practice_proof :=
  fun (A B C : Prop) (H1 : A -> B -> C) (H2 : A -> B) (H3 : A) =>
    H1 H3 (H2 H3).

Goal hilbertS_proof = hilbertS_in_practice_proof.
reflexivity.
Qed.

End propositions_as_types_example.

Module move_and_apply_tactics.

Lemma modus_ponens : forall P Q : Prop, (P -> Q) -> P -> Q.
Show Proof.
move=> P.
move: P.
move=> P Q PQ p.
move: PQ.
apply.
done.
Qed.

Goal forall P Q : Prop, (forall R : Prop, R -> Q) -> P -> Q.
Proof.
move=> P Q rq p.
Fail apply rq.
apply: rq p.
(*
compare with:
refine (rq _ _).
exact p.
*)
Qed.

(* a note an unification *)
Variable A : Prop.
Variable op : A -> A -> A.
Local Notation "a + b" := (op a b). (* left associative *)
Hypothesis opA : forall a b c, a + (b + c) = a + b + c.
Check opA.
Variable lt : A -> A -> Prop.
Local Notation "a < b" := (lt a b).
Hypothesis lt_addr : forall m n p, m < n -> m < n + p.

Goal forall a b c d,
  a < b ->
  a < b + c + d.
move=> a b c d.
Fail apply lt_addr.
(* Error: Impossible to unify "b + c" with "b". *)
(* match m<->a, n<->b, p<->d and thus b + c<->n !!! *)
rewrite -opA.
apply lt_addr.
Qed.

Goal False.
evar (x : nat).
have : (2 + x = 4 + 5)%nat.
  rewrite /x.
  apply refl_equal.
rewrite /= in x *.
Abort.

End move_and_apply_tactics.

Lemma exo0 : forall P : Prop, P -> P.
Proof.
Admitted.

Lemma exo1 : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
Admitted.

Lemma exo2 : forall P : Prop, (P -> P) -> P -> P.
Proof.
(* NB: pove using the modus ponens lemma *)
Admitted.

(* transitivity of implication *)
Lemma exo3 P Q R : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
Admitted.

Section logical_connectives.

Print True.
Check True.
Check I.

Goal True.
apply: I.
Qed.

Print False.

Goal True -> False.
case.
Show Proof.
Abort.

Check False_ind.

Goal False -> 1 = 0.
move=> p.
exact: (False_ind (1 = 0) p).
Qed.

Goal False -> 1 = 0.
case.
Qed.

Print and.
Check conj I I.
Print and_ind.
Print and_rect.

Goal forall P Q, P /\ Q -> Q /\ P.
move=> P Q.
case.
Show Proof.
move=> p q.
split.
exact q.
exact p.
Qed.

Print or.
Print or_ind.

Check (or_intror False I).
About or_intror.
Check (@or_intror False True I).
Check (@or_intror False _ I).
Check (@or_intror _ _ I).
Check (@or_intror _ _ I) :  False \/ True.

Goal forall A B, A \/ B -> B \/ A.
move=> A B.
  case=> [a | b].
  right.
  exact a.
left.
exact b.
Qed.

End logical_connectives.

Lemma exo4 : False \/ True.
Proof.
Abort.

Lemma exo5 : forall A B C : Prop, A /\ B <-> B /\ A.
Proof.
Abort.

Lemma exo6 (A B C : Prop) : A /\ B /\ C ->
  (A /\ B) /\ C.
Proof.
Abort.

Lemma exo7 (A B : Prop) : (A -> B) -> (~B -> ~A).
Proof.
Abort.

Section Set_Prop.

Check nat.

Goal 0 = 1 -> False.
move=> abs.
discriminate.
Qed.

(* case analysis of Prop proofs forbidden on sorts Set and Types *)

Goal (exists n : nat, True) -> nat.
Fail case.
(*  Error: Case analysis on sort Set is not allowed for inductive definition ex *)
Abort.
About ex.

Goal forall A B : Prop, A \/ B -> nat.
move=> A B.
Fail case.
Abort.

(* case analysis of Prop proofs ok on sort Set when only one constructor *)

Goal 0 = 1 -> nat.
move=> abs.
discriminate.
Show Proof.
Qed.

Goal forall n m : nat, n = m /\ n <> m -> nat.
move=> n m.
case => nm nm'.
exact O.
Qed.

Print sum.
Print sumbool.
Print sumor.

(* case analysis of Type proofs ok on any sorts *)

About sig.
Goal {n : nat | True} -> nat.
case.
move=> m _.
exact m.
Qed.

End Set_Prop.

Section product_formation.

(* NB: hierarchy *)
Check Prop.
Check Set.
Set Printing Universes.
Check Type.
Unset Printing Universes.

(* rule Prop <= Set: *)
Variables P0 P1 : Prop.
Check P0 -> P1 : Set.
Check P0 : Set.
(* rule Prop <= Type: *)
Check P0 : Type.
(* NB: rule Set <= Type: *)
Variable S0 : Set.
Check S0 : Type.

(* rule Prod-Prop: *)
Check P1 -> P1 : Prop.
Check (S0 -> P0) : Prop.
Variable T0 : Type.
Check (T0 -> P0) : Prop.

Check (forall x : nat, 0 <= x).
Check (forall x : nat, x = x) : Set.
Check (forall A : Prop, A -> A).
Check (forall P : nat -> Prop, P O -> exists n : nat , P n) : Prop.

(* rule Prod-Set: *)
Check (P0 -> S0) : Set.
Fail Check (P0 -> S0) : Prop.
Variable S1 : Set.
Check (S1 -> S0) : Set.
Fail Check (T0 -> S0) : Set.

Check (nat -> nat).
Fail Check (forall A : Set, A -> A) : Set.

(* rule Prod-Type: *)

Check (Prop -> Prop) : Type.
Check (Set -> Set) : Type.
Check (forall A : Set, A -> A) : Type.
Check (nat -> Prop) : Type.
Check ((Prop -> Prop) -> Prop) : Type.
Check (forall P : nat -> Prop, Prop) : Type.

End product_formation.
