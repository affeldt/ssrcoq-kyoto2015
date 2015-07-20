Require Import Init.

Definition id_explicit (A : Type) (a : A) : A := a.

Check (id_explicit nat O).
Check (id_explicit _ O).

Definition id_implicit {A : Type} (a : A) : A := a.

Check (@id_implicit nat O).
Check (@id_implicit _ O).
Check (id_implicit O).
Check (id_implicit _ O).
Fail Check (id_implicit nat O).
Check (id_implicit (fun x : nat => x) O).

(* strict implicit arguments *)

About cons.
(* the 1st argument of List.cons is strict (inferable from the 2nd
or the 3rd argument) *)
Check (@cons _ O nil).
Check (cons O nil).

Inductive Pair {A : Type} := mkPair :
  forall {l : list A}, length l = 2 -> Pair.

Check (@mkPair _ (cons O (cons O nil)) (eq_refl (length (cons O (cons O nil))))).
Check (@mkPair _ (cons O (cons O nil)) (eq_refl 2)).
Check (mkPair (eq_refl (length (cons O (cons O nil))))).
Fail Check (mkPair (eq_refl 2)).

Reset Pair.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive Pair (A : Type) := mkPair :
  forall l : list A, length l = 2 -> Pair A.

Definition Pair00 := mkPair (eq_refl (length (cons O (cons O nil)))).
Print Pair00.

Unset Printing Implicit Defensive.

Print Pair00.
