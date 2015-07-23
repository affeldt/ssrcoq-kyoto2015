Print bool.

Print bool_rect.
Print bool_ind.
Print bool_rec.

(* negate *)
Definition match_true := match true with true => false | false => true end.

Check match_true.
Eval compute in match_true.

Definition nat_of_bool := bool_rec (fun _ => nat) 1 0.

Check (nat_of_bool : bool -> nat).

Eval compute in (nat_of_bool false).

Definition dep_of_bool := bool_rec (fun b => match b with true => nat | false => bool end) 1 true.

Check (dep_of_bool : forall b, match b with true => nat | false => bool end).

Eval compute in (dep_of_bool false).

Definition dep_of_bool2 b : match b with true => nat | false => bool end :=
  match b with
      true => 1
    | false => true
  end.

Goal dep_of_bool = dep_of_bool2.
reflexivity.
Qed.

Check dep_of_bool2.

From Ssreflect Require Import ssreflect ssrfun ssrbool.

Print andb.
Print negb.
Print orb.

Goal forall a b : bool, ~~ (a && b) = (~~ a) || (~~ b).
by case; case.
Qed.

From Ssreflect Require Import eqtype ssrnat.

Lemma ifP_example : forall n : nat, odd (if odd n then n else n.+1).
Proof.
move=> n.
case: ifP.
  done.
move=> Hn.
rewrite -addn1.
rewrite odd_add.
by rewrite Hn.
Qed.

Check ifP.
(* forall (A : Type) (b : bool) (vT vF : A),
       if_spec b vT vF (b = false) b (if b then vT else vF) *)
Print if_spec.
(* CoInductive if_spec (A : Type) (b : bool) (vT vF : A)
            (not_b : Prop) : bool -> A -> Set :=
    IfSpecTrue : b -> if_spec b vT vF not_b true vT
  | IfSpecFalse : not_b -> if_spec b vT vF not_b false vF
*)
(* ifP is the proof that "if ... is ... then ... else ..." satifies the if_spec predicate *)
(*
upon case analysis, match (a subterm in) the goal with
"(if b then vT else vF)" and generate to goals:
1. b is replaced with true, b is pushed on the stack
1. b is replaced with false, not_b is pushed on the stack
*)

Lemma exo23 : forall n : nat, n * n - 1 < n ^ n.
Proof.
move=> n.
case: (boolP (n == O)).
  admit.
move=> n0.
case: (boolP (n == 1)).
  admit.
move=> n1.
have [m Hm] : exists m, n = m.+2.
  admit.
admit.
Abort.

Check boolP.
(* forall b1 : bool, alt_spec b1 b1 b1 *)
Check (boolP (0 == 1)).
(* alt_spec (0 == 1) (0 == 1) (0 == 1) *)
Check alt_spec.
Print alt_spec.
(* two combinations possible:
   P b true
   P b false
   upon case analysis, there are two branches:
   - "(0 == 1)" is replaced by true and the hypothesis "(0 == 1) (= true)" is pushed
   - "(0 == 1)" is replaced by false and the hypothesis "~~ (0 == 1)" = "(0 != 1)" is pushed
*)
