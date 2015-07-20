Inductive vec (A : Set) : nat -> Set :=
| vnil : vec A 0
| vcons : A -> forall n : nat, vec A n -> vec A (S n).

Section Vapp.

Variable A : Set.

Fixpoint vapp n (vn : vec A n) m (vm : vec A m) : vec A (n + m) :=
match vn with
| vnil _ => vm
| vcons _ hd _ vn' => vcons _ hd _ (vapp _ vn' _ vm)
end.

Lemma vapp_nil n (vn : vec A n) :
  vapp _ vn _ (@vnil A) = eq_rect _ _ vn _ (plus_n_O n).
Proof.
induction vn.
  simpl.
Require Import Eqdep.
  rewrite <- eq_rect_eq.
  reflexivity.
simpl.
Abort.

End Vapp.

Record vec2 (A : Set) (n : nat) := {
  lst : list A ;
  Hlst : length lst = n }.

Lemma vec2_inj (A : Set) (n : nat) (v1 v2 : vec2 A n) :
  lst _ _ v1 = lst _ _ v2 -> v1 = v2.
Proof.
destruct v1.
destruct v2.
simpl.
intro.
subst lst1.
f_equal.
Require Import ProofIrrelevance.
apply proof_irrelevance.
Qed.

Require Import List.

Section Vapp2.

Variable A : Set.

Definition vapp2 n (vn : vec2 A n) m (vm : vec2 A m) : vec2 A (n + m).
apply Build_vec2 with (app (lst _ _ vn) (lst _ _ vm)).
rewrite app_length.
rewrite (Hlst _ _ vn).
rewrite (Hlst _ _ vm).
reflexivity.
Defined.

Lemma vapp2_nil n (vn : vec2 A n) :
  vapp2 _ vn _ (Build_vec2 A O nil eq_refl) = eq_rect _ _ vn _ (plus_n_O n).
Proof.
apply vec2_inj.
simpl.
rewrite <- app_nil_end.
rewrite <- plus_n_O.
simpl.
reflexivity.
Qed.

End Vapp2.

From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Module TupleExample.

Structure tuple_of (n : nat) (T : Type) : Type :=
  Tuple {tval : seq T; _ : size tval == n}.

Definition emp := Tuple O nat nil isT.
Definition one1 := Tuple 1 nat [:: 1] isT.
Definition one2 := Tuple 1 nat [:: 2] isT.

Goal one1 = one2.
rewrite /one1 /one2.
Fail apply val_inj.
Abort.

Fail Check (val one1).

Canonical tuple_subType (n : nat) (T : Type) := [subType for (@tval n T)].

Check (val one1).
Check (@val _ _ _(*(@tuple_subType 1 nat)*) one1).

Goal one1 = one2.
rewrite /one1 /one2.
apply val_inj => /=.
Abort.

Fail Check (one1 == one2).

Fail Check (@eq_op _ one1 one2).

Definition tuple_eqMixin (n : nat) (T : eqType) := [eqMixin of (@tuple_of n T) by <:].

Canonical tuple_eqType n (T : eqType) := EqType (tuple_of n T) (tuple_eqMixin n T).

Check (@eq_op _ (*(tuple_eqType 1 nat_eqType)*) one1 one2).

Check (one1 == one2).

Fail Check (emp == one1).

End TupleExample.

From MathComp Require Import tuple.

Check [tuple of [:: 1; 2; 3]].
Check [seq x * 2 | x <- [:: 1; 2; 3]].
Check [tuple of [seq x * 2 | x <- [:: 1; 2; 3]]].
