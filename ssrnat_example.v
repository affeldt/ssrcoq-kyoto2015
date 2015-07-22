From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(* motivating example *)

Goal forall n, n + n = 2 * n.
Show Proof.
elim.
  Show Proof.
  rewrite addn0.
  rewrite muln0.
  done.
Show Proof.
move=> n IH.
rewrite addSn.
rewrite addnS.
rewrite IH.
rewrite mulnS.
rewrite -addn2.
rewrite addnC.
done.
Show Proof.
Qed.

Print nat.

Print nat_rect.
Print nat_ind.
Print nat_rec.

Definition mynat_ind_proof := fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, P n -> P n.+1) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | n0.+1 => f0 n0 (F n0)
  end.

Lemma mynat_ind : forall (P : nat -> Prop), P 0 ->
  (forall n : nat, P n -> P n.+1) ->
  forall n, P n.
exact mynat_ind_proof.
Qed.

(* le vs. leq *)

Print le.
Print leq.

Goal forall n, 0 <= n.
done.
Show Proof.
Qed.

(* compare with: *)
Print Le.le_0_n.

Goal forall n m, n.+1 <= m.+1 -> n <= m.
done.
Show Proof.
Qed.

(* compare with: *)
Print le_S_n.
Print le_pred.

Goal forall n, n <= n.
done.
Qed.

Goal forall n, n <= n.+1.
done.
Qed.

Goal forall n, n < n = false.
by elim.
Qed.

(* 加算の可換性: prove in one line (without using addnC of course) *)

Lemma exo24 n m : m + n = n + m.
Proof.
Abort.

Lemma exo25 (u : nat -> nat) (u0 : u 0 = 2) (u1 : u 1 = 3) (un : forall n, u n.+2 = 3 * u n.+1 - 2 * u n) n :
  u n = 1 + 2 ^ n.
Proof.
Fail elim/yet_another_ind : n. (* see tactics_example.v *)
Abort.

Lemma exo26 d (Hd : odd d) : d.-1./2 = d./2.
Proof.
Abort.

Lemma exo27 d (Hd : ~~ odd d) : (d.-1)./2 = d./2.-1.
Proof.
Abort.

(* about leqP *)

Goal forall n : nat, (n <= 5 \/ 5 < n)%coq_nat.
move=> n.
destruct (Compare_dec.le_gt_dec n 5).
(* NB: does not replace n <= 5 with True *)
auto.
auto.
Show Proof.
Qed.

Goal forall n : nat, (n <= 5) || (5 < n).
move=> n.
case H : (n <= 5).
done.
move/negbT : H.
rewrite -ltnNge.
move=> ->.
done.
(* pros: replace (n <= 5) by true, etc.
   cons: rewrite in the 2nd branch because of mismatch with standard library,
     does not scale to three way case analysis *)
Qed.

Goal forall n : nat, (n <= 5) || (5 < n).
move=> n.
case: (leqP n 5).
done.
done.
Qed.

Definition rgb := sum unit bool.
Definition red : rgb := inl tt.
Definition green : rgb := inr false.
Definition blue : rgb := inr true.

Definition shift (c : rgb) : rgb :=
  match c with
  | inl _ => green
  | inr false => blue
  | inr true => red
  end.

(* Prove the following: *)
Lemma exo28 c : shift (shift (shift c)) = c.
Proof.
Abort.

CoInductive rgb_spec : rgb -> bool -> bool -> bool -> Prop :=
| red_spec : rgb_spec red true false false
| green_spec : rgb_spec green false true false
| blue_spec : rgb_spec blue false false true.

(* Prove the following: *)
Lemma exo29 (*rgbP*) c : rgb_spec c (c == red) (c == green) (c == blue).
Proof.
Abort.

(* same as above but this time using rgbP: *)
Lemma exo30 c : shift (shift (shift c)) = c.
Proof.
Abort.
