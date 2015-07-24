From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Section bigop_definition.

Variables (R I : Type).
Variables (op : R -> R -> R) (idx : R).
Variables (r : seq I) (P : pred I) (F : I -> R).

Definition bigop :=
  foldr (fun i x => if P i then op (F i) x else x) idx r.

End bigop_definition.

Section bigop_monoid.

Variables (R I : Type).
Variables (op : R -> R -> R).
Variables (P : pred I) (F : I -> R).

Hypothesis opA : associative op.

Lemma bigop_idx (* exo31 *) r idx1 idx2 :
  bigop R I op (op idx1 idx2) r P F =
  op (bigop R I op idx1 r P F) idx2.
Proof.
Admitted.

Variable idx : R.
Hypothesis op0 : left_id idx op.

Lemma bigop_split (* exo32 *) r1 r2 :
  bigop R I op idx (r1 ++ r2) P F =
  op (bigop R I op idx r1 P F) (bigop R I op idx r2 P F).
Proof.
Admitted.

End bigop_monoid.

Notation "\sum_ ( 0 <= i < n ) F" :=
  (bigop _ _ addn 0 (iota 0 n) xpredT (fun i => F))
  (at level 41, i at next level, format "\sum_ ( 0  <=  i  <  n )  F").

Lemma gauss (* exo33 *) n : 2 * (\sum_(0 <= i < n.+1) i) = n * n.+1.
Proof.
Abort.
