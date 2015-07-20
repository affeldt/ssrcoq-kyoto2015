From Ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From MathComp Require Import div finfun bigop prime binomial ssralg finset fingroup finalg perm zmodp matrix.

Local Open Scope ring_scope.

Lemma castmx_mulmx {A : ringType} (f : nat -> nat -> nat) P
  (Pf : forall a b, P a b -> f a b = b) a b (Pab : P a b)
  m (X : 'M[A]_(m, f a b)) n (Y : 'M_(f a b, n)) :
  castmx (erefl m, Pf _ _ Pab) X *m
  castmx (Pf _ _ Pab, erefl n) Y = X *m Y.
Proof.
apply/matrixP => m0 n0.
rewrite !mxE /=.
move: (Pf _ _ Pab) X Y; rewrite (Pf _ _ Pab) => bb X Y.
apply eq_bigr => l _ /=.
rewrite !castmxE /=.
by rewrite !cast_ord_id.
Qed.

Section matrix_example.

Variables (l d : nat).

Variable A : 'M['F_2]_(l - d, d).

Hypothesis dl : d <= l.

Definition H : 'M_(l - d, l) :=
  castmx (erefl, subnKC dl) (row_mx A 1%:M).

Definition G : 'M_(d, l) :=
  castmx (erefl, subnKC dl) (row_mx 1%:M (-A)^T).

Lemma GHT : G *m H ^T = 0.
Proof.
rewrite /G /H.
rewrite trmx_cast /=.
rewrite (castmx_mulmx _ _ subnKC).
rewrite tr_row_mx.
rewrite mul_row_col.
rewrite mul1mx.
rewrite trmx1.
rewrite mulmx1.
rewrite -GRing.linearD /=.
rewrite GRing.addrN.
rewrite trmx0.
done.
Qed.

End matrix_example.