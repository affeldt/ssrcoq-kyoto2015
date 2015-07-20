From Ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From MathComp Require Import div finfun bigop finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal FinSet [ffun x : 'I_3 => true] = setT.
apply/setP => /= x.
rewrite {1}SetDef.pred_of_setE /=.
rewrite {1}/in_mem.
rewrite {1}/mem.
rewrite /=.
rewrite ffunE.
rewrite in_setT.
done.
Qed.

Section finset_example.

Variable T : finType.
Variables A B C : {set T}.

(* use setP *)
Lemma exo38 : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
(* (A \cup B) \cap C = (A \cap C) \cup (B \cap C) *)
Proof.
Abort.

Variables f : nat -> {set T}.

Lemma exo39 : A :&: \bigcup_(i : 'I_3) f i = \bigcup_(i : 'I_3) (A :&: f i).
Proof.
Abort.

Variable U : finType.

Lemma exo40 (h : {ffun T -> U}) :
  injective h -> #| T | <= #| U |.
Proof.
Abort.

End finset_example.
