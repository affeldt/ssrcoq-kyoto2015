Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg finset fingroup zmodp poly ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section test.

Variable R : realFieldType.

Import Num.Theory.

Lemma helper_partition p (Hp : (0 < p)%N) (F : nat -> R) : 
  \sum_(1 <= i < 2 ^ p) F i = \sum_(0 <= i < p) \sum_(2 ^ i <= j < 2 ^ i.+1) F j.
Proof.
elim: p Hp F => //.
case => [_ _ F /= | p IH _ F].
  rewrite /= big_nat_recr //= big_nil big_nat_recr //= big_nil.
  by rewrite expn0 expn1 big_nat_recr //= big_nil !add0r.
rewrite (@big_cat_nat _ _ _ (2 ^ p.+1)) /=; last 2 first.
  by rewrite expn_gt0.
  by rewrite leq_exp2l.
by rewrite IH // [RHS]big_nat_recr.
Qed.

Lemma half_ub i : 1 / 2%:R <= \sum_(0 <= j < 2 ^ i) 1 / (2 ^ i + j.+1)%:R :> R.
Proof.
suff Hj : forall j, (j < 2 ^ i)%N -> 1 / (2 ^ i.+1)%:R <= 1 / (2 ^ i + j.+1)%:R :> R.
  suff : 1 / 2%:R <= \sum_(0 <= j < 2 ^ i) 1%:R / (2 ^ i.+1)%:R :> R.
    rewrite 2!big_nat => ub.
    apply: ler_trans; [ | apply ub | ].
    apply ler_sum => j /= ?; by apply Hj.
  rewrite -big_distrl /= -natr_sum sum1_size size_iota subn0 expnS natrM invrM; last 2 first.
    by rewrite unitf_gt0 // ltr0n.
    by rewrite unitf_gt0 // ltr0n expn_gt0.
  by rewrite mulrA GRing.divff // lt0r_neq0 // ltr0n expn_gt0.
move=> j Hj.
rewrite 2!div1r lef_pinv.
- by rewrite expnS mul2n -addnn ler_nat leq_add2l.
- by rewrite posrE // ltr0n expn_gt0.
- by rewrite posrE addnS ltr0n.
Qed.

Lemma harmo p' : let p := p'.+1 in 
  \sum_(1 <= k < (2 ^ p).+1) (1 / k%:R) >= 1 + p%:R / 2%:R :> R.
Proof.
cbv zeta; set p := p'.+1.
have -> : \sum_(1 <= k < (2 ^ p).+1) 1 / k%:R = 
          1 + \sum_(0 <= i < p) \sum_(0 <= j < 2 ^ i) (1 / (2 ^ i + j.+1)%:R) :> R.
  rewrite big_nat_recl //; last by rewrite expn_gt0.
  rewrite div1r invr1; congr (_ + _).
  rewrite helper_partition //.
  apply eq_bigr => i /= _.
  rewrite -{1}(add0n (2 ^ i)) big_addn expnS mul2n -addnn addnK.
  apply eq_bigr => j _; by rewrite addnC addnS.
apply ler_add => //.
have -> : p%:R / 2%:R = \sum_(0 <= i < p) 1%:R / 2%:R :> R.
  by rewrite -big_distrl /= -natr_sum sum1_size size_iota subn0.
apply ler_sum => i _; apply half_ub.
Qed.



