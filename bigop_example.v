From Ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From MathComp Require Import path div tuple finfun bigop.

Lemma big_cat_example f :
  \sum_(1 <= n < 11) f(n) = \sum_(1 <= n < 6) f(n) + \sum_(6 <= n < 11) f(n).
Proof. by rewrite -big_cat. Qed.

(* hint: use big_nat_recr and big_nil *)
Lemma exo34 : forall n : nat, 2 * (\sum_(0 <= x < n.+1) x) = n * n.+1.
Proof.
Abort.

Lemma exo35 n : (6 * \sum_(k < n.+1) k ^ 2)%nat = n * n.+1 * (n.*2).+1.
Proof.
Abort.

Lemma exo36 (x n : nat) : 1 < x -> (x - 1) * (\sum_(k < n.+1) x ^ k) = x ^ n.+1 - 1.
Proof.
Abort.

Lemma exo37 (v : nat -> nat) (v0 : v 0 = 1) (vn : forall n, v n.+1 = \sum_(k < n.+1) v k) (n : nat) :
  n != 0 -> v n = 2 ^ n.-1.
Proof.
Abort.

Parameter n : nat.
Parameters a b : 'I_n.

(* use bigA_distr_big to prove the following *)

Lemma bigA_distr_big_test : (a + b)^2 = a^2 + 2 * a * b + b^2.
Proof.
case: (boolP (a == b)) => [/eqP -> | ab].
  ring.
transitivity (\prod_(j : 'I_2) (\sum_(i in [predU (pred1 a) & (pred1 b)]) i)).
  rewrite big_ord_recr /=.
  rewrite big_ord_recr /=.
  rewrite big_ord0.
  rewrite mul1n.
  rewrite expnS.
  rewrite expn1.
  rewrite bigU /=; last first.
    by rewrite disjoint1.
  rewrite (big_pred1 a) //.
  by rewrite (big_pred1 b).
rewrite bigA_distr_big /=.
pose f1 := [ffun x : 'I_2 => match x with Ordinal O _ => a | Ordinal 1 _ => a | _ => a end].
pose f2 := [ffun x : 'I_2 => match x with Ordinal O _ => a | Ordinal 1 _ => b | _ => a end].
pose f3 := [ffun x : 'I_2 => match x with Ordinal O _ => b | Ordinal 1 _ => a | _ => a end].
pose f4 := [ffun x : 'I_2 => match x with Ordinal O _ => b | Ordinal 1 _ => b | _ => a end].
have f1f2 : f1 != f2.
  apply/eqP/ffunP.
  move/(_ (@Ordinal _ 1 _)).
  move/(_ erefl).
  rewrite !ffunE.
  by apply/eqP.
have f1f3 : f1 != f3.
  apply/eqP/ffunP.
  move/(_ (@Ordinal _ 0 _)).
  move/(_ erefl).
  rewrite !ffunE.
  by apply/eqP.
have f1f4 : f1 != f4.
  apply/eqP/ffunP.
  move/(_ (@Ordinal _ 0 _)).
  move/(_ erefl).
  rewrite !ffunE.
  by apply/eqP.
have f2f3 : f2 != f3.
  apply/eqP/ffunP.
  move/(_ (@Ordinal _ 0 _)).
  move/(_ erefl).
  rewrite !ffunE.
  by apply/eqP.
have f2f4 : f2 != f4.
  apply/eqP/ffunP.
  move/(_ (@Ordinal _ 0 _)).
  move/(_ erefl).
  rewrite !ffunE.
  by apply/eqP.
have f3f4 : f3 != f4.
  apply/eqP/ffunP.
  move/(_ (@Ordinal _ 1 _)).
  move/(_ erefl).
  rewrite !ffunE.
  by apply/eqP.
set tmp := ffun_on _.
transitivity (\sum_(f in [predU (pred1 f1) & [predU (pred1 f2) & [predU (pred1 f3) & (pred1 f4)]]]) \prod_(i < 2) f i).
  apply eq_bigl => /= f.
  move H : (f \in tmp) => [|].
    apply/esym.
    rewrite !inE /=.
    move/familyP : (H).
    move/(_ (@Ordinal _ O _)).
    move/(_ erefl).
    rewrite /= !inE.
    case/orP => /eqP H1.
    - move/familyP : (H).
      move/(_ (@Ordinal _ 1 _)).
      move/(_ erefl).
      rewrite /= !inE.
      case/orP => /eqP H2.
      + rewrite (_ : f == f1) //.
        apply/eqP/ffunP.
        case.
        case => [i|].
          rewrite ffunE /= -H1.
          congr (f (Ordinal _)).
          by apply eq_irrelevance.
        case=> i //.
        rewrite ffunE /= -H2.
        congr (f (Ordinal _)).
        by apply eq_irrelevance.
      + rewrite (_ : f == f2).
          by rewrite orbC.
        apply/eqP/ffunP.
        case.
        case => [i|].
          rewrite ffunE /= -H1.
          congr (f (Ordinal _)).
          by apply eq_irrelevance.
        case=> i //.
        rewrite ffunE /= -H2.
        congr (f (Ordinal _)).
        by apply eq_irrelevance.
    - move/familyP : (H).
      move/(_ (@Ordinal _ 1 _)).
      move/(_ erefl).
      rewrite /= !inE.
      case/orP => /eqP H2.
      + rewrite (_ : f == f3).
          by rewrite orbA /= orbC.
        apply/eqP/ffunP.
        case.
        case => [i|].
          rewrite ffunE /= -H1.
          congr (f (Ordinal _)).
          by apply eq_irrelevance.
        case=> i //.
        rewrite ffunE /= -H2.
        congr (f (Ordinal _)).
        by apply eq_irrelevance.
      + rewrite (_ : f == f4).
          by rewrite 2!orbA orbC.
        apply/eqP/ffunP.
        case.
        case => [i|].
          rewrite ffunE /= -H1.
          congr (f (Ordinal _)).
          by apply eq_irrelevance.
        case=> i //.
        rewrite ffunE /= -H2.
        congr (f (Ordinal _)).
        by apply eq_irrelevance.
  apply/esym/negbTE.
  rewrite !inE /=.
  move/negbT: H; apply contra => H.
  apply/familyP.
  case/orP : H.
    move/eqP => ->.
    case.
    case => [i|].
      by rewrite !inE ffunE eqxx.
    case=> // i.
    by rewrite !inE ffunE eqxx.
  case/orP.
    move/eqP => ->.
    case.
    case=> [i|].
      by rewrite !inE ffunE eqxx.
    case=> // i.
    by rewrite !inE ffunE eqxx orbC.
  case/orP.
    move/eqP => ->.
    case.
    case=> [i|].
      by rewrite !inE ffunE eqxx orbC.
    case=> // i.
    by rewrite !inE ffunE eqxx.
  move/eqP => ->.
  case.
  case=> [i|].
    by rewrite !inE ffunE eqxx orbC.
  case=> // i.
  by rewrite !inE ffunE eqxx orbC.
rewrite bigU /=; last first.
  by rewrite disjoint1 !inE /= negb_or f1f2 /= negb_or f1f3 f1f4.
rewrite bigU /=; last first.
  by rewrite disjoint1 !inE /= negb_or /= f2f3 f2f4.
rewrite bigU /=; last first.
  by rewrite disjoint1 !inE /=.
rewrite (big_pred1 f1) // (big_pred1 f2) // (big_pred1 f3) // (big_pred1 f4) //.
rewrite !big_ord_recr /= !big_ord0 !mul1n !ffunE /=.
ring.
Qed.
