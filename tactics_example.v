From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(* elim tactic *)

Goal forall n : nat, n + n = 2 * n.
Show Proof.
elim.
Show Proof.
done.
move=> n IH.
ring.
Qed.

(* strong induction *)
Check nat_ind.
Check Wf_nat.lt_wf_ind.

(* SSReflect idiom for strong induction *)
Lemma mylt_wf_ind : forall (n : nat) (P : nat -> Prop),
  (forall n0 : nat, (forall m : nat, (m < n0) -> P m) -> P n0) ->
  P n.
Proof.
move=> n.
move: (leqnn n).
move: {-2}n.
move: n.
elim.
  case=> //.
  move=> _ P.
  apply.
  done.
move=> n IH m mn P HP.
move: (HP).
apply => k km.
apply IH => //.
rewrite -ltnS.
by apply: leq_trans mn.
Qed.

(* TODO *)
Lemma another_ind : forall (P : nat -> Prop),
  P O -> P 1 ->
  (forall m, P m -> P m.+2) ->
  forall m, P m.
Proof.
move=> P P0 P1 IH m.
have : P m /\ P m.+1.
  elim: m => // n [] H1 H2.
  split=> //.
  by apply IH.
by case.
Qed.

Fixpoint another_ind2 (P : nat -> Prop) (P0 : P 0) (P1 : P 1)
  (H : forall m, P m -> P m.+2) m : P m :=
match m with
| O => P0
| 1 => P1
| n.+2 => H _ (another_ind2 P P0 P1 H n)
end.

Lemma yet_another_ind : forall (P : nat -> Prop),
  P O -> P 1 ->
  (forall m, P m /\ P m.+1 -> P m.+2) ->
  forall m, P m.
Proof.
move=> P P0 P1 H n.
have : P n /\ P n.+1.
  elim: n => // n [] H1 H2.
  split => //.
  by apply H.
by case.
Qed.

Module MutualNestedInductiveTypes.

Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
  fnil : forest A
| fcons : tree A -> forest A -> forest A.

Check tree_ind.

Scheme tree_ind2 := Induction for tree Sort Prop
with forest_ind2 := Induction for forest Sort Prop.

Check tree_ind2.

Fixpoint tsize {A : Set} (t : tree A) : nat :=
  match t with
  | node a f => 1 + fsize f
  end
with fsize {A : Set} (f : forest A) :=
  match f with
  | fnil => O
  | fcons t f' => tsize t + fsize f'
  end.

Fixpoint tflat {A : Set} (t : tree A) : seq A :=
  match t with
  | node a f => a :: fflat f
  end
with fflat {A : Set} (f : forest A) :=
  match f with
  | fnil => nil
  | fcons t f' => tflat t ++ fflat f'
  end.

Lemma exo15 A (t : tree A) : tsize t = size (tflat t).
Proof.
(*elim: t => h t /=.*)
(*elim/tree_ind: t => // h t /=.*)
(*Fail elim/tree_ind2 : t.*)
apply: (tree_ind2 _ (fun t => tsize t = size (tflat t)) (fun f => fsize f = size (fflat f))) t => //.
Abort.

Inductive ltree (A : Set) : Set :=
  lnode : A -> list (ltree A) -> ltree A.

Check ltree_ind.

Section ltree_ind2.

Variable A : Set.
Variable (P : ltree A -> Prop).
Variable (Q : list (ltree A) -> Prop).
Hypothesis H0 : Q nil.
Hypothesis H1 : forall (t : ltree A), P t -> forall l : list (ltree A), Q l -> Q (cons t l).
Hypothesis H : forall (a : A) (l : list (ltree A)), Q l -> P (lnode A a l).

Fixpoint ltree_ind2 (t : ltree A) : P t :=
  match t with
  | lnode a l =>
    H a l
      ((fix l_ind (l' : list (ltree A)) : Q l' :=
          match l' with
            | nil => H0
            | cons h' t' => H1 h' (ltree_ind2 h') t' (l_ind t')
          end
       ) l)
  end.

End ltree_ind2.

Fixpoint lsize {A : Set} (l : ltree A) : nat :=
  match l with
    | lnode a l =>
      1 + foldr addn O (map lsize l)
  end.

Fixpoint lflat {A : Set} (l : ltree A) : seq A :=
  match l with
    | lnode a l => a :: flatten (map lflat l)
  end.

Lemma exo16 A (t : ltree A) : lsize t = size (lflat t).
Proof.
(*elim : t => h t /=.*)
apply: (ltree_ind2 _ (fun t => lsize t = size (lflat t)) (fun l => foldr addn O (map lsize l) = size (flatten (map lflat l)))) t => //.
Abort.

End MutualNestedInductiveTypes.

(* rewrite tactic *)

Goal forall n : nat, n = 0 -> forall m : nat, m + n = m.
move=> n n0 m.
rewrite n0.
rewrite addn0.
done.
Qed.

Goal forall n : nat, n = 0 -> forall m : nat, n + m = n.
move=> n n0 m.
rewrite n0.
(* rewrite both occurrences *)
Undo.
rewrite {1}n0.
(* rewrite only the first occurrence *)
Undo.
rewrite {2}n0.
(* rewrite only the second occurrence *)
Undo.
rewrite {-2}n0.
(* rewrite all the occurrences except the second one *)
Undo.
Abort.
(* NB: this is the same occurrence switch <occ-switch> as we used in the proof of strong induction *)

(* the following two example are taken from the ssreflect manual *)

Goal forall x y : nat,
  (forall t u, t + u = u + t) ->
  x + y = y + x.
move=> x y H.
(* rewrite H. changes the lhs, what if I want to change the rhs? *)
(* <rstep> =def= [<r-prefix>]<r-item>
   <r-prefix> =def= ... [ [<r-pattern>] ]
   <r-pattern> =def= <term> | ...
*)
Fail rewrite {2}H.
rewrite [y + _]H.
done.
Qed.

Goal forall x y : nat,
  (forall t u, t + u * 0 = t) ->
  x + y * 4 + 2 * 0 = x + 2 * 0.
Proof.
move=> x y H.
Fail rewrite [x + _]H.
(* rewrite does not try to recover from a pattern-match failure *)
rewrite [x + 2 * _]H.
Abort.

(* contextual pattern *)
Goal forall (a b c : nat),
  (a + b) + (2 * (b + c)) = 0.
move=> a b c.
(* commute b and c *)
Fail rewrite {2}addnC.
rewrite [b + _]addnC.
rewrite [in 2 * _]addnC.
rewrite [in X in _ + X]addnC.
Abort.

(* the same as at the top of the file but detailed, naming conventions to be explained later *)
Goal forall n : nat, n + n = 2 * n.
elim.
  rewrite addn0.
  rewrite muln0.
  done.
move=> n IH.
rewrite mulnS.
rewrite -IH.
rewrite -addSnnS.
rewrite addnCA.
rewrite -addn2.
rewrite addnA.
done.
Qed.

(* structured scripts *)

Lemma undup_filter {A : eqType} (P : pred A) (s : seq A) :
  undup (filter P s) = filter P (undup s).
Proof.
elim: s => // h t IH /=.
case: ifP => /= [Ph | Ph].
- case: ifP => [Hh | Hh].
  + have : h \in t.
      move: Hh; by rewrite mem_filter => /andP [].
    by move=> ->.
  + have : h \in t = false.
      apply: contraFF Hh; by rewrite mem_filter Ph.
    move=> -> /=; by rewrite Ph IH.
- case: ifP => // ht.
  by rewrite IH /= Ph.
Qed.

Fixpoint flat {A : eqType} (l : seq (seq A)) : seq A :=
  if l is h :: t then h ++ flat t else [::].

(* Structure the following script *)
Lemma exo17 {A : eqType} (s : seq (seq A)) a :
  reflect (exists2 s', s' \in s & a \in s') (a \in flat s).
Proof.
elim: s.
right.
by case.
move=> h t IH.
rewrite /= mem_cat.
apply: (iffP idP).
case/orP.
move=> H.
exists h.
by rewrite in_cons eqxx.
done.
case/IH.
move=> /= s st ys.
exists s.
by rewrite in_cons st orbT.
done.
case=> s'.
rewrite in_cons.
case/orP.
move=> s'h as'.
apply/orP.
left.
move/eqP : s'h.
move=> <-.
done.
move=> s't as'.
apply/orP.
right.
apply/IH.
by exists s'.
Qed.

(* congr tactic *)

Goal forall a b c a' b' c', a + b + c = a' + b' + c'.
move=> a b c a' b' c'.
congr (_ + _ + _).
Abort.

(* equation generation *)

Goal forall s1 s2 : seq nat, rev (s1 ++ s2) = rev s2 ++ rev s1.
move=> s1.
move H : (size s1) => n.
move: n s1 H.
elim.
  case => //.
  rewrite /=.
  move=> _ s2.
  by rewrite cats0.
move=> n IH.
case=> // h t.
case=> tn.
move=> s2.
rewrite /=.
rewrite rev_cons.
rewrite IH //.
rewrite rcons_cat.
by rewrite rev_cons.
Qed.

(* NB: from the ssreflect manual *)
Goal forall a b : nat,
  a <> b.
move=> a b.
case H : a => [|n].
Show 2.
Abort.

Module Wlog.

Section wlog.

Variable a : nat.
Hypothesis a1 : 1 < a.

Lemma artificial (k l : nat) : k < l \/ l < k -> a ^ k != a ^ l.
Proof.
wlog : k l / k < l.
  move=> H.
  case=> kl.
    apply H => //; by left.
  rewrite eq_sym.
  apply H => //; by left.
move=> kl _.
by rewrite eqn_exp2l // neq_ltn kl.
Qed.

End wlog.

(* NB: from ssrnat.v *)
Lemma leq_min m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof.
wlog : n1 n2 / n2 <= n1.
  move=> H.
  have : n2 <= n1 \/ n1 <= n2 by apply/orP/leq_total.
  case=> n12.
    by apply H.
  rewrite minnC andbC; by apply H.
move=> n12.
rewrite /minn.
rewrite ltnNge.
rewrite n12.
rewrite /=.
case mn2 : (m <= n2).
  by rewrite (leq_trans mn2 n12).
by rewrite andbC.
Qed.

End Wlog.

(* Search command *)

Search (_ < _)%N.
Search (_ < _ = _)%N.

Search _ (_ <= _)%N.
Search _ (_ <= _)%N "-"%N.
Search _ (_ <= _)%N "-"%N addn.
Search _ (_ <= _)%N "-"%N addn "add".
Search _ (_ <= _)%N "-"%N addn "add" in ssrnat.

(* commutativity of addition? *)
Search (_ + _ = _ + _)%N.
Search _ "commutative".
Search _ commutative.
Search _ addn "C" in ssrnat.
