From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Print finType.
(* Notation finType := Finite.type *)
Print Finite.type.
(* Record type : Type := Pack { sort : Type;  _ : Finite.class_of sort;  _ : Type } *)
Print Finite.class_of.
(* Record class_of (T : Type) : Type := Class
  { base : Choice.class_of T;
    mixin : Finite.mixin_of (Equality.Pack base T) } *)
Print Finite.mixin_of.
(* Record mixin_of (T : eqType) : Type := Mixin
  { mixin_base : Countable.mixin_of T;
    mixin_enum : seq T;
    _ : Finite.axiom (T:=T) mixin_enum } *)


Check 'I_3.
Check (enum 'I_3).

Definition o0 := @Ordinal 3 O erefl.
Definition o1 := @Ordinal 3 1 erefl.
Definition o2 := @Ordinal 3 2 erefl.

Goal @Ordinal 3 1 erefl = insubd ord0 1.
apply val_inj => /=.
rewrite val_insubd.
done.
Abort.

Check (val o2).
Check (valP o2).

Eval compute in o1 < o2.
Set Printing Coercions.
Check (o1 < o2).
Unset Printing Coercions.
Eval compute in o1 != o2.

Goal o1 <> o2.
done.
Qed.

Axiom H : 2 < 3.
Definition o2' := @Ordinal 3 2 H.

Goal o2 = o2'.
Fail done.
rewrite /o2 /o2'.
congr Ordinal.
apply eq_irrelevance. (* unicity of identity proofs as defined in eqtype.v *)
Qed.

Goal o2 = o2'.
apply val_inj.
done.
Qed.

Goal enum 'I_3 = [:: o0; o1; o2].
rewrite enum_ordS.
congr (_ :: _).
  apply val_inj.
  done.
rewrite enum_ordS.
rewrite /=.
congr (_ :: _).
  apply val_inj.
  rewrite /=.
  done.
rewrite enum_ordS.
rewrite /=.
congr (_ :: _).
  apply val_inj.
  rewrite /=.
  done.
apply size0nil.
rewrite size_map.
rewrite size_map.
rewrite size_map.
rewrite size_enum_ord.
done.
Qed.
