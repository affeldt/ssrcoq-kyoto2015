(* example of duplication *)

(* Prop is impredicative *)

Definition DupProp : Prop := forall P : Prop, P -> P /\ P.

Definition DupPropProof : DupProp := fun P p => conj p p.

Lemma DupPropSelf : DupProp /\ DupProp.
Proof.
apply DupPropProof.
exact DupPropProof.
Show Proof.
Undo 2.
exact (DupPropProof _ DupPropProof).
Qed.

(* Type is predicative *)

Set Printing Universes.

Polymorphic Definition DupType : Type := forall P : Type, P -> P * P.
Print DupType.

Polymorphic Definition DupTypeProof : DupType := fun P p => (p, p).

Check (DupTypeProof nat O).
Check (nat * nat)%type : Set.
Check (DupTypeProof Prop True).
Check (Prop * Prop)%type : Type.

Lemma DupTypeSelf : DupType * DupType.
Proof.
exact (DupTypeProof _ DupTypeProof).
Qed.

Unset Printing Universes.

(* example of the identity function *)

Set Printing Universes.

Definition myidProp : Prop := forall A : Prop, A -> A.

Definition myidPropProof : myidProp := fun (A : Prop) (a : A) => a.

Check myidPropProof : forall A : Prop, A -> A.
Check myidProp.
Check (myidPropProof _ myidPropProof).

Definition myidType : Type := forall A : Type, A -> A.

Definition myidTypeProof : myidType := fun (A : Type) (a : A) => a.

Check myidTypeProof : forall A : Type, A -> A.
Check myidType.
Fail Check (myidTypeProof _ myidTypeProof).

Unset Printing Universes.

(* Universe polymorphism *)

Set Printing Universes.

Polymorphic Definition pidType : Type := forall A : Type, A -> A.
Check pidType.

Polymorphic Definition pidTypeProof : pidType := fun (A : Type) (a : A) => a.
Check pidTypeProof.

Check (pidTypeProof _ pidTypeProof).
