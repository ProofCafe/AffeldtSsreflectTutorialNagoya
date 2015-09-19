(* example of duplication *)

(* Prop is impredicative *)

Definition DupProp : Prop := forall P : Prop, P -> P /\ P.

Definition DupPropProof : DupProp := fun P p => conj p p.

Lemma DupPropSelf : DupProp /\ DupProp.
Proof.
apply DupPropProof.
exact DupPropProof.
Qed.

(* Type is predicative *)

Set Printing Universes.

Definition DupType : Type := forall P : Type, P -> P * P.

Definition DupTypeProof : DupType := fun P p => (p, p).

Check (DupTypeProof nat O).
Check (DupTypeProof Prop True).

Lemma DupTypeSelf : DupType * DupType.
Proof.
apply DupTypeProof.
exact DupTypeProof.
Fail Qed.
Abort.

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


