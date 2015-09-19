Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Check 'I_3.
Check (enum 'I_3).

Definition o0 := @Ordinal 3 O erefl.
Definition o1 := @Ordinal 3 1 erefl.
Definition o2 := @Ordinal 3 2 erefl.

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





