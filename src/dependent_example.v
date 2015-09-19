Require Import ssreflect.

(* NB : exo7 and exo8 from the JFR tutorial *)

Lemma exo7 (P : nat -> Prop) : ~ (exists x, P x) -> forall x, ~ P x.
Proof.
Abort.

Lemma exo8 (A : Prop) (P : nat -> Prop) : 
  (exists x, A -> P x) -> (forall x, ~ P x) -> ~ A.
Proof.
Abort.

Lemma exo9 : 
  (exists P : nat -> Prop, forall n, P n) -> 
  forall n, exists P : nat -> Prop , P n.
Proof.
Abort.

Require Import ssrfun ssrbool eqtype ssrnat seq path.

Definition ordered : seq nat -> bool := sorted ltn.

Inductive map :=
| mkMap : forall s : seq (nat * bool), ordered (unzip1 s) -> map.

Inductive int (n : nat) :=
| mkInt : forall s : seq bool, size s = n -> int n.

