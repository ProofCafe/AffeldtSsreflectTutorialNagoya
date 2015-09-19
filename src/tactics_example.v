Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(* elim tactic *)

Goal forall n : nat, n + n = 2 * n.
Show Proof.
elim.
Show Proof.
done.
move=> n IH.
ring.
Qed.

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
Abort.                                      (* o.k. *)
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
rewrite H.                                  (* x + y が書き換えられる。 *)
Undo.
rewrite [y + _]H.                           (* y + x が書き換えられる。 *)
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
Abort.                                      (* ok. *)

(* contextual pattern *)
Goal forall (a b c : nat),
  (a + b) + (2 * (b + c)) = 0.
move=> a b c.
(* commute b and c *)
Fail rewrite {2}addnC.
rewrite [b + _]addnC.         (* b + c が対象 *)
rewrite [in 2 * _]addnC.      (* 2 * (c + b) の中のどっかが対象 *)
rewrite [in X in _ + X]addnC. (* (a + b) + 2 * (b + c) の中の 2 * (b + c) の中のどこがが対象 *)
Abort.                        (* ok. *)

(* the same as above but detailed, naming conventions to be explained later *)
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
(* ringを使う。 *)
Goal forall n : nat, n + n = 2 * n.
  by elim=> [|n IH]; ring.
Qed.

(* structured scripts *)

Lemma undup_filter {A : eqType} (P : pred A) (s : seq A) :
  undup (filter P s) = filter P (undup s).
Proof.
elim: s => // h t IH /=.
case: ifP => /= [Ph | Ph].
- case: ifP => [Hh | Hh].
  + have ->// : h \in t.
      move: Hh; by rewrite mem_filter => /andP [].
  + have : h \in t = false.
      apply: contraFF Hh; by rewrite mem_filter Ph.
    move=> -> /=; by rewrite Ph IH.
- case: ifP => // ht.
  by rewrite IH /= Ph.
Qed.

Fixpoint flat {A : eqType} (l : seq (seq A)) : seq A :=
  if l is h :: t then h ++ flat t else [::].

(* Structure the following script *)
Lemma exo10 {A : eqType} (s : seq (seq A)) a :
  reflect (exists2 s', s' \in s & a \in s') (a \in flat s).
Proof.
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

(* from the ssreflect manual *)

Goal forall a b : nat,
  a <> b.
move=> a b.
case H : a => [|n].
Show 2.
Abort.                                      (* ok. *)

(* congr tactic *)

Goal forall a b c a' b' c', a + b + c = a' + b' + c'.
move=> a b c a' b' c'.
congr (_ + _ + _).
Abort.                                      (* |- a = a', |- b = b',  |- c = c' *)

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

(* END *)
