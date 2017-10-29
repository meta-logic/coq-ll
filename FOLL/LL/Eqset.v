(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Sets, Decidable Sets and Polarities
*)

Require Import Arith.

(* Auxilarly arithmetic results *)
Lemma GtZero : forall n, n >0 -> exists n', n = S n'.
Proof.
  intros.
  destruct n.
  inversion H.
  exists n;auto.
Qed.

Lemma plus_le_reg_r: forall n m q : nat, n + q <= m + q -> n <= m.
Proof.
  intros.
  assert (n+q = q + n) by (apply plus_comm).
  assert (m+q = q + m) by (apply plus_comm).
  rewrite H0 in H. rewrite H1 in H.
  eapply plus_le_reg_l in H.
  assumption.
Qed.

(** Just a set *)

Module Type Eqset.
  Parameter A : Type.
End Eqset.

(** A set with decidable equality
 *)
Module Type Eqset_dec <: Eqset.
  Parameter A : Type.
  Parameter eqA_dec : forall x y : A, {x = y} + {x <> y}.
End Eqset_dec.

(** A set with decidable equality and a function defining which atoms are positive
 *)

Module Type Eqset_dec_pol <: Eqset_dec.
  Parameter A : Type.
  Parameter eqA_dec : forall x y : A, {x = y} + {x <> y}.
  Parameter isPositive : nat -> bool.
End Eqset_dec_pol.

(** An example of Eqset_dec_pol *)
Module NatSet <: Eqset_dec_pol.
  Definition A := nat.
  Definition eqA_dec := Nat.eq_dec.
  Fixpoint isPositive (n:nat) :=
    match n with
    | 0%nat => false
    | 1%nat => true
    | S (S n) => isPositive n
    end.
End NatSet.




