(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Sets, Decidable Sets and Polarities
*)

Require Import Arith.

(** Just a set 
 *)

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




