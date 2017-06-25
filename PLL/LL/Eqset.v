(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)


(** ** Decidable Sets

The type for atomic propositions must be decidable. We use in the Syntax Module, as a parameter, an Eqset_dec as defined below. 

*)




Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Relations.Relations.

Module Type Eqset_dec.

  Parameter A : Type.
  Parameter eqA : A -> A -> Prop.   
  Notation "X =A= Y" := (eqA X Y) (at level 70).

  Parameter eqA_dec : forall x y, {x =A= y} + {~x =A= y}.
  Parameter eq_dec : forall x y : A, {x = y} + {x <> y}.
  
End Eqset_dec.

