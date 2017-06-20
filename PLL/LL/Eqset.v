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

