Add LoadPath "../../".
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.


Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.FLLMetaTheory.
Require Export LL.Multisets.
Require Export LL.Eqset.

  
Module SLL := SqBasic NatSet.
Export SLL.


Example test1: |-F- [] ; [] ; UP(F{fun _ x=> atom(a1 1 (var x))} :: E{fun _ x=> perp(a1 1 (var x))} :: nil).
Proof with simplifyFormula;solveF.
  NegPhase .
  eapply tri_dec1 with (F:=fun T : Type => ex (fun x0 : T => perp (a1 1 (var x0)))) ...
  eapply tri_ex ...
  autounfold. simpl.
  auto ...
Qed.

Definition p := A0 1.
Definition q := A0 3.
Definition r := A0 5.
Hint Unfold p q r.

Example sequent: |-F- [] ; [] ; UP( [ (p ⁺ & q ⁺) $  ⊥ $ (? p ⁻) $ (? q ⁻) ] ).
Proof with simplifyFormula;solveF.
  NegPhase. (* Negative phase *)
  eapply tri_dec2 with (F:= p ⁻) ...
  autounfold ...
  eapply tri_dec2 with (F:= q ⁻) ...
  autounfold ...
Qed.