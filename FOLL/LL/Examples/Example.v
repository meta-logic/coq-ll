(* Add LoadPath "../" . *) 
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Export Sorting.PermutSetoid.
From Stdlib Require Export Sorting.PermutEq.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.


From Stdlib Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.FLLMetaTheory.
Require Export LL.Multisets.
Require Export LL.Eqset.


Module SLL := SqBasic NatSet.
Export SLL.


#[local] Hint Unfold Subst : core .
Example test1: |-F- [] ; [] ; UP(F{fun _ x=> atom(a1 1 (var x))} :: E{fun _ x=> perp(a1 1 (var x))} :: nil).
Proof.
  eapply tri_fx;intros.
  autounfold;simpl.
  eapply tri_store ; solveF.
  eapply tri_store ; solveF.
  eapply tri_dec1 with (F:=fun T : Type => ex (fun x0 : T => perp (a1 1 (var x0)))) ; solveF.
  eapply tri_ex.
  autounfold. simpl.
  solveF.
Qed.

Definition p := A0 1.
Definition q := A0 3.
Definition r := A0 5.
#[local] Hint Unfold p q r : core.

Example sequent: |-F- [] ; [] ; UP( [ (p ⁺ & q ⁺) $  ⊥ $ (? p ⁻) $ (? q ⁻) ] ).
Proof.
  NegPhase.
  eapply tri_dec2 with (F:= (A0 1) ⁻) ; solveF.
  intro H ;inversion H ; solveF. solveF. inversion H1.
  eapply tri_dec2 with (F:= (A0 3) ⁻) ; solveF.
  intro H ;inversion H ; solveF. solveF. inversion H1.
Qed.
