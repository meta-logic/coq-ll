(* Add LoadPath "../../".   *)
Require Export SequentCalculi.
Require Export TriSystem.
Require Export StructuralRules.
Require Import StructuralRulesTriSystem.
Require Export MSet.
Require Export InvTensor.
Require Export InvCopy.
Require Export InvPlus.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.


(********************* COMPLETENESS ************************)


Theorem CompletenessAux : forall B L n,  n |-- B ; L -> exists m, m |-F- B ; empty ; UP L.
  intros.
  generalize dependent B.
  generalize dependent L.
  induction n  using strongind;
    intros L  B H1.
  +  (* Base case *)
    inversion H1;subst;simpl.
    ++ (* Init *)
      assert (3 |-F- B ; empty ; UP [A0 ⁺ ;  A0 ⁻]).
      repeat eapply tri_store;auto.
      eapply tri_dec1 with (F:=A0 ⁺) (L' := [A0 ⁻]);auto.
      eapply tri_init1.
      eapply EquivUpArrow.
      eassumption.
      rewrite H.
      auto.
    ++ (* one *)
      assert (2 |-F- B ; empty ; UP [1]).
      eapply tri_store;auto;simpl.
      eapply tri_dec1 with (F:=1);auto.
      eapply tri_one .
      eapply EquivUpArrow.
      eassumption.
      solve_permutation.
    ++ (* top *)
      assert (0 |-F- B ; empty ; UP (⊤ :: M)).
      eapply tri_top.
      eapply EquivUpArrow.
      eassumption.
      solve_permutation.
  + (* Inductive Cases *)
    inversion H1;subst.
    ++ (* Bot *)
      apply H in H3;auto.
      destruct H3.
      assert(S x |-F- B ; empty ; UP (⊥ :: M)).
      eapply tri_bot;auto.
      eapply EquivUpArrow.
      eassumption.
      solve_permutation.
    ++ (* PAR *)
      apply H in H3;auto.
      destruct H3.
      assert(S x |-F- B ; empty ; UP (F $ G :: M)).
      eapply tri_par;auto.
      eapply EquivUpArrow.
      eassumption.
      solve_permutation.
    ++ (* Tensor *)
      apply H in H3;auto.
      apply H in H4;auto.
      destruct H3.
      destruct H4.
      apply EquivUpArrow with (L':= M ++ [F])in H0; auto. destruct H0.
      apply EquivUpArrow with (L':= N ++ [G])in H3; auto. destruct H3.
      assert (exists m, m |-F- B ; [] ++ [] ++ [F ** G]; UP (M ++ N)).
      eapply InvTensor; simpl;eauto.
      
      
      inversion H4.
      simpl in H5.
      eapply EquivUpArrow with (L:=[F ** G] ++ (M ++ N));auto.
      eapply tri_store;eauto.
      simpl.
      solve_permutation.
      solve_permutation.

    ++ (* OPLUS1 *)
      apply H in H3;auto.
      destruct H3.
      assert (exists m, m |-F- B ; [] ++ [F ⊕ G] ; UP M).
      apply EquivUpArrow with (L' := M ++ [F]) in H0;auto.
      destruct H0.
      eapply InvOplus1. apply H0. simpl. auto.
      solve_permutation.
      destruct H3.
      simpl in H3.
      assert( S x0 |-F- B ; [] ; UP (F ⊕ G :: M)).
      eapply tri_store;auto.
      eapply EquivUpArrow.
      eapply H4.
      solve_permutation.
    ++ (* OPLUS 2 *)
      apply H in H3;auto.
      destruct H3.
      assert (exists m, m |-F- B ; [] ++ [F ⊕ G] ; UP M).
      apply EquivUpArrow with (L' := M ++ [G]) in H0;auto.
      destruct H0.
      eapply InvOplus2. apply H0. simpl. auto.
      solve_permutation.
      destruct H3.
      simpl in H3.
      assert( S x0 |-F- B ; [] ; UP (F ⊕ G :: M)).
      eapply tri_store;auto.
      eapply EquivUpArrow.
      eapply H4.
      solve_permutation.
    ++ (* With *)
      apply H in H3;auto.
      apply H in H4;auto.
      destruct H3.
      destruct H4.
      assert (S (Init.Nat.max x x0) |-F- B ;  [] ; UP ([F & G] ++ M )).
      eapply tri_with;auto.
      eapply EquivUpArrow.
      apply H4.
      rewrite H2.
      solve_permutation.
    ++ (* Copy *)
      rewrite H3 in H4.
      apply H in H4;auto.
      destruct H4.
      
      assert (F € B).
      rewrite meq_cons_app in H2.
      rewrite H2.
      auto.
      
      apply member_then_eq in H4.
      destruct H4 as [B1  [B2 H2']]. 
      rewrite H2 in H0.
      assert (HB' : B1 ++ ([F] ++ B2) =mul= (B1 ++ B2) ++ [F]) by solve_permutation.
      rewrite meq_cons_append in H0.
      
      apply InvCopy in H0.
      
      destruct H0.
      eexists.
      rewrite meq_cons_append in H2.
      rewrite H2. eauto.
      simpl. auto.
      
    ++ (* Quest *)
      apply H in H3;auto.
      destruct H3.
      
      apply EquivUpArrow with (L := [? F] ++ M) (n:= S x);auto.
      eapply tri_quest;auto.
      
      apply TriExchange with (B:= [F] ++ B ) (M:=[]);auto.
      solve_permutation.
    ++ (* Bang *)
      apply meq_sym in H2.
      apply MulSingleton in H2;subst.
      
      apply H in H3;auto.
      destruct H3.
      eexists.
      eapply tri_store;auto.
      simpl.
      eapply tri_dec1 with (F:= ! F);auto.
      eapply tri_bang.
      apply H0.
Qed.




Theorem Completeness : forall B L M n,  n |-- B ; M ++ L ->
                                                  lexpPos M ->
                                                  exists m, m |-F- B ; M ; UP L.
  intros.
  assert (exists m, m |-F- B ; [] ; UP (M ++ L)).
  eapply CompletenessAux;eauto.
  destruct H1.
  apply StoreInversionL with (L:=L) in H1;auto.
Qed.





