(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Soundness
This file proves the soundness of the triadic (focused) system of linear logic *)

(* Add LoadPath "../" .  *)
From Stdlib Require Export Permutation.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Export Sorting.PermutSetoid.
From Stdlib Require Export Sorting.PermutEq.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Export LL.SequentCalculiBasicTheory.


Set Implicit Arguments.

Module FFSoundness (DT : Eqset_dec_pol).
  Module Export Sys :=  SqBasic DT.

  Theorem Soundness : forall (B : list Lexp) n  (M : list Lexp) A ,
      LexpPos M ->
      n |-F- B ; M ; A  ->  |-- B ; M ++ (Arrow2LL A).
  Proof.
    intros B n M A MPos.
    generalize dependent B.
    generalize dependent M.
    generalize dependent A.
    induction n  using strongind;
      intros A M MPos B H1.
    + inversionF H1;subst ;solveF.
      eapply sig2_copy with (F:=  A3°);auto.

    (* INDUCTIVE CASES *)
    + inversionF H1.
      ++ (* tensor *)
        apply sig2_tensor with (N:=M0) (M:=N) (F:=F) (G:=G) ; solveF.
        MReplace (F :: N) ( N ++ (Arrow2LL (DW F) )) .
        apply H with n0 ; solveF.
        MReplace (G :: M0) ( M0 ++ (Arrow2LL (DW G) )) .
        apply H with m ; solveF.
      ++ (* oplus *)
        apply H in H2 ; solveF.
        simpl in *.
        eapply sig2_plus1 with (F:=F) (M:=M) ; solveF.
        rewrite union_comm in H2 ; solveF.
      ++ (* oplus2 *)
        apply H in H2 ; solveF.
        simpl in  *.
        eapply sig2_plus2 with (G:=G) (M:=M) ; solveF.
        rewrite union_comm in H2.
        eauto.
      ++ (* bang *)
        apply H in H2;auto.
        simpl. simpl in H2.
        eapply sig2_bang with (F:=F);auto.
      ++ (* Release *)
        apply H in H3;auto.
      ++ (* bottom *)
        apply H in H2;auto.
        simpl in *.
        eapply sig2_bot;eauto.
      ++ (* par *)
        apply H in H2;auto.
        simpl in *.
        eapply sig2_par ; solveF.
        MReplace  (F :: G :: M ++ M0) (M ++ F :: G :: M0). solveF.
      ++ (* with *)
        apply H in H2 ; solveF.
        apply H in H3 ; solveF.
        simpl in *.
        apply sig2_with with (F:=F) (G:=G) (M:=M ++ M0) ; solveF.
        MReplace ( F :: M ++ M0) ( M ++ F :: M0) ; solveF.
        MReplace (G :: M ++ M0) ( M ++ G :: M0). solveF.
      ++  (* ? *)
        apply H in H2 ; solveF.
        simpl in *.
        apply sig2_quest with (F:=F) (M := M ++ M0) ; solveF.
        rewrite union_comm in H2. solveF.
      ++ (* store *)
        apply H in H3 ; solveF.
        simpl in *.
        rewrite <- union_assoc in H3. solveF.
      ++ (* decide *)
        apply H in H4 ; solveF.
        simpl in *.
        rewrite app_nil_r.
        rewrite H3.
        MReplace (F :: L') ( L' ++ [F]). solveF.
      ++ (* decide *)
        apply H in H4 ; solveF.
        simpl in *.
        rewrite H3.
        eapply sig2_copy with (F:=F) ; solveF.
        rewrite H3 in H4.
        MReplace ( (F::M)++[]) (M ++ [F]). solveF.
      ++ (* exists *)
        apply H in H2;auto.
        simpl in *.
        rewrite union_comm in H2.
        rewrite union_comm.
        eapply sig2_ex ; solveF.
        eauto.
      ++ (* forall *)
        simpl in *.
        eapply sig2_fx ; solveF.
        intro x.
        generalize (H2 x);intro.
        apply H in H0 ; solveF.
        simpl in *.
        MReplace (Subst FX x :: M ++ M0) ( M ++ Subst FX x :: M0). solveF.
  Qed.

End FFSoundness.
