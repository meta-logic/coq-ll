(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Soundness
This file proves the soundness of the triadic (focused) system of linear logic *)

Require Export SequentCalculi.
Require Export Permutation.
(* Require Export MSet. *)
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Module FFSoundness (DT : Eqset_dec_pol).
  
  
  Module Export Sys :=  SqSystems DT.

  Theorem Soundness : forall (B : list Lexp) n  (M : list Lexp) A ,
      LexpPos M ->
      n |-F- B ; M ; A  ->  |-- B ; M ++ (Arrow2LL A).
    intros B n M  A MPos.
    Proof with InvTac.
    generalize dependent B.
    generalize dependent M.
    generalize dependent A.
    induction n  using strongind;
      intros A M MPos B H1.
    + inversion H1;subst ...
      (* intit 2*)
      rewrite H0.
      eapply sig2_copy with (F:=  A3°);auto.

    (* INDUCTIVE CASES *)
    + inversion H1;subst.
      ++ (* tensor *)
        apply H in H3;auto.
        apply H in H4;auto.
        
        simpl in *.

        rewrite H2.
        eapply sig2_tensor with (N:=M0) (M:=N) (F:=F) (G:=G);simpl.
        solve_permutation.
        assert(N ++ [F] =mul= F ::N) as __Hmset1__ by (rewrite union_comm; reflexivity).
        rewrite __Hmset1__ in H3.
        assumption.
        assert(M0 ++ [G] =mul= G ::M0) as __Hmset2__  by (rewrite union_comm; reflexivity).
        rewrite __Hmset2__  in H4.
        eassumption.
        eapply LPos2; eassumption.
        eapply LPos3; eassumption.
      ++ (* oplus *)
        apply H in H2;auto.
        simpl. simpl in H2.
        eapply sig2_plus1 with (F:=F) (M:=M) ...
        rewrite union_comm in H2.
        eauto.
      ++ (* oplus2 *)
        apply H in H2;auto.
        simpl. simpl in H2.
        eapply sig2_plus2 with (G:=G) (M:=M).
        solve_permutation.
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
        eapply sig2_par;auto.
        assert ( M ++ F :: G :: M0 =mul=  F :: G :: M ++ M0) by solve_permutation.
        rewrite H0 in H2.
        eauto.

      ++ (* with *)
        apply H in H2;auto.
        apply H in H3;auto.
        simpl in *.
        apply sig2_with with (F:=F) (G:=G) (M:=M ++ M0).
        solve_permutation.
        
        assert( M ++ ([F] ++ M0) =mul=  [F] ++ (M ++ M0)) by auto.
        rewrite H0 in H2.
        eauto.
        assert( M ++ ([G] ++ M0) =mul=  [G] ++ (M ++ M0)) by auto.
        rewrite H0 in H3.
        eauto.
      ++  (* ? *)
        apply H in H2;auto.
        simpl in *.
        apply sig2_quest with (F:=F) (M := M ++ M0).
        solve_permutation.
        rewrite union_comm in H2.
        eauto.
      ++ (* store *)
        apply H in H3;auto.
        simpl in *.
        rewrite <- union_assoc in H3.
        simpl in H3.
        eassumption.
        apply LPos1 with (L:=[F] ++ M);auto.
        simpl;split;auto.
        apply AsyncEqNeg;auto.

      ++ (* decide *)
        apply H in H4;auto.
        simpl in *.
        rewrite H3.
        simpl.
        rewrite app_nil_r.
        rewrite union_comm in H4.
        eassumption.
        apply  LPos1 in H3;auto.
        eapply LPos3 with (L:= [F] ++ L') ;auto.

      ++ (* decide *)
        apply H in H4;auto.
        simpl in *.
        rewrite H3.
        eapply sig2_copy with (F:=F);auto.
        rewrite H3 in H4.
        MReplace ( (F::M)++[]) (M ++ [F]) ...
      ++ (* exists *)
        apply H in H2;auto.
        simpl in *.
        rewrite union_comm in H2.
        rewrite union_comm.
        eapply sig2_ex;eauto.
      ++ (* forall *)
        simpl in *.
        eapply sig2_fx;auto.
        intro x.
        generalize (H2 x);intro.
        apply H in H0;auto.
        simpl in *.
        assert(Subst FX x :: M ++ M0 =mul=  M ++ (Subst FX x) :: M0) by solve_permutation.
        rewrite H3.
        auto.
  Qed.

End FFSoundness.
