(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Soundness of the Focusing system
*)


Require Export TriSystem.
Require Export SequentCalculi.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

#[local] Hint Resolve Nat.le_max_r Nat.le_max_l : core .

Theorem Soundness : forall B n  M A ,
    lexpPos M ->
    n |-F- B ; M ; A  -> exists m, m |-- B ; M ++ (Arrow2LL A).
  intros B n M  A MPos.
  Proof.  
    
    generalize dependent B.
    generalize dependent M.
    generalize dependent A.
    induction n using strongind;
      intros A M MPos B H1.
    + inversion H1;subst;eexists;simpl.
      ++ (* init1 *)
        eapply sig2h_init.
        eauto.
      ++ (* init2 *)
        rewrite H.
        eapply sig2h_copy with (F:= A0 ⁻);auto.
        eapply sig2h_init.
        eauto.
      ++ (* one *)
        eapply sig2h_one;auto.
      ++ (* top *)
        eapply sig2h_top.
        eauto.

    (** INDUCTIVE CASES *)
    + inversion H1;subst.
      ++ (* tensor *)
        apply H in H3;auto.
        apply H in H4;auto.
        inversion H3 as [n1 H3'].
        inversion H4 as [n2 H4'].
        simpl in H3'.
        simpl in H4'.
        eexists.
        simpl.
        rewrite H2.
        eapply sig2h_tensor with (N:=M0) (M:=N) (F:=F) (G:=G);simpl.
        solve_permutation.
        assert(N ++ [F] =mul= F ::N) as __Hmset1__ by (rewrite union_comm_app; reflexivity).
        rewrite __Hmset1__ in H3'.
        eassumption.
        assert(M0 ++ [G] =mul= G ::M0) as __Hmset2__  by (rewrite union_comm_app; reflexivity).
        rewrite __Hmset2__  in H4'.
        eassumption.
        eapply LPos2; eassumption.
        eapply LPos3; eassumption.
      ++ (* oplus *)
        apply H in H2;auto.
        inversion H2.
        eexists.
        simpl. simpl in H0.
        eapply sig2h_plus1 with (F:=F) (M:=M).
        solve_permutation.
        rewrite union_comm_app in H0.
        eauto.


      ++ (* oplus2 *)
        apply H in H2;auto.
        inversion H2.
        eexists.
        simpl. simpl in H0.
        eapply sig2h_plus2 with (G:=G) (M:=M).
        solve_permutation.
        rewrite union_comm_app in H0.
        eauto.
      ++ (* bang *)
        apply H in H2;auto.
        inversion H2.
        eexists.
        simpl. simpl in H0.
        eapply sig2h_bang with (F:=F);auto.
        apply H0.
      ++ (* Release *)
        apply H in H3;auto.

      ++ (* bottom *)
        apply H in H2;auto.
        inversion H2.
        simpl in H0.
        eexists.
        simpl.
        eapply sig2h_bot;eauto.
      ++ (* par *)
        apply H in H2;auto.
        inversion H2.
        simpl in H0.
        eexists.
        simpl.
        eapply sig2h_par;auto.
        assert ( M ++ F :: G :: M0 =mul=  F :: G :: M ++ M0) by solve_permutation.
        rewrite H3 in H0.
        eauto.

      ++ (* with *)
        apply H in H2;auto.
        apply H in H3;auto.
        inversion H2.
        inversion H3.
        simpl in *.
        eexists.

        
        apply sig2h_with with (F:=F) (G:=G) (M:=M ++ M0).
        solve_permutation.
        
        assert( M ++ ([F] ++ M0) =mul=  [F] ++ (M ++ M0)) by auto.
        rewrite H5 in H0.
        eauto.
        assert( M ++ ([G] ++ M0) =mul=  [G] ++ (M ++ M0)) by auto.
        rewrite H5 in H4.
        eauto.
      ++  (* ? *)
        apply H in H2;auto.
        inversion H2.
        eexists.
        simpl. simpl in H0.
        apply sig2h_quest with (F:=F) (M := M ++ M0).
        solve_permutation.
        rewrite union_comm_app in H0.
        eauto.
      ++ (* store *)
        apply H in H3;auto.
        inversion H3.
        eexists.
        simpl. simpl in H0.
        rewrite <- union_assoc_app in H0.
        simpl in H0.
        eassumption.
        apply LPos1 with (L:=[F] ++ M);eauto.
        simpl;split;auto.

      ++ (* decide *)
        apply H in H4;auto.
        inversion H4.
        eexists.
        simpl. simpl in H0.
        rewrite H3.
        simpl.
        rewrite app_nil_r.
        rewrite union_comm_app in H0.
        eassumption.
        apply  LPos1 in H3;auto.
        eapply LPos3 with (L:= [F] ++ L') ;auto.

      ++ (* decide *)
        apply H in H4;auto.
        inversion H4.
        eexists.
        simpl. simpl in H0.
        rewrite H3.
        eapply sig2h_copy with (F:=F);auto.
        rewrite H3 in H0.
        rewrite (union_comm_cons).
        eauto.
  Qed.
