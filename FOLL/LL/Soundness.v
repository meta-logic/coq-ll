(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Soundness
This file proves the soundness of the triadic (focused) system of linear logic *)

(* Add LoadPath "../" . *)
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export SequentCalculi.

Set Implicit Arguments.

Module FFSoundness (DT : Eqset_dec_pol).
  Module Export Sys :=  SqSystems DT.

  Theorem Soundness : forall (B : list Lexp) n  (M : list Lexp) A ,
      LexpPos M ->
      n |-F- B ; M ; A  ->  |-- B ; M ++ (Arrow2LL A).
  Proof with InvTac.
    intros B n M A MPos.
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
    + inversion H1;simpl;subst.
      ++ (* tensor *)
        apply sig2_tensor with (N:=M0) (M:=N) (F:=F) (G:=G) ...
        MReplace (F :: N) ( N ++ (Arrow2LL (DW F) )) .
        eapply H with (m0 := n0) ...
        MReplace (G :: M0) ( M0 ++ (Arrow2LL (DW G) )) .
        eapply H with (m0 := m) ...
      ++ (* oplus *)
        apply H in H2 ...
        simpl in *.
        eapply sig2_plus1 with (F:=F) (M:=M) ...
        rewrite union_comm in H2 ...
      ++ (* oplus2 *)
        apply H in H2 ...
        simpl in  *.
        eapply sig2_plus2 with (G:=G) (M:=M) ...
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
        eapply sig2_par ...
        MReplace  (F :: G :: M ++ M0) (M ++ F :: G :: M0) ...
      ++ (* with *)
        apply H in H2 ...
        apply H in H3 ...
        simpl in *.
        apply sig2_with with (F:=F) (G:=G) (M:=M ++ M0) ...
        MReplace ( F :: M ++ M0) ( M ++ F :: M0) ...
        MReplace (G :: M ++ M0) ( M ++ G :: M0) ...
      ++  (* ? *)
        apply H in H2 ...
        simpl in *.
        apply sig2_quest with (F:=F) (M := M ++ M0) ...
        rewrite union_comm in H2 ...
      ++ (* store *)
        apply H in H3 ...
        simpl in *.
        rewrite <- union_assoc in H3 ...
      ++ (* decide *)
        apply H in H4 ...
        simpl in *.
        rewrite app_nil_r.
        rewrite H3.
        MReplace (F :: L') ( L' ++ [F])  ...
      ++ (* decide *)
        apply H in H4 ...
        simpl in *.
        rewrite H3.
        eapply sig2_copy with (F:=F) ...
        rewrite H3 in H4 ...
        MReplace ( (F::M)++[]) (M ++ [F]) ...
      ++ (* exists *)
        apply H in H2;auto.
        simpl in *.
        rewrite union_comm in H2.
        rewrite union_comm ...
        eapply sig2_ex ...
        eauto.
      ++ (* forall *)
        simpl in *.
        eapply sig2_fx ...
        intro x.
        generalize (H2 x);intro.
        apply H in H0 ...
        simpl in *.
        MReplace (Subst FX x :: M ++ M0) ( M ++ Subst FX x :: M0) ...
  Qed.

End FFSoundness.
