(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Completeness of Focusing
Here we prove the completeness theorem for the focused system
 *)


(* Add LoadPath "../".  *)
From Stdlib Require Export Permutation.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Export Sorting.PermutSetoid.
From Stdlib Require Export Sorting.PermutEq.
From Stdlib Require Import Program.Equality.
Require Export LL.SequentCalculi. 
Require Export LL.FLLMetaTheory.


Set Implicit Arguments.

(* *** Invertibility lemmas
This module proves that the application of positive rules can be exchanged
 *)
Module InvLemmas (DT : Eqset_dec_pol).
  Module Export SR := FLLMetaTheory DT.

  (*******************************************************************)
  (* Some automation *)
  #[export] Hint Rewrite Neg2pos Ng_involutive : core .
  #[export] Hint Constructors Asynchronous : core .
  #[export] Hint Constructors IsNegativeAtom : core .
  #[export] Hint Resolve l_nil l_sin l_cos : core .
  #[export] Hint Constructors NotAsynchronous : core .
  #[export] Hint Unfold Release : core .
  #[export] Hint Constructors release : core .
  (* End Automation section *)
  (*************************************************************)



  (* =============================================== *)
  (** Invertibility of Copy *)
  (* =============================================== *)   
  Module InvCopy.

    Definition RUp (n:nat) := forall B L  F  M , 
      LexpPos M -> 
      n |-F- B ++ [F] ;M ; UP (L ++ [F])  -> |-F- B ++ [F] ; M ; UP (L ).

    Definition RDown (n:nat) := forall B  F  M  H, 
        LexpPos M -> ~ Asynchronous F ->
        n |-F- B ++ [F]; M ++ [F]  ; DW H -> |-F- B ++ [F] ; M  ; DW H.

    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 

    Lemma RDown0 : RDown 0.
    Proof.
      unfold RDown.
      intros.
      inversion H2;subst ; try(contradiction_multiset).
      destruct M;  simpl in *.
      inversion H3 ; solveF.
      eapply tri_init2 ; solveF.
      inversion H3; contradiction_multiset.
    Qed.

    Lemma RUp0 : RUp 0.
    Proof.
      unfold RUp.
      intros.
      destruct L.
      + inversion H0;subst.
        simpl.
        eapply tri_dec2 with (F:= ⊤) ; solveF.
      + inversion H0. solveF.
    Qed.
    
    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   
    
    Theorem InvCopyUP: forall  n , (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    Proof.
      intros n IH.
      unfold RUp.  intros B L1 F M1 HM1pos HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1;subst.
        ++ (* bot *)
          eapply AdequacyTri1;eauto.
        ++ (* par *)
          eapply tri_dec2 with (F:=F0 $ G) ; solveF.
          eapply tri_rel ; solveF.  eapply tri_par . eapply AdequacyTri1;eauto.
        ++ (* with *)
          eapply tri_dec2 with (F:=F0 & G) ; solveF.
          eapply tri_rel ; solveF.  eapply tri_with;eapply AdequacyTri1;eauto.
        ++ (* quest *)
          eapply tri_dec2 with (F:=? F0) ; solveF.
          eapply tri_rel ; solveF.  eapply tri_quest. eapply AdequacyTri1;eauto.
        ++ (* store *)
          assert(RInd n) by ( apply IH;auto).
          destruct H as [HUp HDown].
          inversion H5;subst.
          +++ (* Decide 1 *)
            rewrite union_comm in H0.
            simpl_union_context;subst.
            rewrite <- HeqM in H1.
            eapply tri_dec2 with (F:= F0); solveF.
            eapply AdequacyTri1;eauto.
            
            rewrite H0 in H1. rewrite H2.
            
            assert( |-F- B ++ [F]; L1; DW F0).
            apply HDown ; solveF.
            rewrite H2 in HM1pos. inversion HM1pos; auto.
            
            assert (Hm : F :: L1 =mul= L1 ++ [F]) by  solve_permutation.
            rewrite <- Hm.
            rewrite Nat.sub_0_r;auto.
            eapply tri_dec1 with (F:= F0) ; solveF.
          +++ (* Decide 2 *)
            assert( |-F- B ++ [F]; M1; DW F0).
            apply HDown ; solveF.
            rewrite Nat.sub_0_r;auto.
            eapply tri_dec2 with (F:=F0) ; solveF.
        ++ (* forall *)
          eapply tri_dec2 with (F:=F{ FX}) ; solveF.
          eapply tri_rel ; solveF.
          eapply tri_fx.
          intro.
          specialize (H3 x).
          eapply AdequacyTri1;eauto.
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RInd n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ; solveF.
        
        ++ (* & *)
          assert(H: RInd n0) by ( apply IH;auto);
            destruct H as [HUp  HDown]; clear HDown.
          assert(H: RInd m) by ( apply IH;auto);
            destruct H as [HUp'  HDown']; clear HDown'.
          unfold RUp in HUp.
          eapply HUp with (L:= F0::L1) in H4 ; solveF.
        ++ (* ? *)
          unfold RUp in HUp.
          assert(Hm: (B ++ [F]) ++ [F0] =mul=  (B ++ [F0]) ++ [F]) by solve_permutation.
          rewrite Hm in H3.
          eapply HUp with (B:= B ++ [F0]) in H3 ; solveF.
          apply tri_quest.
          rewrite Hm. solveF.
        ++ (* store *)
          apply HUp in H5 ; solveF.
        ++ (* forall *)
          apply tri_fx;intro.
          generalize (H3 x);intro.
          unfold RUp in HUp.
          eapply HUp with (L:= Subst FX x :: L1) in H ; solveF.
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    
    Theorem InvCopyDW: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof.
      intros n IH.
      unfold RDown.  intros B F M H  HM1pos HPosF  HD1.
      caseLexp H;subst;solveF; inversion HD1;subst; try contradiction_multiset ; solveF.
      ++ (* atom 1 *)
        eapply AppSingleton in H;subst.
        simpl in HD1; inversion HD1.
        eapply tri_init2 ; solveF.
      ++ (* atom 2 *)
        apply UpExtension in H5 ; solveF.
        destruct H5.
        destruct H.
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown]. clear HDown.
        unfold RUp in HUp.
        apply HUp with (L:= [A3 ⁺]) in H2 ; solveF.
      ++ (* perp1 *)
        eapply AppSingleton in H;subst.
        simpl in HD1; inversion HD1.
        eapply tri_init2 ; solveF.
      ++ (* perp2 *)
        apply UpExtension in H5 ; solveF.
        destruct H5.
        destruct H. 
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp HDown]. clear HDown.
        unfold RUp in HUp.
        apply HUp with (L:= [A3 ⁻]) in H2 ; solveF.
      ++ (* bbot *)
        apply UpExtension in H4 ; solveF.
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown]; solveF.
      ++ (* tensor *)
        symmetry in H2.
        assert(HC: M ++ [F] =mul= [F] ++ M) by solve_permutation; rewrite HC in H2;clear HC.
        (* 2 choices: F is M0 or in N0 *)
        simpl_union_context.
        +++ rewrite union_comm in HL1.
            rewrite HL1 in H7. rewrite H.
            assert(HRI: RInd (S m)) by( apply IH; auto using le_n_S).
            destruct HRI as [HUp HDown] ; solveF.
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H7 ; solveF.
            apply AdequacyTri1 in H3.
            eapply tri_tensor with (N:=N) (M:=L1) ; solveF.
        +++ rewrite union_comm in HL2.
            rewrite HL2 in H3. rewrite H.
            assert(HRI: RInd (S n0)) by( apply IH; auto using le_n_S).
            destruct HRI as [HUp HDown] ; solveF.
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H3 ; solveF.
            apply AdequacyTri1 in H7.
            eapply tri_tensor with (M:=M0) (N:=L2) ; solveF.
      ++ (* Par *)
        apply UpExtension in H6 ; solveF.
        destruct H6 as [m [H6 H6']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* oplus1 *)
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply tri_plus1. solveF.
      ++ (* oplus2 *)
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply tri_plus2. solveF.
      ++ (* with *)
        apply UpExtension in H6 ; solveF.
        destruct H6 as [m [H6 H6']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* quest *)
        apply UpExtension in H5 ; solveF.
        destruct H5 as [m [H5 H5']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* exists *)
        assert(HRI: RInd (S n0)) by (apply IH;auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H3 ; solveF.
        apply tri_ex with (t:=t). solveF.
      ++ (* forall *)
        apply UpExtension in H4 ; solveF.
        destruct H4 as [m [H4 H4']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
    Qed.
    

    Theorem InvAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split.
        apply InvCopyUP. assumption.
        simpl.  rewrite Nat.sub_0_r.
        apply InvCopyDW. assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem InvCopy : forall B L F  M,   |-F- B ++ [F]  ;M ; UP (F :: L) -> LexpPos M  ->|-F- B ++ [F] ; M  ; UP L .
    Proof.
      intros.
      apply EquivUpArrow2 with (L' := L ++ [F]) in H ;auto.
      assert(HRn:  forall n, RUp n) by (apply InvAux).
      apply AdequacyTri2 in H.
      destruct H.
      generalize (HRn x);intros;auto.
    Qed.

  End InvCopy.

  (* =============================================== *)
  (** Invertibility of Exists *)
  (* =============================================== *)   
  Module InvExists.
    Definition RUp (n:nat) := forall B L M FX t, 
      LexpPos M -> 
      n |-F- B ;M ; UP (L ++ [Subst FX t])  -> |-F- B ; M ++ [Ex FX] ; UP L.

    Definition RDown (n:nat) := forall B M H FX t, 
        LexpPos M -> PosOrNegAtom (Subst FX t) ->
        n |-F- B ; M ++ [Subst FX t]  ; DW H -> |-F- B ; M ++ [Ex FX]  ; DW H.
    
    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 
    
    Lemma RDown0 : RDown 0.
    Proof.
      unfold RDown.
      intros.
      inversionF H2;subst;try(contradiction_multiset).
      apply AppSingleton in H3. subst;simpl in *.
      inversion H2. subst.
      rewrite <- H3 in H1.
      apply NegPosAtom in H6.
      assert(False) by (eapply NegPosAtomContradiction;eauto).
      contradiction.
    Qed.
    
    Lemma RUp0 : RUp 0.
    Proof.
      unfold RUp.
      intros.
      destruct L.
      + inversion H0;subst.
        eapply tri_dec1 with (F:= E{ FX}) ; solveF.
        apply tri_ex with (t:=t).
        rewrite <- H1.
        apply tri_rel ; solveF.
      + inversion H0. solveF.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   
    Theorem InvExUP: forall  n , (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    Proof.
      intros n IH.
      unfold RUp.  intros B L1  M1 FX t HM1pos HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1;subst ; solveF.
        ++ (* bot *)
          eapply tri_dec1 with (F:=E{ FX});solveF; eapply tri_ex with (t:=t);solveF;
            rewrite <- H0; eapply tri_rel;solveF; 
              NegPhase; rewrite app_nil_r; eapply AdequacyTri1;eauto.
        ++ (* par *)
          eapply tri_dec1 with (F:=E{ FX}) ; solveF.
          eapply tri_ex with (t:=t) ; solveF.
          rewrite <- H0.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.
        ++ (* with *)
          eapply tri_dec1 with (F:=E{ FX}) ; solveF.
          eapply tri_ex with (t:=t) ; solveF.
          rewrite <- H0.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.
        ++ (* quest *)
          eapply tri_dec1 with (F:=E{ FX}) ; solveF.
          eapply tri_ex with (t:=t) ; solveF.
          rewrite <- H0.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.
        ++ (* store *)
          assert(RInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ; solveF.
          +++ (* Decide 1 *)
            rewrite union_comm in H0.
            simpl_union_context;subst.
            (* taking Subst FX t *)
            rewrite <- HeqM in H1.
            eapply tri_dec1 with (F:= E{ FX}) ; solveF.
            eapply tri_ex with (t:=t).
            rewrite app_nil_r;
              eapply AdequacyTri1;eauto.
            (* taking any other formula *)
            rewrite H0 in H1. rewrite H2.
            assert(HS : Subst FX t :: L1 =mul= L1 ++ [Subst FX t]) by solve_permutation ;rewrite HS in H1; clear HS.
            (* Subst must be: a negative atom, a positive atom or a positive formula *)
            apply NotAsynchronousPosAtoms in H4 as [H4 | [H4 | H4]].
            (* case PosFormula*)
            apply PosFormulaPosOrNegAtom in H4.
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H1 ; solveF.
            eapply tri_dec1 with (F:=F) ; solveF.
            
            (* case positive atom *)
            eapply tri_dec1 with (F:= E{ FX}) ; solveF.
            eapply tri_ex with (t:=t).
            eapply tri_rel ; solveF.
            eapply tri_store ; solveF. apply IsPositiveAtomNotAssync;auto.
            eapply tri_dec1 with (F:= F) ; solveF.
            eapply AdequacyTri1;rewrite app_nil_r;eauto.
            
            (* case negative atom *)
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H1 ; solveF.
            eapply tri_dec1 with (F:=F) ; solveF.
            apply IsNegativePosOrNegAtom;auto.
          +++  (* Decide 2 *)
            (* Subst must be: a negative atom, a positive atom or a positive formula *)
            apply NotAsynchronousPosAtoms in H4 as [H4 | [H4 | H4]].
            (* case PosFormula*)
            apply PosFormulaPosOrNegAtom in H4.
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H1 ; solveF.
            eapply tri_dec2 with (F:=F) ; solveF.
            
            (* case positive atom *)
            eapply tri_dec1 with (F:= E{ FX}) ; solveF.
            eapply tri_ex with (t:=t).
            eapply tri_rel ; solveF.
            rewrite app_nil_r.
            eapply tri_store ; solveF. apply IsPositiveAtomNotAssync;auto.
            eapply tri_dec2 with (F:= F) ; solveF.
            eapply AdequacyTri1;eauto.

            (* case negative atom *)
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H1 ; solveF.
            eapply tri_dec2 with (F:=F) ; solveF.
            apply IsNegativePosOrNegAtom;auto.
        ++ (* forall *)
          eapply tri_dec1 with (F:=E{ FX}) ; solveF.
          eapply tri_ex with (t:=t) ; solveF.
          rewrite <- H0.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.

      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RInd n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ; solveF.
        ++ (* bot *)
          NegPhase.
          apply HUp in H3 ; solveF.
        ++ (* par *)
          NegPhase.
          unfold RUp in HUp.
          apply HUp with (L:=  F :: G :: L1)in H3 ; solveF.
        ++ (* & *)
          assert(H: RInd n0) by ( apply IH;auto);
            destruct H as [HUp  HDown]; clear HDown.
          assert(H: RInd m) by ( apply IH;auto);
            destruct H as [HUp'  HDown']; clear HDown'.
          unfold RUp in HUp.
          eapply HUp with (L:= F::L1) in H4 ; solveF.
          unfold RUp in HUp'.
          eapply HUp' with (L:= G::L1) in H5 ; solveF.
          
        ++ (* ? *)
          apply HUp in H3 ; solveF.
          
        ++ (* store *)
          apply HUp in H5 ; solveF.
          apply tri_store ; solveF.
          assert(Hs : (M1 ++ [l]) ++ [E{ FX}] =mul= (M1 ++ [E{ FX}]) ++ [l]) by solve_permutation; rewrite Hs in H5.
          assumption.
        ++ (* forall *) 
          apply tri_fx;intro.
          generalize (H3 x);intro.
          unfold RUp in HUp.
          eapply HUp with (L:= Subst FX0 x :: L1) in H ; solveF.
    Qed.

    
    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvExDW: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof. (*auto using LexpPosOrNegAtomConc.*)
      intros n IH.
      unfold RDown.  intros B M  H  FX t HPosF HM1pos  HD1.
      caseLexp H;subst;solveF; inversion HD1;subst;try(contradiction_multiset) ; solveF.
      ++ (* atom 1 *)
        (* HD1  + HM1Pos is inconsistent *)
        apply  NegPosAtom in H4.
        apply AppSingleton in H. subst;simpl in *.
        inversionF HD1.
        rewrite <- H in HM1pos.
        assert(False) by (eapply NegPosAtomContradiction;eauto).
        contradiction.
      ++ (* atom 2 *)
        apply UpExtension in H5; auto using LexpPosOrNegAtomConc.
        destruct H5.
        destruct H.
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp HDown]. clear HDown.
        unfold RUp in HUp.
        apply HUp  with (L:= [A3 ⁺]) in H2 ; solveF.
      ++ (* perp1 *)
        (* same inconsistency *)
        apply  NegPosAtom in H4.
        apply AppSingleton in H. subst;simpl in *.
        inversionF HD1.
        rewrite <- H in HM1pos.
        assert(False) by (eapply NegPosAtomContradiction;eauto).
        contradiction.
      ++ (* perp2 *)
        apply UpExtension in H5; auto using LexpPosOrNegAtomConc.
        destruct H5.
        destruct H. 
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp HDown]. clear HDown.
        apply HUp in H2 ; solveF.
      ++ (* bbot *) 
         apply UpExtension in H4; auto using LexpPosOrNegAtomConc.
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown].
        unfold RUp in HUp.
        apply HUp with (L:= [⊥]) in H4' ; solveF.
      ++ (* tensor *)
        symmetry in H2.
        assert(HC: M ++ [Subst FX t] =mul= [Subst FX t] ++ M) by solve_permutation; rewrite HC in H2;clear HC. 
        (* 2 choices: Subst FX t is M or in N *)
        simpl_union_context.
        +++ rewrite union_comm in HL1.
            rewrite HL1 in H7. rewrite H.
            assert(HRI: RInd (S m)) by( apply IH; auto using le_n_S).
            destruct HRI as [HUp HDown] ; solveF.
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H7 ; solveF.
            apply AdequacyTri1 in H3.
            eapply tri_tensor with (N:=N) (M:=L1 ++ [E{ FX}]) ; solveF.
        +++ rewrite union_comm in HL2.
            rewrite HL2 in H3. rewrite H.
            assert(HRI: RInd (S n0)) by( apply IH; auto using le_n_S).
            destruct HRI as [HUp HDown] ; solveF.
            rewrite Nat.sub_0_r in HDown.
            apply HDown in H3 ; solveF.
            apply AdequacyTri1 in H7.
            eapply tri_tensor with (M:=M0) (N:=L2 ++ [E{ FX}]) ; solveF.
      ++ (* Par *)
        apply UpExtension in H6; auto using LexpPosOrNegAtomConc.
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
        unfold RUp in HUp.
        apply HUp with (L:= [F $ G]) in H6' ; solveF.
      ++ (* oplus1 *)
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H5 ; solveF.
      ++ (* oplus2 *)
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H5 ; solveF.
      ++ (* with *)
        apply UpExtension in H6; auto using LexpPosOrNegAtomConc.
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
        unfold RUp in HUp.
        apply HUp with (L:= [F & G]) in H6' ; solveF.
      ++ (* quest *)
        apply UpExtension in H5; auto using LexpPosOrNegAtomConc.
        destruct H5 as [m H5]. destruct H5 as [H5 H5'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
        unfold RUp in HUp.
        apply HUp with (L:= [? F]) in H5' ; solveF.
      ++ (* exists *)
        assert(HRI: RInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H3 ; solveF.
        apply tri_ex with (t:=t0) ; solveF.
      ++ (* forall *)
         apply UpExtension in H4; auto using LexpPosOrNegAtomConc.
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
        unfold RUp in HUp.
        apply HUp with (L:= [F{ FX0}]) in H4' ; solveF.
    Qed.
    

    Theorem InvExAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split.
        apply InvExUP. assumption.
        simpl.  rewrite Nat.sub_0_r.
        apply InvExDW. assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   

    Theorem InvEx : forall B L FX t  M,   |-F- B  ;M ; UP (Subst FX t :: L) -> LexpPos M  ->|-F- B ; M ++ [E{ FX}]  ; UP L .
    Proof.
      intros.
      apply EquivUpArrow2 with (L' := L ++ [Subst FX t]) in H ;eauto.
      assert(HRn:  forall n, RUp n) by (apply InvExAux).
      apply AdequacyTri2 in H.
      destruct H.
      generalize (HRn x);intros.
      apply H1 in H;auto.
    Qed.

  End InvExists.

  (* =============================================== *)
  (** Invertibility of OPlus *)
  (* =============================================== *)   
  Module InvOPlus.
    
    Definition RUp (n:nat) := forall B L M F G, 
      LexpPos M -> 
      n |-F- B ;M ; UP (L ++ [F])  -> |-F- B ; M ++ [F ⊕ G] ; UP L.

    Definition RDown (n:nat) := forall B M H F G, 
        LexpPos M -> PosOrNegAtom F ->
        n |-F- B ; M ++ [F]  ; DW H -> |-F- B ; M ++ [F ⊕ G]  ; DW H.
    
    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 
    
    Lemma RDown0 : RDown 0.
    Proof.
      unfold RDown.
      intros.
      inversionF H2;subst;try(contradiction_multiset).
      apply AppSingleton in H3;subst;simpl in *.
      inversionF H2.
      apply NegPosAtom in H6.
      assert(False) by (eapply NegPosAtomContradiction;eauto).
      contradiction.
    Qed.
    
    Lemma RUp0 : RUp 0.
    Proof.
      unfold RUp.
      intros.
      destruct L.
      + inversion H0;subst.
        eapply tri_dec1 with (F:= ⊤ ⊕ G) ; solveF.
      + inversion H0. solveF.
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   
    Theorem InvPlusUP: forall  n , (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    Proof.
      intros n IH.
      unfold RUp.  intros B L1  M1 F  G HM1pos HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1;subst ; solveF.
        ++ (* bot *)
          eapply tri_dec1 with (F:=⊥ ⊕ G) ; solveF.
          eapply tri_plus1.
          eapply tri_rel ; solveF.
          rewrite app_nil_r; eapply AdequacyTri1;eauto.
        ++ (* par *)
          eapply tri_dec1 with (F:=(F0 $ G0) ⊕ G) ; solveF.
          eapply tri_plus1.
          eapply tri_rel ; solveF.
          rewrite app_nil_r;
            eapply AdequacyTri1;eauto.
        ++ (* with *)
          eapply tri_dec1 with (F:=(F0 & G0) ⊕ G) ; solveF.
          eapply tri_plus1.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.
        ++ (* quest *)
          eapply tri_dec1 with (F:=(? F0) ⊕ G) ; solveF.
          eapply tri_plus1.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.
        ++ (* store *)
          assert(RInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ; solveF.
          +++ (* Decide 1 *)
            rewrite union_comm in H0.
            simpl_union_context;subst.
            (* taking F0 *)
            rewrite <- HeqM in H1.
            eapply tri_dec1 with (F:= F0 ⊕ G) ; solveF.
            eapply tri_plus1.
            rewrite app_nil_r;
              eapply AdequacyTri1;eauto.
            (* taking any other formula *)
            rewrite H0 in H1. rewrite H2.
            assert(HS : F :: L1 =mul= L1 ++ [F]) by solve_permutation ;rewrite HS in H1; clear HS. 
            (* Subst must be: a negative atom, a positive atom or a positive formula *)
            apply NotAsynchronousPosAtoms in H4.
            destruct H4 as [H4 | [H4 | H4]].
            (* case PosFormula*)
            apply PosFormulaPosOrNegAtom in H4.
            eapply tri_dec1 with (F:=F0) ; solveF.
            rewrite Nat.sub_0_r in HDown.
            eapply HDown in H1 ; solveF.

            eauto.

            (* case positive atom *)
            eapply tri_dec1 with (F:= F ⊕ G) ; solveF. 
            eapply tri_plus1.
            eapply tri_rel ; solveF.
            eapply tri_store ; solveF. apply IsPositiveAtomNotAssync;auto.
            eapply tri_dec1 with (F:= F0) ; solveF.
            eapply AdequacyTri1;rewrite app_nil_r;eauto.

            (* case negative atom *)
            rewrite Nat.sub_0_r in HDown.
            eapply HDown in H1 ; solveF.
            eapply tri_dec1 with (F:=F0) ; solveF.
            eassumption.
            apply IsNegativePosOrNegAtom;auto.
          +++  (* Decide 2 *)
            (* Subst must be: a negative atom, a positive atom or a positive formula *)
            apply NotAsynchronousPosAtoms in H4.
            destruct H4 as [H4 | [H4 | H4]].
            (* case PosFormula*)
            apply PosFormulaPosOrNegAtom in H4.
            rewrite Nat.sub_0_r in HDown.
            eapply HDown in H1 ; solveF.
            eapply tri_dec2 with (F:=F0) ; solveF.
            eassumption.

            (* case positive atom *)
            eapply tri_dec1 with (F:= F ⊕ G) ; solveF. 
            eapply tri_plus1.
            eapply tri_rel ; solveF.
            rewrite app_nil_r.
            eapply tri_store ; solveF. apply IsPositiveAtomNotAssync;auto.
            eapply tri_dec2 with (F:= F0) ; solveF.
            eapply AdequacyTri1;eauto.

            (* case negative atom *)
            rewrite Nat.sub_0_r in HDown.
            eapply HDown in H1 ; solveF.
            eapply tri_dec2 with (F:=F0) ; solveF.
            eassumption.
            apply IsNegativePosOrNegAtom;auto.
        ++ (* forall *)
          eapply tri_dec1 with (F:=F{FX} ⊕ G) ; solveF.
          eapply tri_plus1.
          eapply tri_rel ; solveF.
          NegPhase;
            rewrite app_nil_r;
            eapply AdequacyTri1;eauto.

      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RInd n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ; solveF.
        ++ (* & *)
          assert(H: RInd n0) by ( apply IH;auto);
            destruct H as [HUp  HDown]; clear HDown.
          assert(H: RInd m) by ( apply IH;auto);
            destruct H as [HUp'  HDown']; clear HDown'.
          unfold RUp in HUp.
          eapply HUp with (L:= F0::L1) in H4 ; solveF.
          unfold RUp in HUp'.
          eapply HUp' with (L:= G0::L1) in H5 ; solveF.
          NegPhase;eauto.

        ++ (* store *)
          unfold RUp in HUp.
          apply HUp with (G:=G) in H5 ; solveF.
          apply tri_store ; solveF.
          assert(Hs : (M1 ++ [l]) ++ [F ⊕ G] =mul= (M1 ++ [F ⊕ G]) ++ [l]) by solve_permutation; rewrite Hs in H5.
          assumption.
        ++ (* forall *) 
          apply tri_fx;intro.
          generalize (H3 x);intro.
          unfold RUp in HUp.
          eapply HUp with (L:= Subst FX x :: L1) in H ; solveF.
          eassumption.
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvPlusDW: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof.
      intros n IH.
      unfold RDown.  intros B M  H  F G HPosF HM1pos  HD1.
      caseLexp H;subst;solveF; inversionF HD1;subst;try(contradiction_multiset) ; solveF.
      ++ (* atom 1 *)
        (* HD1  + HM1Pos is inconsistent *)
        apply  NegPosAtom in H4.
        apply AppSingleton in H;subst;simpl in *.
        inversionF HD1.
        assert(False) by (eapply NegPosAtomContradiction;eauto).
        contradiction.
      ++ (* atom 2 *)
        apply UpExtension in H5;auto using LexpPosOrNegAtomConc.
        destruct H5.
        destruct H. 
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown]. clear HDown.
        eapply HUp in H2 ; solveF.
        eapply tri_rel ; solveF.
        eassumption.
      ++ (* perp1 *)
        (* same inconsistency *)
        apply NegPosAtom in H4.
        apply AppSingleton in H;subst;simpl in *.
        inversionF HD1.
        assert(False) by (eapply NegPosAtomContradiction;eauto).
        contradiction.
      ++ (* perp2 *)
        apply UpExtension in H5; auto using LexpPosOrNegAtomConc.
        destruct H5.
        destruct H.
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp _].
        eapply HUp in H2 ; solveF.
        eapply tri_rel ; solveF.
        eassumption.
      ++ (* bbot *) 
         apply UpExtension in H4;auto using LexpPosOrNegAtomConc.
                    destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* tensor *)
        symmetry in H2.
        assert(HC: M ++ [F] =mul= [F] ++ M) by solve_permutation; rewrite HC in H2;clear HC. 
        (* 2 choices: F is M or in N *)
        simpl_union_context.
        +++ rewrite union_comm in HL1.
            rewrite HL1 in H7. rewrite H.
            assert(HRI: RInd (S m)) by( apply IH; auto using le_n_S). 
            destruct HRI as [HUp HDown] ; solveF.
            eapply tri_tensor with (N:=N) (M:=L1 ++ [F ⊕ G]) ; solveF.
            eauto.
            apply AdequacyTri1 in H3 ; solveF.
            rewrite Nat.sub_0_r in HDown.
            eapply HDown in H7 ; solveF.
            eauto.
            
            
        +++ rewrite union_comm in HL2.
            rewrite HL2 in H3. rewrite H.
            assert(HRI: RInd (S n0)) by( apply IH; auto using le_n_S).
            destruct HRI as [HUp HDown] ; solveF.
            rewrite Nat.sub_0_r in HDown.
            eapply HDown in H3 ; solveF.
            apply AdequacyTri1 in H7.
            eapply tri_tensor with (M:=M0) (N:=L2 ++ [F ⊕ G]) ; solveF.
            eassumption.
      ++ (* Par *)
        apply UpExtension in H6;auto using LexpPosOrNegAtomConc.
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* oplus1 *)
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown ; solveF.
      ++ (* oplus2 *)
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown ; solveF.
      ++ (* with *)
        apply UpExtension in H6;auto using LexpPosOrNegAtomConc.
        destruct H6 as [m [H6 H6']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* quest *)
         apply UpExtension in H5;auto using LexpPosOrNegAtomConc.
        destruct H5 as [m [H5 H5']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
      ++ (* exists *)
        assert(HRI: RInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply tri_ex with (t:=t) ; solveF. (* HDown in H3 ends *)

      ++ (* forall *)
        apply UpExtension in H4;auto using LexpPosOrNegAtomConc.
        destruct H4 as [m [H4 H4']].
        assert(HRI: RInd m)  by (apply IH ;auto).
        destruct HRI as [HUp HDown] ; solveF.
    Qed.
    

    Theorem InvPlusAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split.
        apply InvPlusUP. assumption.
        simpl.  rewrite Nat.sub_0_r.
        apply InvPlusDW. assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem InvPlus : forall B L F G  M,   |-F- B  ;M ; UP (F :: L) -> LexpPos M  ->|-F- B ; M ++ [F ⊕ G]  ; UP L .
    Proof.
      intros.
      apply EquivUpArrow2 with (L' := L ++ [F]) in H ;eauto.
      assert(HRn:  forall n, RUp n) by (apply InvPlusAux).
      apply AdequacyTri2 in H.
      destruct H.
      generalize (HRn x);intros.
      eapply H1 in H;eauto.
    Qed.


    Lemma OPlusComm : forall B M F G X n, n |-F- B ; M ++ [F ⊕ G] ; X -> n |-F- B ; M ++ [G ⊕ F] ; X.
    Proof.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + inversion H;solveF;subst;try(contradiction_multiset) ; solveF.
        apply AppSingleton in H0;subst;simpl in *.
        inversionF H ; solveF.
        inversion H1;subst ; solveF.
      + inversion H0;subst;try(contradiction_multiset) ; solveF.
        ++ (* tensor *)
          symmetry in H2.
          assert(HS: M ++ [F ⊕ G] =mul=  [F ⊕ G] ++ M) by solve_permutation; rewrite HS in H2;clear HS.
          (* F+ G can be either in M0 or in N *)
          simpl_union_context.
          (* in M0 *)
          rewrite H1. rewrite HL1 in H4. 
          apply trih_tensor with (N:= N) (M:=  [G ⊕ F] ++ L1) ; solveF.
          assert(HS: G ⊕ F :: L1 =mul=  L1  ++ [G ⊕ F]) by eauto;rewrite HS;clear HS.
          apply H;eauto.
          assert(HS:  L1 ++ [F ⊕ G] =mul=   [F ⊕ G] ++ L1) by eauto;rewrite HS.
          assumption.
          (* in N *)
          rewrite H1. rewrite HL2 in H3.
          apply trih_tensor with (N:= [G ⊕ F] ++ L2) (M:=  M0) ; solveF.
          assert(HS: G ⊕ F :: L2 =mul=  L2  ++ [G ⊕ F]) by eauto;rewrite HS;clear HS.
          apply H;eauto.
          assert(HS:  L2 ++ [F ⊕ G] =mul=   [F ⊕ G] ++ L2) by eauto;rewrite HS.
          assumption.
        ++ (* store *)
          apply trih_store ; solveF.
          assert(HS:  (M ++ [G ⊕ F]) ++ [F0] =mul=  (M ++ [F0]) ++ [G ⊕ F]) by solve_permutation.
          rewrite HS.
          apply H;auto.
          assert(HS':  (M ++ [F ⊕ G]) ++ [F0] =mul=  (M ++ [F0]) ++ [F ⊕ G]) by solve_permutation.
          rewrite <- HS'.
          auto.
        ++ (* decide 1 *)
          rewrite union_comm in H3.
          simpl_union_context;subst.
          inversion H4 ; solveF.
          eapply trih_dec1 with (F:= G ⊕ F) ; solveF. apply trih_plus2. rewrite HeqM. rewrite app_nil_r. auto.
          eapply trih_dec1 with (F:= G ⊕ F) ; solveF. apply trih_plus1. rewrite HeqM. rewrite app_nil_r. auto.
          rewrite H3.
          eapply trih_dec1 with (F:= F0) ; solveF.
          apply H;auto. rewrite H1 in H4.
          assert(HS:  F ⊕ G :: L1 =mul=  L1 ++ [F ⊕ G ]) by eauto; rewrite HS in H4.
          assumption.
        ++  (* decide 2 *)
          eapply trih_dec2 with (F:=F0) ; solveF.
        ++ (* exists *)
          eapply trih_ex with (t:=t) ; solveF.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM (FLIPPING F and G    *)
    (* =============================================== *)   
    Theorem InvPlusComm: forall B L F G  M,   |-F- B  ;M ; UP (G :: L) -> LexpPos M  ->|-F- B ; M ++ [F ⊕ G]  ; UP L .
    Proof.
      intros.
      apply InvPlus with (G:=F)in H;auto.
      apply AdequacyTri2 in H.
      destruct H.
      apply OPlusComm in H.
      apply AdequacyTri1 with (n:=x);auto.
    Qed.
  End InvOPlus.

  (* =============================================== *)
  (** Invertibility of Tensor *)
  (* =============================================== *)
  Module InvTensor.

    Definition RUp (nm:nat) := forall B L M L' M' F G n m,
      nm = n + m -> LexpPos M -> LexpPos M' ->  n |-F- B ;M ; UP (L ++ [F])  -> m |-F- B ;M' ; UP (L' ++ [G])  -> |-F- B ; M ++ M' ++  [F ** G] ; UP (L ++ L').

    Definition RDown (nm:nat) := forall B M M' H F G n m, 
        nm = n + m -> LexpPos M -> LexpPos M' -> PosOrNegAtom F ->
        n |-F- B ; M ++ [F]  ; DW H -> m |-F- B ; M' ; UP [G] -> |-F- B ; M ++ M' ++  [F ** G]  ; DW H.

    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 

    Lemma RDown0 : RDown 0.
    Proof.
      unfold RDown.
      intros.
      symmetry in H0. apply Nat.eq_add_0 in H0.
      destruct H0;subst.
      inversion H4;try(contradiction_multiset).
      apply AppSingleton in H0;subst;simpl in *.
      inversion H4;subst.
      apply NegPosAtom in H8. subst.
      assert(False) by (eapply NegPosAtomContradiction;eauto).
      contradiction.
    Qed.

    Lemma RUp0 : RUp 0.
    Proof.
      unfold RUp.
      intros.
      symmetry in H. apply Nat.eq_add_0 in H.
      destruct H;subst.
      inversion H2;subst.
      destruct L;destruct L';simpl in *.
      + inversion H;subst.
        inversion H3;subst.
        eapply tri_dec1 with (F:= ⊤ ** ⊤) ; solveF.
        eapply tri_tensor with (N:=M) (M:=M') ; solveF.
      + inversion H3;subst. solveF.
      + inversion H. solveF.
      + inversion H. solveF.
    Qed.

    (* =============================================== *)
    (* F ** G COMMUTES *)
    (* =============================================== *)
    Lemma TensorComm : forall B M F G X n, n |-F- B ; M ++ [F ** G] ; X -> n |-F- B ; M ++ [G ** F] ; X.
    Proof.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + inversion H;try(contradiction_multiset) ; solveF.
        apply AppSingleton in H0;subst;simpl in *.
        inversion H;subst. inversion H1;subst ; solveF.
      + inversion H0;try(contradiction_multiset);subst ; solveF.
        ++ (* tensor *)
          symmetry in H2.
          assert(HS: M ++ [F ** G] =mul=  [F ** G] ++ M) by solve_permutation; rewrite HS in H2;clear HS.
          (* F ** G can be either in M0 or in N *)
          simpl_union_context.
          (* in M0 *)
          rewrite H1. rewrite HL1 in H4.
          apply trih_tensor with (N:= N) (M:=  [G ** F] ++ L1) ; solveF.
          assert(HS: G ** F :: L1 =mul=  L1  ++ [G ** F]) by eauto;rewrite HS;clear HS.
          apply H;eauto.
          assert(HS:  L1 ++ [F ** G] =mul=   [F ** G] ++ L1) by eauto;rewrite HS.
          assumption.
          (* in N *)
          rewrite H1. rewrite HL2 in H3.
          apply trih_tensor with (N:= [G ** F] ++ L2) (M:=  M0) ; solveF.
          assert(HS: G ** F :: L2 =mul=  L2  ++ [G ** F]) by eauto;rewrite HS;clear HS.
          apply H;eauto.
          assert(HS:  L2 ++ [F ** G] =mul=   [F ** G] ++ L2) by eauto;rewrite HS.
          assumption.
        ++ (* store *)
          apply trih_store ; solveF.
          assert(HS:  (M ++ [G ** F]) ++ [F0] =mul=  (M ++ [F0]) ++ [G ** F]) by solve_permutation.
          rewrite HS.
          apply H;auto.
          assert(HS':  (M ++ [F ** G]) ++ [F0] =mul=  (M ++ [F0]) ++ [F ** G]) by solve_permutation.
          rewrite <- HS'.
          auto.
        ++ (* decide 1 *)
          rewrite union_comm in H3.
          simpl_union_context;subst.
          inversion H4 ; solveF.
          rewrite HeqM. rewrite H3.
          eapply trih_dec1 with (F:= G ** F) ; solveF.
          assert (Hmax: max n0 m = max m n0) by apply Nat.max_comm; rewrite Hmax; clear Hmax.
          apply trih_tensor with (N:=M0) (M:=N) ; solveF.

          rewrite H3.
          eapply trih_dec1 with (F:= F0) ; solveF.
          apply H;auto. rewrite H1 in H4.
          MReplaceIn ( F ** G :: L1) (L1 ++ [F **G]) H4.
          auto.

        ++  (* decide 2 *)
          eapply trih_dec2 with (F:=F0) ; solveF.
        ++ (* exists *)
          eapply trih_ex with (t:=t) ; solveF.
    Qed.


    Lemma TensorComm' : forall B M F G X , |-F- B ; M ++ [F ** G] ; X -> |-F- B ; M ++ [G ** F] ; X.
    Proof.
      intros.
      apply AdequacyTri2 in H.
      destruct H.
      apply TensorComm in H.
      eapply AdequacyTri1;eauto.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Cases when one of the lists is not empty *)
    (* =============================================== *)
    Lemma InvTensorConsNil (nm : nat) (IH : forall m : nat, m <= nm -> RInd m) (B L1 M1 : list Lexp)
          (l : Lexp) (L2  M2 : list Lexp) (F  G : Lexp) (n'  m' : nat) : S nm = n' + m' -> LexpPos M1 -> LexpPos M2 -> n' |-F- B; M1; UP (L1 ++ [F]) -> m' |-F- B; M2; UP (l :: L2 ++ [G]) -> |-F- B; M1 ++ M2 ++ [F ** G]; UP (L1 ++ l :: L2).
    Proof.
      intros HNM  HM1pos HM2pos HD1 HD2.
      apply EquivUpArrow2 with (L':= L1 ++ l :: L2) (L := l:: L2 ++ L1);eauto.
      inversion HD2;subst;NegPhase.
      (* bot *)
      apply EquivUpArrow2 with (L:= L1 ++ L2) (L' := L2 ++ L1);eauto.
      assert(HUp : RUp(n' + n)) by (apply IH;lia).
      eapply HUp ; solveF.
      (* par *)
      apply EquivUpArrow2 with (L:= L1 ++ F0 :: G0 :: L2) (L' := F0 :: G0 :: L2 ++ L1);eauto.
      assert(HUp : RUp(n' + n)) by (apply IH;lia).
      eapply HUp ; solveF.
      (* with *)
      rewrite Nat.add_succ_r in HNM;inversion HNM;subst.
      assert(HUp1 : RUp(n' + n)). apply IH. apply Nat.add_le_mono;auto.
      apply EquivUpArrow2 with (L:= L1 ++ F0 :: L2) (L' := F0 :: L2 ++ L1);eauto.
      rewrite Nat.add_succ_r in HNM;inversion HNM;subst.
      assert(HUp2 : RUp(n' + m)). apply IH. apply Nat.add_le_mono;auto.
      apply EquivUpArrow2 with (L:= L1 ++ G0 :: L2) (L' := G0 :: L2 ++ L1);eauto .
      (* quest *)
      assert(HUp : RUp(n' + n)) by (apply IH;lia).
      apply EquivUpArrow2 with (L:= L1 ++ L2) (L' := L2 ++ L1);eauto.
      eapply HUp ; solveF.
      eapply TriWeakening ; solveF.
      (*  store *)
      apply tri_store ; solveF.
      MReplace ( (M1 ++ M2 ++ [F ** G]) ++ [l])  (M1 ++ (M2 ++ [l]) ++ [F ** G] ).
      apply EquivUpArrow2 with (L:= L1 ++ L2) (L' := L2 ++ L1);eauto.
      assert(HUp : RUp(n' + n)) by (apply IH;lia);
        eapply HUp ; solveF.
      (* forall *)
      generalize (H3 x);intro.
      assert(HUp : RUp(n' + n)) by (apply IH;lia).
      apply EquivUpArrow2 with (L:= L1 ++ Subst FX x ::L2) (L' := Subst FX x :: L2 ++ L1);eauto.
    Qed.

    (* ================================================ *)
    (* PROOF OF RUP *)
    (* Case when the 2 formulas are async. or pos. atoms*)
    (* ================================================ *)

    Lemma ITCaseAsyncAsync:  forall n m B M1 M2 F G, (Asynchronous F \/  IsPositiveAtom F) ->  (Asynchronous G \/ IsPositiveAtom G) -> n |-F- B; M1; UP [F] -> m |-F- B; M2; UP [G] ->  |-F- B; M1 ++ M2 ++ [F ** G]; UP [].
    Proof.
      intros.
      eapply tri_dec1 with (F:= F ** G) ; solveF.
      rewrite app_nil_r.
      eapply tri_tensor with (N:=M1) (M:=M2);solveF;
        eapply tri_rel ;auto using AsIsPosRelease;
          eapply AdequacyTri1;eauto.
    Qed.

    Lemma ITAsyncSync  : forall nm n m  B M1 M2 F G, (Asynchronous F \/ IsPositiveAtom F) ->  ~ Asynchronous G -> (forall m : nat, m <= nm -> RInd m) -> nm = n + m ->  LexpPos M1 -> LexpPos M2 -> n |-F- B; M1; UP [F] ->  m |-F- B; M2 ++ [G]; UP [] ->  |-F- B; M1 ++ M2 ++ [F ** G]; UP [].
    Proof.
      intros nm n m  B M1 M2 F G AF AG IH Hnm HM1 HM2 HD1 HD2.
      apply NotAsynchronousPosAtoms' in AG; destruct AG as [AG | AG].

      (* G is a positive atom... then, release works (Lemma  ITCaseAsyncAsync) *)
      eapply ITCaseAsyncAsync;eauto. apply trih_store;auto using IsPositiveAtomNotAssync ; solveF. eauto.


      (* G cannot do release *)
      inversion HD2;subst.
      + (* Case DEC 1*)
        rewrite union_comm in H0;
          simpl_union_context;subst.

        (* case focus on F *) 
        eapply tri_dec1 with (F:= F ** F0);solveF;try(solve_permutation);
          eapply tri_tensor with (N:=M1) (M:=M2) ; solveF.
        apply tri_rel;auto using AsyncRelease, AsIsPosRelease ; solveF. eapply AdequacyTri1;eauto.
        rewrite HeqM; eapply AdequacyTri1;eauto.

        (* case focus on other formula *)
        MReplaceIn L' (L1 ++ [G])  H1.
        rewrite H2.
        eapply tri_dec1 with (F:= F0) ; solveF.
        (* We use the HI on H1 and HD1 *)
        assert(IH2 : RInd(n + S n0)) by(  apply IH;auto); destruct IH2 as [HUp HDw].
        assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
        MReplace (M1 ++ L1 ++ [F ** G]) ( (L1 ++ M1) ++ [F ** G]).
        apply TensorComm'.
        MReplace ( (L1 ++ M1) ++ [G ** F] ) ( L1 ++ M1 ++ [G ** F] ).
        apply HDw with n0 n;try(lia);auto using PosFNegAtomPorOrNegAtom ; solveF.

      + (* Case DEC 2 *)
        assert(IH2 : RInd(n + S n0)) by(  apply IH;auto);
          destruct IH2 as [HUp HDw].
        assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
        eapply tri_dec2 with (F:=F0);solveF.
        unfold RDown in HDw.
        MReplace (M1 ++ M2 ++ [F ** G]) ( (M2 ++ M1) ++ [F ** G]).
        apply TensorComm'.
        MReplace ( (M2 ++ M1) ++ [G ** F]) ( M2 ++ M1 ++ [G ** F]).
        eapply HDw with n0 n;try(lia);auto using PosFNegAtomPorOrNegAtom;solveF.
    Qed.


    Ltac TensorFlip M1 M2 F G :=
      MReplace (M1 ++ M2 ++ [F ** G]) ((M2 ++ M1) ++ [F ** G] ); apply TensorComm'; MReplace ((M2 ++ M1) ++ [G ** F]) (M2 ++ M1 ++ [G ** F]).




    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Case when both formulas are not Async *)
    (* =============================================== *)
    Lemma ITSyncSync : forall nm n m  B M1 M2 F G, ~ Asynchronous F -> ~ Asynchronous G ->  (forall m : nat, m <= nm -> RInd m) -> S nm = S n + S m -> LexpPos M1 -> LexpPos M2 -> S n |-F- B; M1 ; UP [F] -> S m |-F- B; M2 ; UP [G] ->  |-F- B; M1 ++ M2 ++ [F ** G]; UP [].
    Proof.
      intros nm n m  B M1 M2 F G AF AG IH Hnm HM1 HM2 HD1 HD2.
      apply NotAsynchronousPosAtoms' in AF; destruct AF as [AF | AF];
        apply NotAsynchronousPosAtoms' in AG; destruct AG as [AG | AG].
      + (* Both are positive *)
        eapply ITCaseAsyncAsync;eauto.
      + (* F is a positive atom *)
        assert(~Asynchronous G) by auto using PosFIsNegAAsync.
        assert(~Asynchronous F) by auto using IsPositiveAtomNotAssync.
        inversion HD2;subst ; solveF.
        eapply ITAsyncSync with (nm:=nm) (n:= S n) (m:= m) ;eauto. lia.

      + (* G is a positive atom *)
        assert(~Asynchronous G) by auto using IsPositiveAtomNotAssync.
        assert(~Asynchronous F) by auto using PosFIsNegAAsync.
        inversion HD1;subst ; solveF.
        TensorFlip M1 M2 F G.
        eapply ITAsyncSync with (nm:=nm) (n:= S m) (m:= n) ;eauto. lia.
      +  (* F nor G can do release *)
        assert(HAG : ~Asynchronous G) by auto using PosFIsNegAAsync.
        assert(HAF : ~Asynchronous F) by auto using PosFIsNegAAsync.
        inversion HD1;subst ; solveF.
        inversion HD2;subst ; solveF.

        inversion H5;subst;inversion H7;subst.
        ++ (* DEC1 DEC1 *)
          rewrite union_comm in H0.
          rewrite union_comm in H3.
          simpl_union_context;subst.
          apply DestructMSet in H0; destruct H0 as [Hten1' | Hten2' ];
            [ destruct Hten1' as [HeqE' HeqM'] | destruct Hten2' as [L1' Hten2']; destruct Hten2'];subst.
          (* F and G were chosen *)
          eapply tri_dec1 with (F:= F0 ** F1) ; solveF.
          rewrite HeqM'. rewrite HeqM.
          apply tri_tensor with (N:= L') (M:= L'0);solveF;try solve_permutation;
            eapply AdequacyTri1;eauto.
          (* G is chosen *)
          rewrite H3.
          eapply tri_dec1 with (F:= F0) ; solveF.
          MReplaceIn L' (L1' ++ [F]) H1.
          assert (IH' : RInd (S n0 + S (S n))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by lia;rewrite Hn in HDw;clear Hn.
          eapply  HDw with n0 (S ( S n));auto using PosFNegAtomPorOrNegAtom; solveF.
          (* Nor F nor G were chosen *)
          rewrite H9.
          eapply tri_dec1 with (F:= F1) ; solveF.
          MReplaceIn L'0 (L1 ++ [G]) H8.
          assert (IH' : RInd (S n + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          TensorFlip M1 L1 F G.
          eapply  HDw with n (S ( S n0));auto using PosFNegAtomPorOrNegAtom. solveF.
        ++ (* DEC 1 DEC 2 *)
          eapply tri_dec2 with (F:=F1) ; solveF.
          assert (IH' : RInd (S n + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          TensorFlip M1 M2 F G.
          eapply  HDw with n (S ( S n0));auto using PosFNegAtomPorOrNegAtom.
        ++ (* DEC 2 DEC 1 *)
          eapply tri_dec2 with (F:=F0) ; solveF.
          assert (IH' : RInd (S n0 + S (S n))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by lia;rewrite Hn in HDw;clear Hn.
          eapply HDw with n0 (S ( S n));auto using PosFNegAtomPorOrNegAtom.
        ++ (* DEC 2 DEC 2 *)
          eapply tri_dec2 with (F:=F0) ; solveF.
          assert (IH' : RInd (S n0 + S (S n))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by lia;rewrite Hn in HDw;clear Hn.
          eapply  HDw with n0 (S ( S n));auto using PosFNegAtomPorOrNegAtom.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)
    Theorem InvTensorUP: forall  nm , (forall m : nat, m <= nm-> RInd m) -> RUp (S nm).
    Proof.
      intros nm IH.
      unfold RUp.  intros B L1  M1 L2 M2  F  G n' m' HNM HM1pos  HM2pos HD1 HD2.
      destruct L1;destruct L2;simpl in *.
      + (* L1 and L2 are Empty *)   
        inversion HD1;inversion HD2;subst;solveF;
          try(
              match goal with
              | [ |- |-F- ?B; ?M1 ++ ?M2 ++ [?F ** ?G]; UP [] ]
                => tryif (assert(HAFG :Asynchronous F /\ Asynchronous G) by (split;solveF))
                then
                  eapply ITCaseAsyncAsync;eauto
                else idtac
              end).
        eapply ITAsyncSync with  (nm := nm) (n:= 0%nat) (m:=n) ;try lia;solveF;eauto.
        apply ITAsyncSync with (nm:=nm) (n:= S n) (m:=n0);try lia;solveF.
        apply ITAsyncSync with (nm:=nm) (n:= S n) (m:=n0);try lia;solveF.
        apply ITAsyncSync with (nm:=nm) (n:= S (max n m)) (m:=n0);try lia;solveF.
        apply ITAsyncSync with (nm:=nm) (n:= S n) (m:=n0);try lia;solveF.
        TensorFlip M1 M2 F Top.  eapply ITAsyncSync with  (nm := nm) (n:= 0%nat) (m:=n) ;try lia;solveF;eauto.
        TensorFlip M1 M2 F Bot.  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) ;try lia;solveF;eauto.
        TensorFlip M1 M2 F (F1 $ G0).  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) ;try lia;solveF;eauto.
        TensorFlip M1 M2 F (F1 & G0).  eapply ITAsyncSync with  (nm := nm) (n:= S (max n0 m)) (m:=n) ;try lia;solveF;eauto.
        TensorFlip M1 M2 F (? F1).  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) ;try lia;solveF;eauto.
        (* both F and G are not asynchronous formulas *)
        eapply  ITSyncSync with (nm := nm) (n:=n) (m:=n0) ; solveF.

        TensorFlip M1 M2 F (F{ FX}).  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) ;try lia;solveF;eauto.
        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) ;try lia;solveF;eauto.

      + (* L1 is empty and L2 is not empty *)
        apply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m') (L1 := []) ; solveF.
      + (* L1 is not empty and L2 is empty *)
        assert( |-F- B; M2 ++ M1 ++ [G ** F]; UP ([] ++ l :: L1 )).
        eapply InvTensorConsNil with (nm:=nm) (n':=m') (m':=n') ; solveF. lia.
        apply AdequacyTri2 in H. destruct H.
        rewrite app_nil_r in *.
        MReplaceIn (M2 ++ M1 ++ [G ** F]) ((M2 ++ M1) ++ [G ** F]) H.
        apply TensorComm in H.
        MReplace (M1 ++ M2 ++ [F ** G]) ((M2 ++ M1) ++ [F ** G]).
        eapply AdequacyTri1;eauto.
      + (* L1 and L2 are not empty *)
        apply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m') (L1 := l :: L1) ; solveF.
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)
    Theorem InvTensorDW: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof.
      intros n IH.
      unfold RDown.  intros B M M'  H  F G n0 m Hnm  HM1pos HM2pos HPosF HD1 HD2.
      caseLexp H;subst;solveF; inversion HD1;subst;try(contradiction_multiset) ; solveF.
      ++ (* atom 1 *)
        (* HD1  + HM1Pos is inconsistent *)
        apply  NegPosAtom in H4.
        apply AppSingleton in H;subst;simpl in *.
        inversionF HD1.
        assert(False) by (eapply NegPosAtomContradiction;eauto).
        contradiction.
      ++ (* atom 2 *)
        apply UpExtension in H5;auto using LexpPosOrNegAtomConc.
        destruct H5.
        destruct H.
        assert(HRI: RInd (m + x)). apply IH. lia.
        eapply tri_rel ; solveF.
        destruct HRI as [HUp  HDown]. clear HDown.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ([A3 ⁺] ++ [])).
        eapply HUp with x m ; solveF. lia.
        eapply EquivUpArrow2;eauto.
      ++ (* perp1 *)
        (* same inconsistency *)
        apply  NegPosAtom in H4.
        apply AppSingleton in H;subst;simpl in *.
        inversionF HD1.
        assert(False) by (eapply NegPosAtomContradiction;eauto).
        contradiction.
      ++ (* perp2 *)
        apply UpExtension in H5;auto using LexpPosOrNegAtomConc.
        destruct H5.
        destruct H.
        assert(HRI: RInd (m + x)). apply IH. lia.
        eapply tri_rel ; solveF.
        destruct HRI as [HUp  HDown]. clear HDown.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ( [A3 ⁻] ++ [])).
        eapply HUp with x m ; solveF. lia.
        eapply EquivUpArrow2;eauto.
      ++ (* bbot *)
         apply UpExtension in H4;auto using LexpPosOrNegAtomConc.
        destruct H4 as [m' H4]. destruct H4 as [H4 H4'].
        assert(HRI: RInd (m' + m))  by (apply IH ;lia).
        destruct HRI as [HUp HDown] ; solveF.
        apply tri_rel ; solveF.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ( [⊥] ++ [])).
        eapply HUp with m' m ; solveF.
        eapply EquivUpArrow2;eauto.
      ++ (* tensor *)
        symmetry in H2.
        assert(HC: M ++ [F] =mul= [F] ++ M) by solve_permutation; rewrite HC in H2;clear HC.
        (* 2 choices: F is M or in N *)
        simpl_union_context.
        +++ rewrite union_comm in HL1.
            rewrite HL1 in H7. rewrite H.
            assert(HRI: RInd (S m + m0)). apply IH. lia.
            destruct HRI as [HUp  HDown];auto.
            eapply HDown in H7 ; solveF.
            apply AdequacyTri1 in H3.
            apply H7 in HD2.
            eapply tri_tensor with (N:=N ) (M:=L1 ++ M' ++ [F ** G]) ; solveF.
            lia.
            assumption.
        +++ rewrite union_comm in HL2.
            rewrite HL2 in H3. rewrite H.
            assert(HRI: RInd (S m + n)). apply IH. lia.
            destruct HRI as [HUp HDown] ; solveF.
            eapply HDown in H3 ; solveF.
            apply AdequacyTri1 in H7.
            apply H3 in HD2.
            eapply tri_tensor with (M:=M0 ) (N:=L2 ++ M' ++ [F ** G]) ; solveF.
            lia.
            assumption.
      ++ (* Par *)
        apply UpExtension in H6;auto using LexpPosOrNegAtomConc.
        destruct H6 as [m' [H6 H6']].
        assert(HRI: RInd (m' + m))  by (apply IH ;lia).
        destruct HRI as [HUp HDown] ; solveF.
        apply tri_rel ; solveF.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ( [F0 $ G0] ++ [])).
        eapply HUp with m' m ; solveF.
        eapply EquivUpArrow2;eauto.
      ++ (* oplus1 *)
        assert(HRI: RInd (S m +n)) by (apply IH ; lia).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply tri_plus1.
        eapply HDown with n m ; solveF.
        lia.
      ++ (* oplus2 *)
        assert(HRI: RInd (S m +n)) by (apply IH ; lia).
        destruct HRI as [HUp HDown] ; solveF.
        rewrite Nat.sub_0_r in HDown.
        apply tri_plus2.
        eapply HDown with n m ; solveF.
        lia.
      ++ (* with *)
        apply UpExtension in H6;auto using LexpPosOrNegAtomConc.
        destruct H6 as [m' [H6 H6']].
        assert(HRI: RInd (m' + m))  by (apply IH ;lia).
        destruct HRI as [HUp HDown] ; solveF.
        apply tri_rel ; solveF.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ( [F0 & G0] ++ [])).
        eapply HUp with m' m ; solveF.
        eapply EquivUpArrow2;eauto.

      ++ (* quest *)
        apply UpExtension in H5;auto using LexpPosOrNegAtomConc.
        destruct H5 as [m' [H5 H5']].
        assert(HRI: RInd (m' + m))  by (apply IH ;lia).
        destruct HRI as [HUp  HDown] ; solveF.
        apply tri_rel ; solveF.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ( [? F0] ++ [])).
        eapply HUp with m' m ; solveF.
        eapply EquivUpArrow2;eauto.

      ++ (* exists *)
        assert(HRI: RInd (m + S n)) by (apply IH;lia).
        destruct HRI as [HUp HDown] ; solveF.
        eapply HDown in H3;eauto.
        lia.
      ++ (* forall *)
        apply UpExtension in H4;auto using LexpPosOrNegAtomConc.
        destruct H4 as [m' [H4 H4']].
        assert(HRI: RInd (m' + m))  by (apply IH ;lia).
        destruct HRI as [HUp HDown] ; solveF.
        apply tri_rel ; solveF.
        assert(|-F- B; M ++ M' ++ [F ** G]; UP ( [F{ FX}] ++ [])).
        eapply HUp with m' m ; solveF.
        eapply EquivUpArrow2;eauto.
    Qed.


    Theorem InvTensorAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split.
        apply InvTensorUP. assumption.
        simpl.  rewrite Nat.sub_0_r.
        apply InvTensorDW. assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)
    
    Theorem InvTensor : forall B L L' F G  M M', LexpPos M  -> LexpPos M' ->  |-F- B  ;M ; UP (F :: L) -> |-F- B; M'; UP (G :: L') -> |-F- B ; M ++ M' ++ [F ** G]  ; UP (L ++ L') .
    Proof.
      intros.
      apply EquivUpArrow2 with (L' := L ++ [F]) in H1 ;eauto.
      apply EquivUpArrow2 with (L' := L' ++ [G]) in H2 ;eauto.
      assert(HRn:  forall n, RUp n) by (apply InvTensorAux).
      apply AdequacyTri2 in H1.
      apply AdequacyTri2 in H2.
      destruct H1.
      destruct H2.
      generalize (HRn (x + x0));intros.
      eapply H3 in H;eauto.
    Qed.

  End InvTensor.


  (* =============================================== *)
  (** Completeness Theorem *)
  (* =============================================== *)
  Module Completeness.


    Theorem CompletenessAux : forall B L n,  n |-- B ; L -> |-F- B ; empty ; UP L.
    Proof.
      intros.
      generalize dependent B.
      generalize dependent L.
      induction n  using strongind; intros L  B H1.
      +  (* Base case *)
        inversion H1;subst;simpl.
        ++ (* Init *)
          generalize( ApropPosNegAtom A3);intro HA3.
          destruct HA3 as [HA3 | HA3];
            (* Positive Polarity *)
            apply EquivUpArrow2 with (L:= [A3 ⁺; A3 ⁻]);NegPhase ; solveF.
          eapply tri_dec1 with (F:=A3 ⁻).
          apply PositiveNegativeAtomNeg;auto.
          eauto.
          solveF.

          (* Negative Atom *)
          eapply tri_dec1 with (F:=A3 ⁺).
          apply NegativePositiveAtomNeg ; solveF.
          eauto.
          solveF.
        ++ (* one *)
          apply EquivUpArrow2 with (L:= [1]) ; solveF. NegPhase.
          eapply tri_dec1 with (F:=1) ; solveF.
        ++ (* top *)
          apply EquivUpArrow2 with (L:= ⊤ :: M) ; solveF.
      + (* Inductive Cases *)
        inversion H1;subst;solveF;
          try(match goal with [H : ?L =mul= ?M |- |-F- _ ; _ ; UP ?L] =>
                              apply EquivUpArrow2 with (L:= M) end);auto; NegPhase.
        ++ (* Bot *)
          eapply H with (m:=n) ; solveF.
        ++ (* PAR *)
          eapply H with (m:=n) ; solveF.
        ++ (* Tensor *)
          apply H in H3 ; solveF.
          apply H in H4 ; solveF.
          MReplace ([F ** G]) ( [] ++ [] ++ [F ** G]). 
          apply InvTensor.InvTensor ; solveF.
        ++ (* OPLUS1 *)
          apply H in H3 ; solveF.
          MReplace ([F ⊕ G]) ( [] ++ [F ⊕ G]). 
          apply InvOPlus.InvPlus ; solveF.
        ++ (* OPLUS2 *)
          apply H in H3 ; solveF.
          MReplace ([F ⊕ G]) ( [] ++ [F ⊕ G]).
          apply InvOPlus.InvPlusComm ; solveF.
        ++ (* With *)
          apply H with m ; solveF.
        ++ (* With2 *)
          apply H with n0 ; solveF.
        ++ (* Copy *)
          apply H in H4 ; solveF.
          apply EquivUpArrow2 with (L':= F :: L) in H4 ; solveF.
          MReplaceIn (B) (B0 ++ [F]) H4.
          apply InvCopy.InvCopy in H4 ; solveF.
          MReplace (B) (B0 ++ [F]). solveF.
        ++ (* Quest *)
          apply H in H3 ; solveF.
          MReplace (B ++ [F]) (F :: B). solveF.
        ++ (* Bang *)
          apply H in H3 ; solveF.
          eapply tri_dec1 with (F:=!F) ; solveF.
        ++ (* exists *)
          apply H in H3 ; solveF.
          apply InvExists.InvEx in H3 ; solveF.
        ++ (* forall *)
          generalize (H3 x);intro H3'.
          apply H in H3' ; solveF.
    Qed.

    Theorem Completeness : forall B L M n,  n |-- B ; M ++ L -> LexpPos M -> |-F- B ; M ; UP L.
    Proof.
      intros.
      apply CompletenessAux in H.
      apply AdequacyTri2 in H.
      destruct H.
      apply  StoreInversionL in H ; solveF.
      destruct H.
      eapply AdequacyTri1;eauto.
    Qed.

  End Completeness.

End InvLemmas.
