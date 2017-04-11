(* Add LoadPath "../../".    *)
Require Export TriSystem. 
Require Export MSet. 
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import StructuralRulesTriSystem.

Set Implicit Arguments.

Module InvCopy.
  
Definition RUp (n:nat) := forall B L  F  M , 
      lexpPos M -> 
      n |-F- B ++ [F] ;M ; UP (L ++ [F]) 
                            -> exists m, m|-F- B ++ [F] ; M ; UP (L ).

Definition RDown (n:nat) := forall B  F  M  H, 
    lexpPos M -> AsynchronousF F = false ->
    n |-F- B ++ [F]; M ++ [F]  ; DW H
                                   -> exists m, m|-F- B ++ [F] ; M  ; DW H.



Lemma RDown0 : RDown 0.
Proof.
  unfold RDown.
  intros.
  inversion H1;subst.
  destruct M. simpl in *.
  inversion H2. subst.
  eexists.
  eapply tri_init2;eauto.
  inversion H2. subst.
  apply EmptyMS in H7.
  contradiction.
Qed.




Definition RInd (n:nat) := RUp n /\ RDown (n -1). 


Lemma RUp0 : RUp 0.
  unfold RUp.
  intros.
  
  destruct L.
  + inversion H0;subst.
    eexists.
    simpl.
    eapply tri_dec2 with (F:= ⊤);auto.
    eapply tri_rel;auto.
    eapply tri_top.
  + inversion H0. subst.
    
    eexists.
    eapply tri_top.
Qed.



Theorem InvCopyAux1: forall  n , (forall m : nat, m <= n -> RInd m) -> RUp (S n).
  intros n IH.
  unfold RUp.  intros B L1 F M1 HM1pos HD1.
  destruct L1.
  + (* L1 is Empty *)
    simpl in *.
    assert (HF: NotPosOrPosAtom F \/ PosOrPosAtom F) by (apply DecPosOrPosAtom). 
    destruct HF as [HF | HF].
    inversion HF;subst.
    ++  (* Neg Atom *)
      inversion HD1;subst.
      (* Decide 1 *)
      inversion H5;subst.
      rewrite union_comm_app in H0.
      simpl_union_context;subst.
      inversion H.
 
     (*  rewrite union_comm in H0. 
        Agora, temos duas notações, comutatividade só pra ++. *)
      rewrite meq_cons_append in H0. 
      rewrite H0 in H1.
      
      
       assert (Hn : S n0 <= S n0) by auto.
       generalize (IH (S n0) Hn);intros.
       destruct H3.

       unfold RDown in H6.
       simpl in H6.
       rewrite Nat.sub_0_r in H6.

       apply H6 in H1; auto.
       destruct H1.
       eexists.
       rewrite H2.
       eapply tri_dec1 with (F:=F);eauto.
       apply LPos1  with (M:= [F] ++ L1) in HM1pos;auto.
       eapply LPos3 in HM1pos. eassumption. eauto.

    (* Decide 2 *)
       rewrite union_comm_app in H0.
      simpl_union_context;subst.
      simpl in H. intuition.
      assert (Hn : S n0 <= S n0) by auto.
      generalize (IH (S n0) Hn);intros.
       destruct H3.

       unfold RDown in H6.
       simpl in H6.
       rewrite Nat.sub_0_r in H6.

       apply H6 with (H:=F) in H1;auto.
       destruct H1.
       eexists.
       
       eapply tri_dec2 with (F:=F);auto.
       rewrite H2. eauto.
       eassumption.
    ++ (* Top *) 
      eexists. eapply tri_dec2 with (F:= ⊤);auto. eapply tri_rel;auto. apply tri_top.
    ++ (* bot *)
      inversion HD1;subst.
      eexists. eapply tri_dec2 with (F:= ⊥);auto. eapply tri_rel;auto. apply tri_bot. eassumption.
      simpl in H4. intuition.
    ++ (* Par *)
      inversion HD1;subst.
      eexists. eapply tri_dec2 with (F:= F0 $ G);auto. eapply tri_rel;auto. apply tri_par. eassumption.
      simpl in H4. intuition.
    ++ (* With *)
      inversion HD1;subst.
      eexists. eapply tri_dec2 with (F:= F0 & G);auto. eapply tri_rel;auto. apply tri_with; eassumption.
      simpl in H4. intuition.
    ++ (* quest *)
      inversion HD1;subst.
       eexists. eapply tri_dec2 with (F:= ? F0);auto. eapply tri_rel;auto. apply tri_quest. eassumption.
       simpl in H4. intuition.
    ++
      (* Store *)
      inversion HD1;subst.
       inversion HF.
       inversion HF.
       inversion HF.
       inversion HF.
       inversion H5;subst.
       rewrite union_comm_app in H0.
       simpl_union_context ; subst.

       (* Decide 1 *)
       eexists.
       rewrite HeqM.
       eapply tri_dec2 with (F:=F0);eauto.

       (* Decide 2 *)
       rewrite meq_cons_append in H0.
      rewrite H0 in H1.
       
       generalize(IH (S n0) (le_n (S n0)));intros.
       destruct H3.
       simpl in H6.
       rewrite Nat.sub_0_r in H6.
       apply H6 in H1;auto.
       destruct H1.
       eexists.
       rewrite H2.
       eapply tri_dec1 with (F:=F0);eauto.
       apply LPos1  with (M:= [F0] ++ L1) in HM1pos;auto.
       eapply LPos3 in HM1pos. eassumption. eauto.
       
       

       rewrite H0 in H1.
       generalize(IH (S n0) (le_n (S n0)));intros.
       destruct H2.
       simpl in H3.
       rewrite Nat.sub_0_r in H3.
       rewrite <- H0 in H1.
       apply H3 in H1;auto.
       destruct H1.
       eexists.
       rewrite H0.
       eapply tri_dec2 with (F:=F0);auto.
       rewrite <- H0.
       eassumption.
       
  +  (* L is not empty *)
    inversion HD1;subst.
    ++   
      generalize(IH n (le_n n));intros.
      eapply H in H3;auto.
      destruct H3.
      eexists.
      eapply tri_bot.
      eassumption.
    ++ generalize(IH n (le_n n));intros.
       assert (Heq: F0 :: G :: L1 ++ [F] = (F0 :: G :: L1) ++ [F]) by auto.
       rewrite Heq in H3.
      eapply H in H3;auto.
      destruct H3.
      eexists.
      eapply tri_par.
      eassumption.
    ++
      assert (Hn0: n0 <= Init.Nat.max n0 m) by auto.
      generalize(IH n0 Hn0);intros.
      assert (Hm: m <= Init.Nat.max n0 m) by auto.
      generalize(IH m Hm);intros.
      
      rewrite app_comm_cons in H4.
      rewrite app_comm_cons in H5.
      eapply H in H4;auto.
      eapply H0 in H5;auto.
      destruct H4.
      destruct H5.
      eexists. eapply tri_with;eauto.
    ++ generalize(IH n (le_n n));intros.
       assert (Heq : (B ++ [F]) ++ [F0] =mul= (B ++ [F0]) ++ [F]) by solve_permutation.
       rewrite Heq in H3.
       eapply H in H3;auto.
       destruct H3.
       eexists.
       eapply tri_quest.
       rewrite Heq.
      eassumption.
    ++ generalize(IH n (le_n n));intros.
       eapply H  in H5;auto.
       destruct H5.
       eexists.
       eapply tri_store;auto.
       eassumption.
       apply LPos1 with (L:= [l] ++ M1);eauto.
       firstorder.
Qed.



Theorem InvCopyAux2: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).
  intros n IH.
  unfold RDown.  intros B F M H  HM1pos HPosF  HD1.
  elim (DecPosOrPosAtom H);intro HHpos.
  + (* H is not positive or atom *)
    inversion HHpos;subst.
    ++ (* Neg Atom *)
      inversion HD1;subst.
      apply UpExtension in H4.
      destruct H4 as [n'  [IHn IHd]].
      inversion IHd;subst.
      assert(Hnm: n <= S n0 ) by omega.
      generalize(IH n Hnm);intros.
    
      destruct H.
      unfold RUp in H.
       
      assert( exists m0 : nat, m0 |-F- B ++ [F]; M ++ [v ⁻] ; UP ([] ++ [])).
      apply H  ;auto.
      apply LPos1 with (L:= [v ⁻] ++ M);eauto. firstorder.
      
      destruct H2.
      eexists.
      eapply tri_rel;auto. eapply tri_store;auto.
      simpl in H2.
      eassumption.
      apply LPos1 with (L:= [F] ++ M);eauto. firstorder. 
    ++ (* top *)
    eexists.
    eapply tri_rel;auto. eapply tri_top;auto.
    ++ (* bot *)
      inversion HD1;subst.
      apply UpExtension in H4.
      destruct H4 as [n'  [IHn IHd]].
      simpl in IHd.
      inversion IHd;subst.
      
      assert(Hnm: n <= S n0 ) by omega.
      generalize(IH n Hnm);intros.
    
      destruct H.

      assert( exists m0 : nat, m0 |-F- B ++ [F]; M ; UP ([] ++ [])).
      apply H;auto.

      destruct H2. simpl in H2.
      eexists.
      eapply tri_rel;auto. eapply tri_bot;auto. eassumption.
      simpl in H5.
      intuition.
      
      apply LPos1 with (L:= [F] ++ M);eauto.
      constructor;auto using PosOrPosAtomAsync.
      
    ++ (* Par *)
      inversion HD1;subst.
      apply UpExtension in H4.
      destruct H4 as [n'  [IHn IHd]].
      simpl in IHd.
      inversion IHd;subst.
      
      assert(Hnm: n <= S n0 ) by omega.
      generalize(IH n Hnm);intros.
    
      destruct H.
      
      assert( exists m0 : nat, m0 |-F- B ++ [F] ; M ; UP ([F0 ; G] ++ [])).
      apply H;auto.
      
      destruct H2. simpl in H2.
      eexists.
      eapply tri_rel;auto. eapply tri_par;auto. eassumption.
      simpl in H5.
      intuition.
      apply LPos1 with (L:= [F] ++ M);eauto.
      constructor;auto using PosOrPosAtomAsync.
      
    ++ (* with *)
      inversion HD1;subst.
      apply UpExtension in H4.
      destruct H4 as [n'  [IHn IHd]].
      simpl in IHd.
      inversion IHd;subst.
      
      
      (* assert(Hnm0: (Init.Nat.max n  m)  <= S n0 ) by omega.*)
      apply le_S_n in IHn.
      
      assert(Hnm1:  n <=  S n0 ). apply Nat.le_trans with (m:=Init.Nat.max n m);auto.
      assert(Hnm2:  m <=  S n0 ). apply Nat.le_trans with (m:=Init.Nat.max n m);auto.

      
      generalize(IH n Hnm1);intros.
      generalize(IH m Hnm2);intros.
    
      destruct H.
      destruct H1.
      
      assert( exists m0 : nat, m0 |-F- B ++ [F]; M; UP ([F0] ++ []))
        by ( apply H;auto).

      assert( exists m0 : nat, m0 |-F- B ++ [F]; M; UP ([G] ++ []))
        by (apply H1;auto).
      

      destruct H4. simpl in H4.
      destruct H6. simpl in H6.
      eexists.
      eapply tri_rel;auto. eapply tri_with;auto; eassumption.
      inversion H5. intuition.
      
      apply LPos1 with (L:= [F] ++ M);eauto.
      constructor;auto using PosOrPosAtomAsync.
      
    ++ (* Quest *)
      inversion HD1;subst.
      apply UpExtension in H4.
      destruct H4 as [n'  [IHn IHd]].
      simpl in IHd.
      inversion IHd;subst.
      
      assert(Hnm: n <= S n0 ) by omega.
      generalize(IH n Hnm);intros.
     
      destruct H.
      assert (Mequiv :  (B ++ [F]) ++ [F0] =mul=  (B ++ [F0]) ++ [F]) by solve_permutation.


      assert( exists m0 : nat, m0 |-F- (B ++ [F0]) ++ [F]; M; UP ([] ++ [])).
      apply H;auto. simpl. rewrite <- Mequiv. assumption.

      destruct H2.
      eexists.
      eapply tri_rel;auto.  eapply tri_quest;auto.
      rewrite Mequiv. eassumption.
      
      simpl in H5.
      intuition.
      apply LPos1 with (L:= [F] ++ M);eauto.
      constructor;auto using PosOrPosAtomAsync.

  + (* H is positive *)
    inversion HHpos;subst.
    ++ (* Positive Atom *)
      inversion HD1;subst.
      apply eq_then_meq in H2.
      symmetry in H2.
      rewrite union_comm_app in H2.
      apply resolvers2 in H2.
      destruct H2.
      
      subst.
      eexists.
      eapply tri_init2;eauto.

      
      apply eq_then_meq in H.
      contradiction_multiset.
      
      simpl in H0. 
      intuition.

    ++ (* 0 *)
      inversion HD1;subst.
      simpl in H0.
      intuition.

    ++ (* one *)
      inversion HD1;subst.
      apply eq_then_meq in H2.
      contradiction_multiset.

      simpl in H0.
      intuition.
    ++ (* Tensor *)
      inversion HD1;subst.
      assert (Ht : M++[F] =mul= [F] ++ M) by eauto.
      rewrite Ht in H1. clear Ht.
      symmetry in H1.
      assert ((exists L1, M0 =mul= [F] ++ L1) \/ (exists L2, N =mul= [F] ++ L2)) as Hten.
      eapply solsls. eapply H1.
      destruct Hten as [Hten1 | Hten2].
      
      
      +++ (* destruct HFnm as [M0' HFnm]. *)
        destruct Hten1 as [L1 HL1];
        assert (M =mul= N ++ L1) by ( eapply solsls2;eauto).
          rewrite union_comm_app in HL1.
          eapply TriExchange with (M' := L1 ++ [F]) in H6;auto .
          assert (Hn1 : S m <= S (Init.Nat.max n0 m)) by (auto using le_n_S).

          generalize(IH (S m) Hn1);intros.
          
          destruct H0.
          assert(exists m0 : nat, m0 |-F- B ++ [F] ; L1 ; DW G).
          apply H2 ;eauto. 
          eapply LPos2 in HM1pos;eauto.
          simpl.
          rewrite Nat.sub_0_r.
          rewrite union_comm_app.
          rewrite app_nil_r in H6.
          apply H6.
          
          destruct H3.
          eexists.
          eapply tri_tensor with (N:= N) (M:= L1);auto.
          rewrite H.
          solve_meq.
          eauto.
          eauto.
      +++
        destruct Hten2 as [L2 HL2].
        rewrite union_comm_app in H1.
        assert (M =mul= M0 ++ L2) by (eapply solsls2; eauto).
        
        rewrite union_comm_app in HL2.
        
          eapply TriExchange with (M' := L2 ++ [F]) in H5;auto .
          assert(Hn1: (S n0)  <= S(Init.Nat.max n0 m) ) by (auto using le_n_S). 
          generalize(IH (S n0) Hn1);intros.
          destruct H0.
          assert(exists m0 : nat, m0 |-F- B ++ [F] ; L2; DW F0).
          apply H2;eauto. 
          eapply LPos2 in HM1pos;eauto.

          simpl.
          rewrite Nat.sub_0_r.
          rewrite union_comm_app.
          rewrite app_nil_r in H5.
                    
          assumption.
          
          
          destruct H3.
          eexists.
          eapply tri_tensor with (M:= M0) (N:= L2 );auto.
          eassumption.
          eassumption.
          
      +++ simpl in H0.
          intuition.
          
      
    ++ (* Oplus *)
      inversion HD1;subst.
      generalize(IH (S n0) ( le_n (S n0)));intros.
      destruct H.
      assert(exists m0 : nat, m0 |-F- B ++ [F]; M ; DW F0).
      apply H0;auto.
      simpl.
      rewrite Nat.sub_0_r.
      assumption.

      destruct H1.
      eexists.
      eapply tri_plus1;eauto.

      (* Symmetric for G0 *)
      generalize(IH (S n0) ( le_n (S n0)));intros.
      destruct H.
      assert(exists m0 : nat, m0 |-F- B ++ [F]; M; DW G).
      apply H0;auto.
      simpl.
      rewrite Nat.sub_0_r.
      assumption.

      destruct H1.
      eexists.
      eapply tri_plus2;eauto.
      simpl in H0.
      intuition.

    ++ (* bang *)
      inversion HD1;subst.
      apply eq_then_meq in H.
      contradiction_multiset.
      
      simpl in H0.
      intuition.
Qed.
      

Theorem InvCopy' : forall n, RInd n.
  intro n.
  induction n using strongind.
  + unfold RInd.
    split; [apply RUp0 | apply RDown0].
  + unfold RInd in *.
    split.
    apply InvCopyAux1. assumption.
    simpl.  rewrite Nat.sub_0_r.

    apply InvCopyAux2. assumption.
Qed.

End InvCopy.
Export InvCopy.

Theorem InvCopy : forall B L F  M n,   n |-F- B ++ [F]  ;M ; UP (F :: L) -> lexpPos M  -> exists m, m|-F- B ++ [F] ; M  ; UP L .
  intros.
  apply EquivUpArrow with (L' := L ++ [F]) in H .
  destruct H.
  assert(HRn:  forall n, RUp n) by (apply InvCopy').
  
  generalize (HRn (x));intros.
  apply H1  ;auto.
  change (F::L) with ([F] ++ L).
  solve_permutation.
Qed.

