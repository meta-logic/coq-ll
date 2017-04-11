(* Add LoadPath "../../".  *)
Require Export TriSystem. 
Require Export StructuralRulesTriSystem.
Require Export MSet.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Hint Resolve  app_nil_r.

Module InvPlus.

  Lemma OPlusComm : forall B M F G X n, n |-F- B ; M ++ [F ⊕ G] ; X -> n |-F- B ; M ++ [G ⊕ F] ; X.
    intros.
    generalize dependent B.
    generalize dependent M.
    generalize dependent X.
    generalize dependent n.
    induction n using strongind;intros.
    + inversion H;subst.
      ++ (* H0 inconsistent *)
        apply eq_then_meq in H0. 
        symmetry in H0.
        rewrite union_comm_app in H0.
        apply resolvers2 in H0. intuition. inversion H1.
      ++ (* H0 inconsistent *)
        apply eq_then_meq in H0.
        contradiction_multiset. 
      ++ (* H0 inconsistent *)
        apply eq_then_meq in H0. 
        contradiction_multiset.     
      ++ (* Top *)
        eapply tri_top.
    + inversion H0;subst.
      ++ (* Tensor *)
        assert(H2': M0 ++ N =mul= [F ⊕ G] ++ M) by ( rewrite <- H2;solve_permutation).
        clear H2.
        
        assert ((exists L1, M0 =mul= [F ⊕ G] ++ L1) \/ (exists L2, N =mul= [F ⊕ G] ++ L2)) as Hten.
        eapply solsls;eauto.
        destruct Hten as [Hten1 | Hten2].
        +++
          destruct Hten1 as [L1 HL1]. assert (M =mul= N ++ L1) by (
                                                                   eapply solsls2;eauto).
          rewrite union_comm_app in H1.

          eapply TriExchange with (M' := L1 ++ [F ⊕ G] ) in H4; auto.
            apply H in H4; auto using Max.le_max_r.  
            eapply tri_tensor with (M:=L1 ++ [G ⊕ F]) (N:=N);auto.
            rewrite H1. solve_permutation.
            solve_permutation.
        +++
          destruct Hten2 as [L2 HL2].
          rewrite union_comm_app in H2'.
          assert (M =mul= M0 ++ L2).
          eapply solsls2 with (M:=N);eauto. 

          eapply TriExchange with (M' := L2 ++ [F ⊕ G]  ) in H3;auto.
            apply H in H3; auto using Max.le_max_l.
            eapply tri_tensor with (N:=L2 ++ [ G ⊕F]) (M:=M0);auto. rewrite H1. 
            solve_permutation.
            eauto.
      ++ (* Oplus *) apply tri_plus1;auto.
      ++ (* Oplus *) apply tri_plus2;auto.
      ++ (* bang *)
        apply eq_then_meq in H2. 
        contradiction_multiset.
      ++ (* Release *) apply tri_rel;auto.
      ++ (* bot *) apply tri_bot;auto.
      ++ (* par *) apply tri_par;auto.
      ++ (* with *) apply tri_with;auto.
      ++ (* quest *) apply tri_quest;auto.
      ++ (* store *)  
        eapply TriExchange with (M' :=  (M ++ [F0]) ++ [F ⊕ G]) in H3;auto.
        apply H in H3;auto.
        apply tri_store;auto.
        eapply TriExchange with (M' :=  (M ++ [G ⊕ F]) ++ [F0]) in H3;auto. 
        apply H3.
        solve_permutation.
        solve_permutation.

      ++ (* decide *)
        (* M ++ [F ⊕ G] =mul= [F0] ++ L' *)
        rewrite union_comm_app in H3.
        simpl_union_context.
        +++ subst.
            rewrite HeqM.
            eapply tri_dec1 with (F:= G ⊕ F);auto.
            
            inversion H4;subst.
            
            eapply tri_plus2. rewrite app_nil_r. assumption.
            eapply tri_plus1. rewrite app_nil_r. assumption.
            inversion H3.
      +++ rewrite meq_cons_append in H1.
          rewrite H1 in H4.
          apply H in H4;auto.
          rewrite H3.
          eapply tri_dec1 with (F:=F0);eauto.
          
      ++ (* decide B *)
        eapply tri_dec2;eauto.
Qed.





Definition RUp (n:nat) := forall B L  F G M , 
      lexpPos M -> 
      n |-F- B;M ; UP ( L ++ [F]) 
                   -> exists m, m|-F- B ; M  ++ [F ⊕ G] ; UP (L ).

Definition RDown (n:nat) := forall B  F G M  H, 
    lexpPos M ->
    PosOrPosAtom F -> 
    n |-F- B;M ++ [F] ; DW H
                         -> exists m, m|-F- B ; M  ++ [F ⊕ G] ; DW H.






Definition RInd (n:nat) := RUp n /\ RDown (n -1).


Lemma RUp0 : RUp 0.
  unfold RUp.
  intros.
  
  destruct L.
  + inversion H0;subst.
    eexists.
    simpl.
    eapply tri_dec1 with (F:= ⊤ ⊕ G);auto;
    eapply tri_plus1 ;auto;(
    eapply tri_rel;auto;
    eapply tri_top).
  + inversion H0. subst.
    simpl.
    eexists.
    eapply tri_top.
Qed.



Lemma RDown0 : RDown 0.
  unfold RDown.
  intros.
  inversion H2;subst.
  + destruct M. simpl in *. inversion H3. subst.
    inversion H1.
    inversion H3.
    apply EmptyMS in H5.
    contradiction.
  + apply EmptyMS in H3;contradiction.
  + apply EmptyMS in H3;contradiction.
Qed.


Theorem InvPlusAux1: forall  n , (forall m : nat, m <= n -> RInd m) -> RUp (S n).
  intros n IH.
  unfold RUp.  intros B L1 F G M1 HM1pos HD1.
  destruct L1.
  + (* L1 is Empty *)
    simpl in *.
    assert (HF: NotPosOrPosAtom F \/ PosOrPosAtom F) by (apply DecPosOrPosAtom). 
    destruct HF as [HF | HF].
    ++ (* F is not a positive formula *)
      eexists.
      eapply tri_dec1 with (F:=  F ⊕ G);auto.
      eapply tri_plus1.
      eapply tri_rel;auto.
      apply NotPosOrPosAtomRelease. assumption.
      rewrite app_nil_r.
      apply HD1.
    ++ (* F IS PosOrPosAtom *)
      apply StoreInversion in HD1;auto.
      simpl in HD1. rewrite Nat.sub_0_r in HD1.
      (* it must be a dec rule *)
      inversion HD1;subst.
      +++ (*DEC 1 *)
        rewrite union_comm_app in H0.
        simpl_union_context;subst.

        eexists.
        eapply tri_dec1 with (F:=F0 ⊕ G);auto.
        eapply tri_plus1.
        rewrite HeqM.
        rewrite app_nil_r.
        eassumption.
 
        rewrite H0 in H1.
        rewrite meq_cons_append in H1.
        assert(Hn : S n0 <= S n0) by auto.
        generalize(IH (S n0) Hn);intros.
        destruct H3. 
        simpl in H4. rewrite Nat.sub_0_r in H4.
        eapply H4 in H1;eauto.
        destruct H1.
        eexists.
        rewrite H2.
        eapply tri_dec1 with (F:=F0);auto.
        eapply H1.   
        apply LPos1 in H2;auto.
        inversion H2.
        auto. 
        
      +++  (* DEC 2 *)
        assert(Hn : S n0 <= S n0) by auto.
        generalize(IH (S n0) Hn);intros.
        destruct H2.
        simpl in H3. rewrite Nat.sub_0_r in H3.
        unfold RDown in H3.
        apply H3 with (G:=G) in H1;auto.
        destruct H1. rewrite H0 in H1.
        eexists.
        rewrite H0. 
        eapply tri_dec2 with (F:=F0);eauto.
    
  +   (* L is not empty *)
    inversion HD1;subst. 
    ++   
      generalize(IH n (le_n n));intros.
      destruct H.
      unfold RUp in H.
      apply H with (G:=G)in H3;auto.
      destruct H3.
      eexists.
      eapply tri_bot.
      eassumption.
    ++ generalize(IH n (le_n n));intros.
       destruct H.
       assert (F0 :: G0 :: L1 ++ [F] = (F0 :: G0 :: L1) ++ [F]) by auto.
       rewrite H1 in H3.
       unfold RUp in H.
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
      destruct H.
      destruct H0. 
      rewrite app_comm_cons in H4.
      rewrite app_comm_cons in H5.
      unfold RUp in H. unfold RUp in H0.
      eapply H with (G:=G) in H4;auto.
      eapply H0 with (G:=G) in H5;auto.
      destruct H4.
      destruct H5. 
      eexists. eapply tri_with;eauto.
    ++ generalize(IH n (le_n n));intros.
       destruct H.
       eapply H in H3;auto.
       destruct H3.
       eexists.
       eapply tri_quest. 
      eassumption.
    ++ generalize(IH n (le_n n));intros. 
       destruct H.
       unfold RUp in H.
       eapply H with (G:=G) in H5;auto. 
       destruct H5.
       eexists.
       eapply tri_store;auto.
       assert((M1 ++ [l]) ++ [F ⊕ G] =mul=  (M1 ++ [F ⊕ G]) ++ [l]) by solve_permutation.
       rewrite <- H2. eauto.
       apply LPos1 with (L:= [l] ++ M1);eauto.
       constructor;auto.
Qed.


  
                                                            

Theorem InvPlusAux2: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).
  intros n IH.
  unfold RDown.  intros B F G M H  HM1pos HPosF  HD1.
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
      assert( exists m0 : nat, m0 |-F- B; ((M ++ [v ⁻]) ) ++ [F ⊕ G]; UP ([] ++ [])).
      apply H  ;auto.
      
      apply LPos1 with (L:= [v ⁻] ++ M);auto. solve_permutation. firstorder.
      destruct H2.
      eexists.
      eapply tri_rel;auto. eapply tri_store;auto.
      simpl in H2. 
      eapply TriExchange.  apply H2. auto. solve_permutation.
      eapply LPos1;auto.
      rewrite union_comm_app. firstorder. apply PosOrPosAtomAsync;auto.
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
      
      assert( exists m0 : nat, m0 |-F- B; M ++ [F ⊕ G]; UP ([] ++ [])).
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
      
      assert( exists m0 : nat, m0 |-F- B; M ++ [F ⊕ G]; UP ([F0 ; G0] ++ [])).
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
      
      assert( exists m0 : nat, m0 |-F- B; M ++ [F ⊕ G]; UP ([F0] ++ []))
        by ( apply H;auto).

      assert( exists m0 : nat, m0 |-F- B; M ++ [F ⊕ G]; UP ([G0] ++ []))
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
      
      assert( exists m0 : nat, m0 |-F- B ++ [F0]; M ++ [F ⊕ G]; UP ([] ++ [])).
      apply H;auto.
      destruct H2.
      eexists.
      eapply tri_rel;auto. eapply tri_quest;auto. eassumption.
      
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
      destruct H2. subst.
      inversion HPosF.
      apply EmptyMS in H.
      contradiction.

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
      assert (Ht : M++[F] =mul= [F] ++ M) by solve_permutation.
      rewrite Ht in H1. clear Ht.
      symmetry in H1.
      assert ((exists L1, M0 =mul= [F] ++ L1) \/ (exists L2, N =mul= [F] ++ L2)) as Hten.
      eapply solsls;eauto.
      destruct Hten as [Hten1 | Hten2].
            
      +++ (* destruct HFnm as [M0' HFnm]. *)
        destruct Hten1 as [L1 HL1];
        assert (M =mul= N ++ L1) by ( eapply solsls2;eauto).

          rewrite union_comm_app in HL1.
          eapply TriExchange with (M' := L1 ++ [F]) in H6;auto .
          assert (Hn1 : S m <= S (Init.Nat.max n0 m)) by (auto using le_n_S).

          generalize(IH (S m) Hn1);intros.
          
          destruct H0.
          assert(exists m0 : nat, m0 |-F- B; L1 ++ [F ⊕ G]; DW G0).
          apply H2 ;eauto. 
          eapply LPos2 in HM1pos;eauto.
          simpl.
          rewrite Nat.sub_0_r.
          assumption.
          destruct H3. 
          eexists.
          eapply tri_tensor with (N:= N) (M:= L1 ++ [F ⊕ G]);auto.
          rewrite union_comm_app in H.
          rewrite H.
          solve_permutation.

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
          assert(exists m0 : nat, m0 |-F- B; L2 ++ [F ⊕ G]; DW F0).
          apply H2;eauto.
          eapply LPos3 in H;auto.

          simpl.
          rewrite Nat.sub_0_r.
          assumption.
          
          
          destruct H3.
          eexists.
          eapply tri_tensor with (M:= M0) (N:= L2 ++ [F ⊕ G]);auto. 
          rewrite H. auto.
          solve_permutation.
          eauto.
          eauto.
          
          
      +++ simpl in H0.
          intuition.
          
      
    ++ (* Oplus *)
      inversion HD1;subst.
      generalize(IH (S n0) ( le_n (S n0)));intros.
      destruct H.
      assert(exists m0 : nat, m0 |-F- B; M ++ [F ⊕ G]; DW F0).
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
      assert(exists m0 : nat, m0 |-F- B; M ++ [F ⊕ G]; DW G0).
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
      

Theorem InvPlus' : forall n, RInd n.
  intro n.
  induction n using strongind.
  + unfold RInd.
    split; [apply RUp0 | apply RDown0].
  + unfold RInd in *.
    split.
    apply InvPlusAux1. assumption.
    simpl.  rewrite Nat.sub_0_r.

    apply InvPlusAux2. assumption.
Qed.

End InvPlus.
Export InvPlus.

Theorem InvOplus1 : forall B L F G M n, n |-F- B;M ; UP (L ++ [F]) -> lexpPos M -> exists m, m|-F- B ; M ++ [F ⊕ G] ; UP L .
  intros.
  assert(HRn:  forall n, RUp n) by (apply InvPlus').
  generalize (HRn (n));intros.
  unfold RUp in H1.
  apply H1  ;auto.
Qed.

Theorem InvOplus2 : forall B L F G M n, n |-F- B;M ; UP (L ++ [G]) -> lexpPos M -> exists m, m|-F- B ; M ++ [F ⊕ G] ; UP L .
  intros.
  assert(HRn:  forall n, RUp n) by (apply InvPlus').
  generalize (HRn (n));intros.
  unfold RUp in H1.
  assert (exists m : nat, m |-F- B; M ++ [G ⊕ F]; UP L).
  apply H1  ;auto.
  destruct H2.
  apply OPlusComm in H2.
  eexists.
  eauto.
Qed.
  
