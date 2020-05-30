(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)


(** ** Invertibility Lemmas
These theorems prove, roughly, that the application of positive rules
can be exchanged.
 *)


(* Add LoadPath "../../".    *)
Require Export TriSystem. 
(*Require Export MSet.  *)
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

(** Automatization for multiset reasoning  *)
Ltac simpl_union_context := 
  match goal with
  | [ H : [?b] ++ ?M =mul= [?a] ++ ?L |- _ ] =>  
    apply DestructMSet in H; destruct H as [Hten1 | Hten2 ];
    [ destruct Hten1 as [HeqE HeqM] | destruct Hten2 as [L1 Hten2]; destruct Hten2]
  | [ H : [?b] ++ ?M =mul= ?a :: ?L |- _ ] =>  
    apply DestructMSet in H; destruct H as [Hten1 | Hten2 ];
    [ destruct Hten1 as [HeqE HeqM] | destruct Hten2 as [L1 Hten2]; destruct Hten2]
  | [ H : ?M ++ ?N =mul= [?a] ++ ?x |- _ ] =>
    assert ((exists L1, M =mul= [a] ++ L1) \/ (exists L2, N =mul= [a] ++ L2)) as Hten by refine (solsls _ _ H);
    destruct Hten as [Hten1 | Hten2];
    [ destruct Hten1 as [L1 HL1]; assert (x =mul= N ++ L1) by refine (solsls2 _ H HL1) |
      destruct Hten2 as [L2 HL2]; rewrite union_comm_app in H;
      assert (x =mul= M ++ L2) by refine (solsls2 _ H HL2); rewrite union_comm_app in H
    ]

  end.

Ltac contradiction_multiset := 
  repeat
    match goal with
    | [ H : [?l] ++ ?L =mul= [] |- _ ] => 
      apply DestructMulFalse in H; contradiction
    | [ H : ?L ++ [?l] =mul= [] |- _ ] => 
      rewrite union_comm_app in H
    | [ H : [] =mul= [?l] ++ ?L |- _ ] => 
      symmetry in H      
    | [ H : [] =mul= ?L ++ [?l] |- _ ] => 
      symmetry in H        
    end.



(** Invertibility of the Copy Rule *)
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


Set Implicit Arguments.
Hint Resolve  app_nil_r : core .

(** Invertibility of the OPlus Rule *)
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

(** Invertibility of the Tensor Rule *)
Module InvTensor.
  Lemma TensorComm : forall B M F G X n, n |-F- B ; M ++ [F ** G] ; X -> n |-F- B ; M ++ [G ** F] ; X.
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
        apply resolvers2 in H0; intuition. inversion H1.
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
        (* rewrite union_comm_app in H2 *)
        
        assert(H2': M0 ++ N =mul= [F ** G] ++ M) by ( rewrite <- H2;solve_permutation).
        clear H2.

        assert ((exists L1, M0 =mul= [F ** G] ++ L1) \/ (exists L2, N =mul= [F ** G] ++ L2)) as Hten.
        eapply solsls;eauto.

        destruct Hten as [Hten1 | Hten2].
        
        +++
          destruct Hten1 as [L1 HL1]. assert (M =mul= N ++ L1) by (
                                                                   eapply solsls2;eauto).
          rewrite union_comm_app in H1.
          eapply TriExchange with (M' := L1 ++ [F ** G] ) in H4; auto.
          apply H in H4; auto using Max.le_max_r. 
          eapply tri_tensor with (M:=L1 ++ [G ** F]) (N:=N);auto.
          rewrite H1. solve_permutation.
          rewrite HL1. auto.
          solve_permutation.
        +++
          destruct Hten2 as [L2 HL2].
          rewrite union_comm_app in H2'.
          assert (M =mul= M0 ++ L2).
          eapply solsls2 with (M:=N);eauto.
          eapply TriExchange with (M' := L2 ++ [F ** G]  ) in H3;auto.
          rewrite union_comm_app in H1.
          apply H in H3; auto using Max.le_max_l.
          eapply tri_tensor with (N:=L2 ++ [ G **F]) (M:=M0);auto.
          rewrite H1.
          solve_permutation.
          solve_permutation.
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
        eapply TriExchange with (M' :=  (M ++ [F0]) ++ [F ** G]) in H3;auto.
        apply H in H3;auto.
        apply tri_store;auto.
        eapply TriExchange with (M' :=  (M ++ [G ** F]) ++ [F0]) in H3;auto.
        apply H3.
        solve_permutation.
        solve_permutation.
      ++ (* decide *)
        (* M ++ [F ** G] =mul= [F0] ++ L' *)
        rewrite union_comm_app in H3.
        simpl_union_context.
        +++ subst.
            inversion H4;subst.
            eapply tri_dec1 with (F:= G ** F);auto.
            rewrite HeqM.
            rewrite union_comm_app in H5.
            assert(Init.Nat.max n0 m = Init.Nat.max m n0) by (apply Max.max_comm).
            rewrite H1.
            eapply tri_tensor with (m:=n0)(n:=m) (N:=M0) (M:=N);auto.
            rewrite H5. auto. solve_permutation.
            inversion H3.
        +++ rewrite meq_cons_append in H1.
            rewrite H1 in H4.
            apply H in H4;auto.
            rewrite H3.
            eapply tri_dec1 with (F:=F0);eauto.
      ++ (* decide B *)
        eapply tri_dec2;eauto.
  Qed.
  
  





  Definition RUp (nm:nat) := forall B L L' F G M M' n m, nm = plus n m -> 
                                                         lexpPos M -> lexpPos M' ->
                                                         n |-F- B;M ; UP ( L ++ [F]) -> m |-F- B;M' ; UP (L' ++ [G]) -> exists m, m|-F- B ; M ++ M' ++ [F ** G] ; UP (L ++ L').

  Definition RDown (nm:nat) := forall B  F G M M' n m H, nm = plus n m ->
                                                         lexpPos M -> lexpPos M' ->
                                                         PosOrPosAtom F -> 
                                                         n |-F- B;M ++ [F] ; DW H -> m |-F- B;M' ; UP ([G]) -> exists m, m|-F- B ; M ++ M' ++ [F ** G] ; DW H.


  Definition RInd (n:nat) := RUp n /\ RDown (n -1).


  Lemma RUp0 : RUp 0.
    unfold RUp.
    intros.
    assert(n = 0%nat) by omega.
    assert(m = 0%nat) by omega.
    subst.
    destruct L ; destruct L'.
    + inversion H2. inversion H3. subst.
      eexists.
      simpl.
      eapply tri_dec1 with (F:= ⊤ ** ⊤);eauto.
      eapply tri_tensor with (M:=M) (N:= M');auto;(
        eapply tri_rel;auto;
        eapply tri_top).
    + inversion H3. subst.
      simpl.
      eexists.
      eapply tri_top.
    + inversion H2. subst.
      simpl.
      eexists.
      eapply tri_top.
    + inversion H2. subst.
      simpl.
      eexists.
      eapply tri_top.
  Qed.




  Lemma RDown0 : RDown 0.
    unfold RDown.
    intros.
    assert(n = 0%nat) by omega.
    assert(m = 0%nat) by omega.
    subst.
    inversion H4. subst.
    inversion H5; subst.
    +
      destruct M. simpl in *. inversion H6.
      subst.
      inversion H3.
      simpl in H6.
      inversion H6;subst.
      apply EmptyMS in H8.
      contradiction.
      
      
    + apply EmptyMS in H6;contradiction.
    + apply EmptyMS in H6;contradiction.
  Qed.


  Theorem InvTensorAuxNilNilPosNeg:
    forall  n n1 n2 B M1 M2 F G ,
      (forall m : nat, m <= n -> RInd m) ->
      n1 |-F- B ; M1; UP [F] ->
                      n2 |-F- B ; M2; UP [G] ->
                                      PosOrPosAtom F -> NotPosOrPosAtom G ->
                                      S n = plus n1 n2 ->
                                      lexpPos M1 -> lexpPos M2 ->
                                      exists m : nat, m |-F- B; (M1 ++ M2) ++ [F ** G]; UP [].
    intros n n1 n2 B M1 M2 F G IH HD1 HD2 HF HG Hnm  HM1pos HM2pos.
    apply PosOrPosAtomAsync in HF as HF'.
    inversion HD1;subst;simpl in *; try(inversion HF').
    
    (* It must be a decition rule *)
    inversion H5;subst;auto.
    + (* DEC 1 *)
      rewrite union_comm_app in H1.
      apply DestructMSet in H1 as Heq.
      destruct Heq as [[Heq Heq'] | Heq];subst. 
      ++(* case F0 = F *)
        eexists.
        eapply tri_dec1 with (F:= F0 ** G) ;auto. 
        eapply tri_tensor with (N:=M1)(M:=M2);auto. solve_permutation.
        rewrite Heq'.  eassumption.
        eapply tri_rel;auto.
        apply NotPosOrPosAtomRelease;auto.
        eassumption.
        
      ++ destruct Heq as [M2'].
         destruct H3.
         
         assert (Hn: S (plus n1 n2) <= n ) by omega.
         generalize (IH (S (n1+ n2)) Hn) as IH';intros.
         destruct IH' as [HRU HRD].
         simpl in HRD.
         rewrite Nat.sub_0_r in HRD.
         assert(exists m : nat, m |-F- B; (M2' ++ M2 ) ++ [F ** G]; DW F0) .
         rewrite <- app_assoc.

         apply HRD with (m:=n2) (n:=n1);clear HRD; auto.
         rewrite meq_cons_app in H6. 
         apply LPos3 in H6;auto.
         assert(M2' ++ [F] =mul= L'). rewrite H3. solve_permutation.
         eapply TriExchange;eauto.
         inversion H7.
         assert(HeqMul: (M1 ++ M2) ++ [F ** G]  =mul= [F0] ++ (M2' ++ M2 ++ [F ** G])) by
             (rewrite H6; simpl; solve_permutation).
         eexists.
         eapply tri_dec1 with (F:=F0);eauto.
         rewrite app_assoc. eassumption.
    + (* Decision on B *)
      assert (Hn: S (plus n1 n2) <= n ) by omega.
      generalize (IH (S (n1+ n2)) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      simpl in HRD.
      rewrite Nat.sub_0_r in HRD.
      assert(exists m : nat, m |-F- B; (M1 ++ M2 ) ++ [F ** G]; DW F0) .
      rewrite <- app_assoc.
      apply HRD with (m:=n2) (n:=n1);clear HRD; auto.
      
      inversion H3.
      eexists. eapply tri_dec2 with (F:=F0)  ;eauto.
  Qed.

  

  
  
  Theorem InvTensorAuxNilNilPosPos:
    forall  n n1 n2 B M1 M2 F G ,
      (forall m : nat, m <= n -> RInd m) ->
      n1 |-F- B ; M1; UP [F] ->
                      n2 |-F- B ; M2; UP [G] ->
                                      PosOrPosAtom F -> PosOrPosAtom G ->
                                      S n = plus n1 n2 ->
                                      lexpPos M1 -> lexpPos M2 ->
                                      exists m : nat, m |-F- B; (M1 ++ M2) ++ [F ** G]; UP [].
    intros n n1 n2 B M1 M2 F G IH HD1 HD2 HF HG Hnm  HM1pos HM2pos.
    apply PosOrPosAtomAsync in HF as HF'.
    apply PosOrPosAtomAsync in HG as HG'.
    inversion HD1;subst;simpl in *; try(inversion HF').
    inversion HD2;subst;simpl in *; try(inversion HG').
    (* clear HD1. clear HD2. *)
    
    (* It must be a decition rule *)
    inversion H5;inversion H8;subst;auto.
    + (* DEC 1 / DEC 1*)
      rewrite union_comm_app in H2. rewrite union_comm_app in H12.
      apply DestructMSet in H2 as Heq1.
      apply DestructMSet in H12 as Heq2.
      destruct Heq1 as [[Heq1 Heq1'] | Heq1]; destruct Heq2 as [[Heq2 Heq2'] | Heq2]; subst.
      ++(* case F0 = F F1 = G*)
        eexists.
        eapply tri_dec1 with (F:= F0 ** F1) ;auto.
        rewrite app_nil_r.
        eapply tri_tensor with (N:=M1)(M:=M2) ;eauto.
        rewrite Heq1'. eauto.
        rewrite Heq2'.
        eauto.
      ++ (* case F0 = F, G<> F1 *)
        destruct Heq2 as [M2']. destruct H6.
        assert (Hn: S (S (S(n2 + n3))) <= n ) by omega.
        generalize (IH (S (S (S (n2+ n3)))) Hn) as IH';intros.
        destruct IH' as [HRU HRD].
        simpl in HRD.
        (* rewrite Nat.sub_0_r in HRD. *)
        
        assert(exists m : nat, m |-F- B; M2' ++ M1  ++ [G ** F0]; DW F1) .

        apply HRD with (m:=S (S n2)) (n:=  n3) ;clear HRD; auto.
        omega.
        rewrite meq_cons_app in H9. 
        apply LPos3 in H9;auto.
        rewrite meq_cons_append in H6. rewrite H6  in H13. auto.
        
        destruct H10.
        assert(HeqMul: (M1 ++ M2) ++ [F0 ** G]  =mul= [F1] ++ (M1 ++ M2'  ++ [F0 ** G]))
          by (rewrite H9; solve_permutation).
        eexists. eapply tri_dec1 with (F:=F1);eauto.
        rewrite app_assoc.
        apply TensorComm ;auto.
        eapply TriExchange;eauto.
      ++ (* case F0 <> F , F1 = G *)
        destruct Heq1 as [M1']. destruct H6.
        assert (Hn: S (S (S(n2 + n3))) <= n ) by omega.
        generalize (IH (S (S (S (n2+ n3)))) Hn) as IH';intros.
        destruct IH' as [HRU HRD].
        simpl in HRD.
        (* rewrite Nat.sub_0_r in HRD. *)
        
        assert(exists m : nat, m |-F- B; M1' ++ M2  ++ [F ** F1]; DW F0) .
        apply HRD with (m:=S (S n3)) (n:=  n2);clear HRD; auto.
        omega.
        rewrite meq_cons_app in H9. 
        apply LPos3 in H9;auto.
        rewrite meq_cons_append in H6. rewrite <- H6. eauto.
        destruct H10.
        assert(HeqMul: (M1 ++ M2) ++ [F ** F1]  =mul= [F0] ++ (M1' ++ M2  ++ [F ** F1])) by(
                                                                                             rewrite H9; solve_permutation).
        eexists. eapply tri_dec1 with (F:=F0);eauto.
        
      ++ (* case both are different *)
        destruct Heq1 as [M1']. destruct H6.
        destruct Heq2 as [M2']. destruct H10.
        
        assert (Hn: S (S (S(n2 + n3))) <= n ) by omega.
        generalize (IH (S (S (S (n2+ n3)))) Hn) as IH';intros.
        destruct IH' as [HRU HRD].
        simpl in HRD.
        (* rewrite Nat.sub_0_r in HRD. *)

        assert(exists m : nat, m |-F- B; M1' ++ M2  ++ [F ** G]; DW F0) .
        apply HRD with (m:=S (S n3)) (n:=  n2);clear HRD; auto.
        omega.
        rewrite meq_cons_app in H9. 
        apply LPos3 in H9 ;auto.
        rewrite meq_cons_append in H6. rewrite <- H6. eauto.
        destruct H15.
        assert(HeqMul: (M1 ++ M2) ++ [F ** G]  =mul= [F0] ++ (M1' ++ M2  ++ [F ** G])) by(
                                                                                           rewrite H9; solve_permutation).
        eexists. eapply tri_dec1 with (F:=F0);eauto.
    + (* DEC 2 / DEC 1*)
      assert (Hn: S (S (S(n2 + n3))) <= n ) by omega.
      generalize (IH (S (S (S (n2+ n3)))) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      simpl in HRD.
      
      assert(exists m : nat, m |-F- B; M2 ++ M1  ++ [G ** F]; DW F1) .
      apply HRD with (m:=S (S n2)) (n:=  n3);clear HRD; auto.
      omega.
      destruct H6.
      eexists.
      apply TensorComm;auto.
      eapply tri_dec2 with (F:=F1);eauto.
      eapply TriExchange;eauto.
    + (* DEC 1 / DEC 2*)
      assert (Hn: S (S (S(n2 + n3))) <= n ) by omega.
      generalize (IH (S (S (S (n2+ n3)))) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      simpl in HRD.
      
      assert(exists m : nat, m |-F- B; M1 ++ M2  ++ [F ** G]; DW F0) .
      apply HRD with (m:=S (S n3)) (n:=  n2);clear HRD; auto.
      omega.
      destruct H6.
      eexists.
      rewrite <- app_assoc.
      eapply tri_dec2 with (F:=F0);eauto.

    + (* DEC 2 / DEC 2*)
      assert (Hn: S (S (S(n2 + n3))) <= n ) by omega.
      generalize (IH (S (S (S (n2+ n3)))) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      simpl in HRD.
      
      assert(exists m : nat, m |-F- B; M1 ++ M2  ++ [F ** G]; DW F0) .
      apply HRD with (m:=S (S n3)) (n:=  n2);clear HRD; auto.
      omega.
      destruct H6.
      eexists.
      rewrite <- app_assoc.
      eapply tri_dec2 with (F:=F0);eauto.
  Qed.


  Lemma InvTensorAux1' : forall n n1 n2 B M1 M2 L1 l L2 F G,
      n1 |-F- B; M1; UP (L1 ++ [F]) ->
                     n2 |-F- B; M2; UP ((l :: L2) ++ [G])->
                                    (forall m : nat, m <= n -> RInd m) ->
                                    S n = plus n1 n2 ->
                                    lexpPos M1 ->
                                    lexpPos M2 ->
                                    exists m : nat, m |-F- B; (M1 ++ M2) ++ [F ** G]; UP (L1 ++ l :: L2).

    intros n n1 n2 B M1 M2 L1 l L2 F G HD1 HD2 IH Hnm HM1pos HM2pos.
    simpl in *.
    inversion HD2;subst.
    ++ (* top *)
      apply EquivAuxTop.
    ++ (* bottom *)
      assert (Hn: (plus n0 n1) <= n ) by omega.
      generalize (IH (plus n0 n1) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      clear HRD.
      unfold RUp in HRU .
      assert(Hih : exists m : nat, m |-F- B; M1 ++ M2  ++ [F ** G]; UP (L1 ++ L2)) .
      apply HRU with (n:=n1) (m:=n0);auto.
      omega.
      destruct Hih.
      rewrite <- app_assoc.
      eapply EquivAuxBot ;eassumption.
    ++ (* par *)
      assert (Hn: (plus n0 n1) <= n ) by omega.
      generalize (IH (plus n0 n1) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      clear HRD.
      unfold RUp in HRU .
      assert(Hih : exists m : nat, m |-F- B; M1 ++ M2  ++ [F ** G]; UP (L1 ++ (F0 :: G0 :: L2))) .
      apply HRU with (n:=n1) (m:=n0);auto.
      omega.
      destruct Hih.
      rewrite <- app_assoc.
      eapply EquivAuxPar with(F:=F0) (G:=G0); eassumption.
    ++ (* with *)
      assert (Hn: (plus n0 n1) <= n ) by (
                                       rewrite <- Nat.add_succ_comm in Hnm; inversion Hnm;
                                       rewrite plus_comm;
                                       apply plus_le_compat_l ;apply  Max.le_max_l).

      
      assert (Hn': (plus m n1) <= n ) by (
                                       rewrite <- Nat.add_succ_comm in Hnm; inversion Hnm;
                                       rewrite plus_comm;
                                       apply plus_le_compat_l ;apply  Max.le_max_r).
      
      generalize (IH (plus n0 n1) Hn) as IH';intros.
      generalize (IH (plus m n1) Hn') as IH'';intros.
      
      destruct IH' as [HRU HRD];clear HRD.
      destruct IH'' as [HRU' HRD'];clear HRD'.
      unfold RUp in HRU .
      unfold RUp in HRU'.
      
      
      assert(Hih : exists m : nat, m |-F- B; M1 ++ M2  ++ [F ** G]; UP (L1 ++ (F0  :: L2))) .
      apply HRU with (n:=n1) (m:=n0);auto.
      omega. 

      assert(Hih' : exists m : nat, m |-F- B; M1 ++ M2  ++ [F ** G]; UP (L1 ++ (G0  :: L2))) .
      apply HRU' with (n:=n1) (m0:=m);auto.
      omega.
      clear HRU. clear HRU'.
      
      destruct Hih.
      destruct Hih'.
      rewrite <- app_assoc.
      eapply EquivAuxWith;eassumption.
      
    ++ (* quest *)
      assert (Hn: (plus n0 n1) <= n ) by omega.
      generalize (IH (plus n0 n1) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      clear HRD.
      unfold RUp in HRU .
      assert(Hih : exists m : nat, m |-F- B ++ [F0] ; M1 ++ M2  ++ [F ** G]; UP (L1 ++  L2)) .
      apply HRU with (n:=n1) (m:=n0);auto.
      omega.
      eapply TriWeakening;eauto.
      
      
      destruct Hih.
      rewrite <- app_assoc.
      eapply EquivAuxQuest; eassumption.
    ++ (* Store *)
      assert (Hn: (plus n0 n1) <= n ) by omega.
      generalize (IH (plus n0 n1) Hn) as IH';intros.
      destruct IH' as [HRU HRD].
      clear HRD.
      unfold RUp in HRU .
      assert(Hih : exists m : nat, m |-F- B  ; M1 ++ (M2 ++ [l])  ++ [F ** G]; UP (L1 ++  L2)) .
      apply HRU with (n:=n1) (m:=n0);auto.
      omega.
      assert (lexpPos( [l] ++ M2)).
      apply lexpPosUnion;auto. firstorder.
      apply LPos1 with (L:= [l] ++ M2);auto. solve_permutation.
      
      destruct Hih.
      eapply EquivAuxSync with (F:=l);eauto.
      eapply TriExchange with (M':= ((M1 ++ M2) ++ [F ** G]) ++ [l])in H;auto.
      eassumption.
      solve_permutation.

  Qed.
  

  Theorem InvTensorAux1: forall  n , (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    intros n IH.
    unfold RUp.  intros B L1 L2 F G M1 M2 n1 n2 Hnm HM1pos HM2pos HD1 HD2.
    destruct L1; destruct L2.
    + (* L1 and L2 are Empty *)
      simpl in *.
      assert (HF: NotPosOrPosAtom F \/ PosOrPosAtom F) by (apply DecPosOrPosAtom).
      assert (HG: NotPosOrPosAtom G \/ PosOrPosAtom G) by (apply DecPosOrPosAtom).

      destruct HG as [HG | HG] ; destruct HF as [HF | HF].
      ++
        (* F and G are NotPosOrPosAtom *)
        eexists.
        eapply tri_dec1 with (F := F ** G) ;eauto.
        eapply tri_tensor with (F:=F) (M:=M2) (N:=M1);auto. solve_permutation.
        eapply tri_rel; auto using NotPosOrPosAtomRelease;eassumption.
        eapply tri_rel; auto using NotPosOrPosAtomRelease;eassumption.
      ++ (* F is positive and G is Not *)
        rewrite app_assoc.
        eapply InvTensorAuxNilNilPosNeg;eauto.
      ++ (* G is positive and F is Not *)
        assert(exists m : nat, m |-F- B; (M2 ++ M1) ++ [G ** F]; UP []).
        eapply InvTensorAuxNilNilPosNeg with(F:=G) (G:=F) (n1:=n2) (n2:=n1) (M1:=M2)(M2:=M1);eauto. omega.
        destruct H.
        eexists.
        rewrite app_assoc.
        apply TensorComm.
        eapply TriExchange with (M:= (M2 ++ M1) ++ [G ** F]);eauto.
        
      ++ (* Both are positive *)
        rewrite app_assoc.
        eapply InvTensorAuxNilNilPosPos;eauto.

    + (* L2 is not empty *)
      rewrite  app_assoc.
      eapply InvTensorAux1';eauto.

    + (* L2 empty and L1 is not empty *)
      assert ((l :: L1) ++ [] = [] ++ (l :: L1) ) by  auto using app_nil_r.
      rewrite H.
      assert(exists m : nat,m |-F- B; (M2 ++ M1) ++ [G ** F]; UP ([] ++ l :: L1)).
      eapply InvTensorAux1' with (F:=G) (G:=F);eauto.
      omega.
      destruct H0.
      apply TensorComm in H0.
      eexists.
      eapply TriExchange;eauto.
      
    + (* L1 and L2 are not empty *)
      rewrite app_assoc.
      eapply InvTensorAux1';eauto.
  Qed.       

  



  
  

  Theorem InvTensorAux2: forall  n , (forall m : nat, m <= n -> RInd m) -> RDown (n).

    intros n IH.
    unfold RDown.  intros B F G M M' n1 n2 H Hnm HM1pos HM2pos HPosF  HD1 HD2.
    elim (DecPosOrPosAtom H);intro HHpos.
    + (* H is not positive or atom *)
      inversion HHpos;subst.
      ++ (* Neg Atom *)
        inversion HD1;subst.
        apply UpExtension in H4.
        destruct H4 as [n'  [IHn IHd]].
        inversion IHd;subst.
        assert(Hnm: plus n0 n2 <= plus (S n) n2 ) by omega.
        generalize(IH (plus n0 n2) Hnm);intros.
        
        destruct H.
        unfold RUp in H.
        assert( exists m0 : nat, m0 |-F- B; (M ++ [v ⁻]) ++ M' ++ [F ** G]; UP ([] ++ [])).
        apply H with (m:=n2) (n:= n0);auto.
        apply LPos1 with (L:= [v ⁻] ++ M);eauto. constructor;auto.
        destruct H2.
        eexists.
        eapply tri_rel;auto. eapply tri_store;auto.
        simpl in H2.
        eapply TriExchange.  apply H2. auto. solve_permutation.
        eapply LPos1;auto. firstorder.
        
        apply LPos1 with  (L:=[F] ++ M);auto.
        simpl. intuition. solve_permutation.
        constructor;auto.
        apply PosOrPosAtomAsync;auto.
      ++ (* top *)
        eexists.
        eapply tri_rel;auto. eapply tri_top;auto.
      ++ (* bot *)
        inversion HD1;subst.
        apply UpExtension in H4.
        destruct H4 as [n'  [IHn IHd]].
        simpl in IHd.
        inversion IHd;subst.
        
        assert(Hnm: plus n0 n2 <= plus (S n) n2 ) by omega.
        generalize(IH (plus n0 n2) Hnm);intros.
        
        destruct H.
        
        assert( exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; UP ([] ++ [])).
        apply H with (m:=n2) (n:= n0);auto.

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
        
        assert(Hnm: plus n0 n2 <= plus (S n) n2 ) by omega.
        generalize(IH (plus n0 n2) Hnm);intros.
        
        destruct H.
        
        assert( exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; UP ([F0 ; G0] ++ [])).
        apply H with (m:=n2) (n:= n0);auto.
        
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
        
        
        assert(Hnm0: (Init.Nat.max n0  m) + n2 <= plus (S n) n2 ) by omega.
        assert(Hnm1:  plus n0 n2 <= plus (S n) n2 ) by (
                                                apply plus_le_reg_r in Hnm0;
                                                apply plus_le_compat_r;
                                                assert (n0 <= Init.Nat.max n0 m) by apply Max.le_max_l;
                                                omega).
        
        
        assert(Hnm2:  plus m n2 <= plus (S n) n2 ) by (
                                               apply plus_le_reg_r in Hnm0;
                                               apply plus_le_compat_r;
                                               assert (m <= Init.Nat.max n0 m) by apply Max.le_max_r;
                                               omega).

        
        
        generalize(IH (plus n0 n2) Hnm1);intros.
        generalize(IH (plus m n2) Hnm2);intros.
        
        destruct H.
        destruct H1.
        
        assert( exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; UP ([F0] ++ []))
          by ( apply H with (n:=n0) (m:=n2);auto).

        assert( exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; UP ([G0] ++ []))
          by (apply H1  with (n:=m) (m0:=n2);auto).
        

        destruct H4. simpl in H4.
        destruct H6. simpl in H6.
        eexists.
        eapply tri_rel;auto. eapply tri_with;auto; eassumption.
        simpl in H5.
        intuition.
        apply LPos1 with (L:= [F] ++ M);eauto.
        constructor;auto using PosOrPosAtomAsync.
        
      ++ (* Quest *)
        inversion HD1;subst.
        apply UpExtension in H4.
        destruct H4 as [n'  [IHn IHd]].
        simpl in IHd.
        inversion IHd;subst.
        
        assert(Hnm: plus n0 n2 <= plus (S n) n2 ) by omega.
        generalize(IH (plus n0 n2) Hnm);intros.
        
        destruct H.
        
        assert( exists m0 : nat, m0 |-F- B ++ [F0]; M ++ M' ++ [F ** G]; UP ([] ++ [])).
        apply H with (m:=n2) (n:= n0);auto.
        eapply TriWeakening;eauto.
        

        destruct H2. simpl in H2.
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
        (*  Bem, não é multiset mas vamos tentar *)
        apply eq_then_meq in H2.
        symmetry in H2.
        rewrite union_comm_app in H2.
        apply resolvers2 in H2.
        destruct H2.
        subst.
        inversion HPosF.

        apply EmptyMS in H. contradiction.
        
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
        
        assert(H2': M0 ++ N =mul= [F] ++ M)by ( rewrite <- H1;solve_permutation).
        clear H1.

        assert ((exists L1, M0 =mul= [F] ++ L1) \/ (exists L2, N =mul= [F] ++ L2)) as Hten.
        eapply solsls;eauto.
        destruct Hten as [Hten1 | Hten2].
        +++
          destruct Hten1 as [L1 HL1]. assert (M =mul= N ++ L1) by (
                                                                   eapply solsls2;eauto).
          rewrite union_comm_app in HL1.
          eapply TriExchange with (M' := L1 ++ [F]) in H6;auto .
          assert(Hn1: (S m) + n2 <= S(Init.Nat.max n m) + n2) by(
                                                                  apply le_n_S;apply plus_le_compat;auto).
          generalize(IH (plus (S m) n2) Hn1);intros.
          destruct H0.
          assert(exists m0 : nat, m0 |-F- B; L1 ++ M' ++ [F ** G]; DW G0).
          apply H1 with   (n :=m) (m0:=n2) ;eauto. omega.
          eapply LPos2 in HM1pos;eauto.
          
          destruct H2.
          (*rewrite H in H1. *)
          
          assert(exists m0 : nat, m0 |-F- B; L1 ++ N ++ M' ++ [F ** G] ;  DW (F0 ** G0)).
          eexists.
          eapply tri_tensor with (N:= N) (M:= L1 ++ M' ++ [F ** G]);eauto.
          destruct H3.
          eapply TriExchange with (M' := (M ++ M') ++ [F ** G])in H3;auto.
          eexists.
          rewrite app_assoc.
          eassumption.
          rewrite H.
          solve_permutation.
          
        +++
          destruct Hten2 as [L2 HL2].
          rewrite union_comm_app in H2'.
          assert (M =mul= M0 ++ L2).
          eapply solsls2 with (M:=N);eauto.
          
          rewrite union_comm_app in HL2.
          eapply TriExchange with (M' := L2 ++ [F]) in H5;auto .
          assert(Hn1: (S n) + n2 <= S(Init.Nat.max n m) + n2) by(
                                                                  apply le_n_S;apply plus_le_compat;auto).
          generalize(IH (plus (S n) n2) Hn1);intros.
          destruct H0.
          assert(exists m0 : nat, m0 |-F- B; L2 ++ M' ++ [F ** G]; DW F0).
          apply H1 with   (n0 :=n) (m:=n2) ;eauto. omega.
          eapply LPos2 in HM1pos;eauto.
          
          destruct H2.
          (* rewrite HL2 in H1. *)
          
          assert(exists m0 : nat, m0 |-F- B; M0 ++ L2 ++ M' ++ [F ** G] ;  DW (F0 ** G0)).
          eexists.
          eapply tri_tensor with (M:= M0) (N:= L2 ++ M' ++ [F ** G]);eauto.
          
          destruct H3.
          eapply TriExchange with (M' := (M ++ M') ++ [F ** G])in H3;auto.
          eexists.
          rewrite app_assoc.
          eassumption.
          rewrite H.
          solve_permutation.
        +++ simpl in H0.
            intuition.
            
            
      ++ (* Oplus *)
        inversion HD1;subst.
        generalize(IH (plus (S n) n2) ( le_n (plus (S n) n2)));intros.
        destruct H.
        assert(exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; DW F0).
        apply H0 with (n0 :=n) (m:=n2);auto.
        omega.
        destruct H1.
        eexists.
        eapply tri_plus1;eauto.

        (* Symmetric for G0 *)
        generalize(IH (plus (S n) n2) ( le_n (plus (S n) n2)));intros.
        destruct H.
        assert(exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; DW G0).
        apply H0 with (n0 :=n) (m:=n2);auto.
        omega.
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
  

  Theorem InvTensor' : forall n, RInd n.
    intro n.
    induction n using strongind.
    + unfold RInd.
      split; [apply RUp0 | apply RDown0].
    + unfold RInd in *.
      split.
      apply InvTensorAux1. assumption.
      simpl.  rewrite Nat.sub_0_r.

      apply InvTensorAux2. assumption.
  Qed.

End InvTensor.    
Export InvTensor.



Theorem InvTensor : forall B L L' F G M M' n m, lexpPos M -> lexpPos M' -> n |-F- B;M ; UP ( L ++ [F]) -> m |-F- B;M' ; UP (L' ++ [G]) -> exists m, m|-F- B ; M ++ M' ++ [F ** G] ; UP (L ++ L').
  intros.
  assert(HRn:  forall n, RUp n) by (apply InvTensor').
  generalize (HRn (plus n m));intros.
  unfold RUp in H3.
  apply H3  with (n0:=n) (m0:=m) ;auto.
Qed.
