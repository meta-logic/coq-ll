(* Add LoadPath "../../".   *)
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
  
  





Definition RUp (nm:nat) := forall B L L' F G M M' n m, nm = n + m -> 
                                                       lexpPos M -> lexpPos M' ->
                                                       n |-F- B;M ; UP ( L ++ [F]) -> m |-F- B;M' ; UP (L' ++ [G]) -> exists m, m|-F- B ; M ++ M' ++ [F ** G] ; UP (L ++ L').

Definition RDown (nm:nat) := forall B  F G M M' n m H, nm = n + m ->
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
                                    S n = n1 + n2 ->
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
       
       assert (Hn: S (n1 + n2) <= n ) by omega.
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
    assert (Hn: S (n1 + n2) <= n ) by omega.
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
                                    S n = n1 + n2 ->
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
 S n = n1 + n2 ->
 lexpPos M1 ->
 lexpPos M2 ->
 exists m : nat, m |-F- B; (M1 ++ M2) ++ [F ** G]; UP (L1 ++ l :: L2).

  intros n n1 n2 B M1 M2 L1 l L2 F G HD1 HD2 IH Hnm HM1pos HM2pos.
    simpl in *.
    inversion HD2;subst.
    ++ (* top *)
      apply EquivAuxTop.
    ++ (* bottom *)
      assert (Hn: (n0 + n1) <= n ) by omega.
      generalize (IH (n0 + n1) Hn) as IH';intros.
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
      assert (Hn: (n0 + n1) <= n ) by omega.
      generalize (IH (n0 + n1) Hn) as IH';intros.
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
      assert (Hn: (n0 + n1) <= n ) by (
                                       rewrite <- Nat.add_succ_comm in Hnm; inversion Hnm;
                                       rewrite plus_comm;
                                       apply plus_le_compat_l ;apply  Max.le_max_l).

      
      assert (Hn': (m + n1) <= n ) by (
                                       rewrite <- Nat.add_succ_comm in Hnm; inversion Hnm;
                                       rewrite plus_comm;
                                       apply plus_le_compat_l ;apply  Max.le_max_r).
      
      generalize (IH (n0 + n1) Hn) as IH';intros.
      generalize (IH (m + n1) Hn') as IH'';intros.
      
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
      assert (Hn: (n0 + n1) <= n ) by omega.
      generalize (IH (n0 + n1) Hn) as IH';intros.
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
      assert (Hn: (n0 + n1) <= n ) by omega.
      generalize (IH (n0 + n1) Hn) as IH';intros.
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
      assert(Hnm: n0 + n2 <= S n + n2 ) by omega.
      generalize(IH (n0 + n2) Hnm);intros.
    
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
      
      assert(Hnm: n0 + n2 <= S n + n2 ) by omega.
      generalize(IH (n0 + n2) Hnm);intros.
    
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
      
      assert(Hnm: n0 + n2 <= S n + n2 ) by omega.
      generalize(IH (n0 + n2) Hnm);intros.
    
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
      
      
      assert(Hnm0: (Init.Nat.max n0  m) + n2 <= S n + n2 ) by omega.
      assert(Hnm1:  n0 + n2 <= S n + n2 ) by (
                                              apply plus_le_reg_r in Hnm0;
                                              apply plus_le_compat_r;
                                              assert (n0 <= Init.Nat.max n0 m) by apply Max.le_max_l;
                                              omega).
      
      
      assert(Hnm2:  m + n2 <= S n + n2 ) by (
                                             apply plus_le_reg_r in Hnm0;
                                             apply plus_le_compat_r;
                                             assert (m <= Init.Nat.max n0 m) by apply Max.le_max_r;
                                             omega).

      
      
      generalize(IH (n0 + n2) Hnm1);intros.
      generalize(IH (m + n2) Hnm2);intros.
    
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
      
      assert(Hnm: n0 + n2 <= S n + n2 ) by omega.
      generalize(IH (n0 + n2) Hnm);intros.
    
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
          generalize(IH (S m + n2) Hn1);intros.
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
          generalize(IH (S n + n2) Hn1);intros.
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
      generalize(IH (S n + n2) ( le_n (S n + n2)));intros.
      destruct H.
      assert(exists m0 : nat, m0 |-F- B; M ++ M' ++ [F ** G]; DW F0).
      apply H0 with (n0 :=n) (m:=n2);auto.
      omega.
      destruct H1.
      eexists.
      eapply tri_plus1;eauto.

      (* Symmetric for G0 *)
      generalize(IH (S n + n2) ( le_n (S n + n2)));intros.
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
  generalize (HRn (n+m));intros.
  unfold RUp in H3.
  apply H3  with (n0:=n) (m0:=m) ;auto.
Qed.
