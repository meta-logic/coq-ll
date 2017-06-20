(* This file is part of the Linear Logic  formalization in Coq: https://github.com/brunofx86/LL *)

(** ** Cut Elimination

Proof of cut-elimination and the consistency of LL as a corollary.

 *)

Require Export CutCases.
Require Export myTactics.
Set Implicit Arguments.

Lemma ap_cut_free B L M1 M2 v :
  0%nat = lexp_weight (v ⁺) ->
  L =mul= M1 ++ M2 ->
  0 |~> 0; B; v ⁻ :: M2 ->
              0 |~> 0; B; v ⁺ :: M1 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros Hw P Hn2 Hn1.
  inversion Hn1; inversion Hn2; subst;
    try simpl_cases0;
    try broken; try solve_cont;
      try simpl_cases2;
      try top_commutes; try simpl_cases0.
  
  destruct (eq_dec (A0 ⁻) (A1 ⁻)). 
  apply atp_eq in e.
  apply atn_eq in e0.
  rewrite e in *;
    rewrite e0 in *.
  simpl in H0. 
  do 2 simpl_cases4.
  rewrite union_comm_app in P.
  rewrite H0, H in P.
  eexists.
  refine (sig3_init _ P).
  apply atp_eq in e.
  rewrite e in *.
  simpl in H0.
  solve_cont.
Qed.
Arguments ap_cut_free [B L M1 M2 v].

Lemma zt_cut_free B L M1 M2 :
  0%nat = lexp_weight (⊤) ->
  L =mul= M1 ++ M2 ->
  0 |~> 0; B; 0 :: M2 ->
              0 |~> 0; B; ⊤ :: M1 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros Hw P Hn2 Hn1.
  inversion Hn1; subst.
  apply resolvers in H; firstorder; inversion H.
  apply resolvers2 in H; firstorder; inversion H.
  simpl_cases4. 
  
  inversion Hn2; subst.
  apply resolvers in H0; firstorder; inversion H0.
  apply resolvers2 in H0; firstorder; inversion H0.
  simpl_cases2. top_commutes.
Qed.
Arguments zt_cut_free [B L M1 M2].

Lemma bo_cut_free B L M1 M2 :
  0%nat = lexp_weight (⊥) ->
  L =mul= M1 ++ M2 ->
  0 |~> 0; B; 1 :: M2 ->
              0 |~> 0; B; ⊥ :: M1 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros Hw P Hn2 Hn1.
  inversion Hn1; subst.
  apply resolvers in H; firstorder; inversion H.
  apply resolvers2 in H; firstorder; inversion H.
  simpl_cases2. top_commutes. 
Qed.
Arguments bo_cut_free [B L M1 M2].

Theorem cut_aux B L M1 M2 F n1 n2 : 
  0%nat = lexp_weight F -> 0%nat = n1 + n2 -> L =mul= M1 ++ M2 ->
  n1 |~> 0 ; B ; F :: M1 -> n2 |~> 0 ; B ; F° :: M2 -> 
                                           exists m, m |~> 0 ; B ; L.
Proof.
  intros Hw Hh P Hn1 Hn2.    
  simpl_bases; (* n1 = n2 = 0 *)
    clear Hh.
  
  destruct F; simpl ((_)°)in *; try inversion Hw.
  -
    refine (ap_cut_free Hw P Hn2 Hn1).
  - 
    rewrite union_comm_app in P.
    refine (ap_cut_free Hw P Hn1 Hn2).
  - 
    refine (zt_cut_free Hw P Hn2 Hn1).
  -
    refine (bo_cut_free Hw P Hn2 Hn1).
  -
    rewrite union_comm_app in P.      
    refine (zt_cut_free Hw P Hn1 Hn2).
  -
    rewrite union_comm_app in P.      
    refine (bo_cut_free Hw P Hn1 Hn2).
Qed.     
Arguments cut_aux [B L M1 M2 F n1 n2].

Lemma tp_cut_free B L M1 M2 F1 F2 :
  L =mul= M1 ++ M2 ->
  0 |~> 0; B; (F1 ** F2) :: M1 ->
              0 |~> 0; B; (F1° $ F2°) :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros P Hn1 Hn2.
  inversion Hn1; subst.
  apply resolvers in H; firstorder; inversion H.
  apply resolvers2 in H; firstorder; inversion H.
  simpl_cases2.
  top_commutes. 
Qed.
Arguments tp_cut_free [B L M1 M2 F1 F2].

Lemma wp_cut_free B L M1 M2 F1 F2 :
  L =mul= M1 ++ M2 ->
  0 |~> 0; B; (F1 ⊕ F2) :: M1 ->
              0 |~> 0; B; (F1° & F2°) :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros P Hn1 Hn2.
  inversion Hn1; subst.
  apply resolvers in H; firstorder; inversion H.
  apply resolvers2 in H; firstorder; inversion H.
  simpl_cases2. top_commutes.
Qed.
Arguments wp_cut_free [B L M1 M2 F1 F2].

Lemma bq_cut_free B L M1 M2 F :
  L =mul= M1 ++ M2 ->
  0 |~> 0; B; (! F) :: M1 ->
              0 |~> 0; B; (? F°) :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros P Hn1 Hn2.
  inversion Hn1; subst.
  apply resolvers in H; firstorder; inversion H.
  apply resolvers2 in H; firstorder; inversion H.
  simpl_cases2. top_commutes.
Qed.
Arguments bq_cut_free [B L M1 M2 F].

Theorem cut_aux' B L M1 M2 F w : 
  S w = lexp_weight F -> L =mul= M1 ++ M2 ->
  0 |~> 0 ; B ; F :: M1 -> 0 |~> 0 ; B ; F° :: M2 -> 
                                         exists m, m |~> 0 ; B ; L.
Proof.
  intros Hw P Hn1 Hn2.

  destruct F; simpl ((_)°)in *; try inversion Hw.
  -
    refine (tp_cut_free P Hn1 Hn2).
  -
    rewrite union_comm_app in P.
    refine (tp_cut_free P Hn2 _).
    rewrite <- !ng_involutive; auto.
  -
    refine (wp_cut_free P Hn1 Hn2). 
  - 
    rewrite union_comm_app in P.
    refine (wp_cut_free P Hn2 _).
    rewrite <- !ng_involutive; auto.
  - 
    refine (bq_cut_free P Hn1 Hn2).  
  -
    rewrite union_comm_app in P.
    refine (bq_cut_free P Hn2 _). 
    rewrite <- !ng_involutive; auto.
Qed.
Arguments cut_aux' [B L M1 M2 F w].

Theorem ccut_aux  B L M1 M2 F w :
  S w = lexp_weight (! F) -> L =mul= M1 ++ M2 ->
  0 |~> 0 ; B ; ! F :: M1 -> 0 |~> 0 ; F° :: B ; M2 -> 
                                                 exists m, m |~> 0 ; B ; L.
Proof.
  intros Hw P Hn1 Hn2.
  inversion Hn1; subst;
    [ apply resolvers in H; firstorder; inversion H |
      apply resolvers2 in H; firstorder; inversion H |
      simpl_cases2; top_commutes].
Qed.      
Arguments ccut_aux [B L M1 M2 F w].

Lemma cut_elimination_base: forall n B L,   
    n |~> 1 ; B ; L -> exists m, m |~> 0 ; B ; L.
Proof.
  intros.
  revert dependent B.
  revert dependent L.
  induction n using strongind; intros.
  - inversion H.
  - inversion H0; subst. 
    + assert (exists m, m |~> 0; B; M) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_bot _ Ht); eauto.   
    + assert (exists m, m |~> 0; B; F :: G :: M) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_par _ Ht); resolve_rewrite.  
    + apply Nat.eq_add_1 in H2.
      destruct H2; destruct H1; subst.
      assert (exists m, m |~> 0; B; F :: M) as Hyp.
      refine (H _ _ _ _ H4); resolve_max.
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_tensor _ Ht H5); resolve_rewrite. 
      assert (exists m, m |~> 0; B; G :: N) as Hyp.
      refine (H _ _ _ _ H5); resolve_max.
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_tensor _ H4 Ht); resolve_rewrite.       
    + assert (exists m, m |~> 0; B; F :: M) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_plus1 _ Ht); resolve_rewrite.  
    + assert (exists m, m |~> 0; B; G :: M) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_plus2 _ Ht); resolve_rewrite.  
    + apply Nat.eq_add_1 in H2.
      destruct H2; destruct H1; subst.
      assert (exists m, m |~> 0; B; F :: M) as Hyp.
      refine (H _ _ _ _ H4); resolve_max.
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_with _ Ht H5); resolve_rewrite. 
      assert (exists m, m |~> 0; B; G :: M) as Hyp.
      refine (H _ _ _ _ H5); resolve_max.
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_with _ H4 Ht); resolve_rewrite.   
    + rewrite H3 in H4.
      assert (exists m, m |~> 0; B; F:: L) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_copy _ _ Ht); auto.
    + assert (exists m, m |~> 0; F:: B; M) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_quest _ Ht); auto.
    + assert (exists m, m |~> 0; B; [F]) as Hyp by solve [eapply H; auto].
      destruct Hyp as [t Ht].
      eexists;
        refine (sig3_bang _ Ht); auto.
    + (* caso CUT *)
      clear H0. clear H.
      revert dependent B.
      revert dependent L.
      revert dependent n.
      
      dependent induction w using strongind;
        
        dependent induction h using strongind; intros.
      
      * 
        inversion H3; subst.
        **
          cut_free.
          simpl in H0, H1.
          refine (cut_aux _ _ _ H4 H8); auto.
        **
          cut_free.
          simpl in H1, H0.
          inversion H0.
      * 
        inversion H3; subst. 
        **
          
          cut_free.
          simpl in H1.
          rename H1 into Hw, H2 into Hh.
          rename H4 into P, H5 into Hn1, H9 into Hn2.
          rename m into n1, n0 into n2. 
          rename M into M1, N into M2.  

          destruct F; simpl ((_)°)in *; try inversion Hw.
          refine (aux_CUT_ap _ Hh _ P Hn1 Hn2); eauto.
          rewrite union_comm_app in P.
          rewrite Nat.add_comm in Hh.
          refine (aux_CUT_ap _ Hh _ _ Hn2 Hn1); eauto.
          refine (aux_CUT_tz _ Hh _ Hn1 Hn2); eauto.
          refine (aux_CUT_bo _ Hh _ Hn1 Hn2); eauto.
          rewrite union_comm_app in P.
          rewrite Nat.add_comm in Hh.
          refine (aux_CUT_tz _ Hh _ Hn2 Hn1); eauto.
          rewrite union_comm_app in P.
          rewrite Nat.add_comm in Hh.
          refine (aux_CUT_bo _ Hh _ Hn2 Hn1); eauto.
        **
          cut_free.
          simpl in H1.
          inversion H1.
      * 
        inversion H3; subst.
        **
          cut_free.
          simpl in H2.
          cut_free.
          refine (cut_aux' H1 H4 H5 H9).        
        **
          cut_free.
          simpl in H2.
          cut_free.         
          refine (ccut_aux H1 H4 H5 H9).
      * inversion H3; subst; try cut_free.
        -- (** cut *)
          rename H2 into Hw, H4 into Hh.
          rename H5 into P, H6 into Hn1, H10 into Hn2.
          rename m into n1, n0 into n2. 
          rename M into M1, N into M2.
          clear H3.
          destruct F; simpl ((_)°)in *; try inversion Hw.
          refine (aux_CUT_tp _ _ _ _ P Hn1 Hn2); eauto. 
          rewrite union_comm_app in P.
          rewrite Nat.add_comm in Hh.
          refine (aux_CUT_tp _ _ _ _ P Hn2 _); eauto.
          rewrite <- !lweight_dual; auto.
          rewrite <- !ng_involutive; auto.
          rewrite union_comm_app in P.
          rewrite Nat.add_comm in Hh.
          refine (aux_CUT_pw _ _ _ _ P Hn2 _); eauto.     
          rewrite <- !lweight_dual; auto.
          rewrite <- !ng_involutive; auto.
          refine (aux_CUT_pw _ _ _ _ P Hn1 Hn2); eauto.
          refine (aux_CUT_bq _ _ _ _ P Hn1 Hn2); eauto.
          rewrite union_comm_app in P.
          rewrite Nat.add_comm in Hh.
          refine (aux_CUT_bq _ _ _ _ P Hn2 _); eauto.
          rewrite <- !lweight_dual; auto.
          rewrite <- !ng_involutive; auto.
        --
          rename H2 into Hw, H4 into Hh.
          rename H5 into P, H6 into Hn1, H10 into Hn2.
          rename m into n1, n0 into n2.
          rename M into M1, N into M2. 
          
          inversion Hn1;subst.
          eapply resolvers in H1; intuition; inversion H2.
          eapply resolvers2 in H1; intuition; inversion H2.
          
          (* Top Commutes *)
          simpl_cases2.
          rewrite H2 in P.
          eexists.
          eapply sig3_top; resolve_rewrite.
          
          (* Bot Commutes *)
          simpl_cases2.
          assert (exists m, m |~> 0 ; B; x ++ M2) as Hyp. 
          rewrite H1 in H2.
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H2 Hn2); 
                auto; try resolve_rewrite]; resolve_max.
          
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_bot _ Ht); auto; resolve_rewrite.
          
          (* Par Commutes *)
          simpl_cases2.
          assert (exists m, m |~> 0 ; B; F0 :: G :: (x ++ M2)) as Hyp. 
          rewrite H1 in H2; 
            rewrite union_rotate_cons in H2.
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H2 Hn2); 
                auto; try resolve_rewrite]; resolve_max.
          
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_par _ Ht); auto; resolve_rewrite.
          
          (* Tensor Commutes *)
          simpl_cases2.
          cut_free.
          simpl_cases_tns.
          
          assert (exists m, m |~> 0 ; B; F0 :: (L1 ++ M2)) as Hyp.
          rewrite HL1 in H4;
            rewrite meq_swap_cons in H4.
          refine (H0 _ _ _ _ _ _);
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H4 Hn2); 
                auto; try resolve_rewrite].
          inversion Hh.  resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_tensor _ Ht H6); auto; resolve_rewrite.
          
          assert (exists m, m |~> 0 ; B; G :: (L2 ++ M2)) as Hyp.
          
          rewrite HL2 in H6;
            rewrite meq_swap_cons in H6.
          refine (H0 _ _ _ _ _ _);
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H6 Hn2); 
                auto; try resolve_rewrite].
          inversion Hh.  resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_tensor _ H4 Ht); auto; resolve_rewrite.
          
          (* Plus1 Commutes *)
          simpl_cases2.
          assert (exists m : nat, m |~> 0 ; B; F0 :: x ++ M2) as Hyp.
          rewrite H1 in H2;
            rewrite meq_swap_cons in H2.  
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H2 Hn2); 
                auto; try resolve_rewrite]; resolve_max.
          
          destruct Hyp as [t Ht];
            try rewrite union_assoc in Ht;
            eexists;
            refine (sig3_plus1 _ Ht); auto; resolve_rewrite. 
          
          (* Plus2 Commutes *)
          simpl_cases2.
          assert (exists m : nat, m |~> 0 ; B; G :: x ++ M2) as Hyp.
          rewrite H1 in H2; 
            rewrite meq_swap_cons in H2.  
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H2 Hn2); 
                auto; try resolve_rewrite]; resolve_max.
          
          destruct Hyp as [t Ht];
            try rewrite union_assoc in Ht;
            eexists;
            refine (sig3_plus2 _ Ht); auto; resolve_rewrite.
          
          (* With Commutes *)  
          simpl_cases2.
          cut_free.          
          assert (exists m, m |~> 0 ; B; F0 :: (x ++ M2)) as Hyp1.
          rewrite H2 in H4; 
            rewrite meq_swap_cons in H4;
            refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H4 Hn2); 
                auto; try resolve_rewrite];resolve_max.
          inversion Hh;  resolve_max.
          
          assert (exists m, m |~> 0 ; B; G :: (x ++ M2)) as Hyp2.
          rewrite H2 in H6; rewrite meq_swap_cons in H6;
            refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H6 Hn2); 
                auto; try resolve_rewrite];resolve_max.
          inversion Hh;  resolve_max.
          destruct Hyp1 as [t1 Ht1];
            destruct Hyp2 as [t2 Ht2];
            
            eexists;
            refine (sig3_with _ Ht1 Ht2); resolve_rewrite.
          
          (* Copy Commutes *)  
          assert (exists m, m |~> 0 ; B ; F0 :: L) as Hyp.
          rewrite meq_swap_cons in H2.
          rewrite H2 in H4.
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H4 Hn2); 
                auto; try resolve_rewrite];resolve_max.
          
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_copy _ _ Ht); auto; resolve_rewrite.
          
          (* Quest Commutes *)  
          simpl_cases2.
          
          assert (exists m, m |~> 0 ; F0 :: B; x ++ M2) as Hyp.
          rewrite H1 in H2. 
          eapply height_preserving_weakning_sig3 with (D:=[F0]) in Hn2.
          rewrite <- app_comm_cons in Hn2.
          rewrite union_comm_app in Hn2.
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0); 
                refine (sig3_ccut _ _ _ H2 Hn2); 
                auto; try resolve_rewrite]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_quest _ Ht); auto; resolve_rewrite.
          
          (* Bang Principal *) 
          eapply resolvers2 in H1; intuition.
          rewrite H5 in P, Hn1; clear H5.
          rewrite <- P in *. clear P.
          rewrite bng_eq in H4.
          rewrite <- H4 in *; clear H4.
          
          inversion Hn2; subst; inversion Hh; try cut_free.
          eexists; eapply sig3_init; eassumption.
          eexists; eapply sig3_one; eassumption.
          eexists; eapply sig3_top; eassumption.
          assert (exists m : nat, m |~> 0; B; M) as Hyp.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H4);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_bot _ Ht); auto; resolve_rewrite.
          assert (exists m, m |~> 0; B; F1 :: G :: M) as Hyp.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H4);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_par _ Ht); auto; resolve_rewrite.     
          assert (exists m, m |~> 0; B; F1 :: M) as Hyp1.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H5);
              auto]; resolve_max.
          assert (exists m, m |~> 0; B; G :: N) as Hyp2.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H7);
              auto]; resolve_max.        
          destruct Hyp1 as [t1 Ht1];
            destruct Hyp2 as [t2 Ht2];
            eexists;
            refine (sig3_tensor _ Ht1 Ht2); auto; resolve_rewrite.
          assert (exists m, m |~> 0; B; F1 :: M) as Hyp.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H4);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_plus1 _ Ht); auto; resolve_rewrite.   
          assert (exists m, m |~> 0; B; G :: M) as Hyp.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H4);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_plus2 _ Ht); auto; resolve_rewrite.
          assert (exists m, m |~> 0; B; F1 :: M) as Hyp1.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H5);
              auto]; resolve_max.
          assert (exists m, m |~> 0; B; G :: M) as Hyp2.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H7);
              auto]; resolve_max.        
          destruct Hyp1 as [t1 Ht1];
            destruct Hyp2 as [t2 Ht2];
            eexists;
            refine (sig3_with _ Ht1 Ht2); auto; resolve_rewrite.
          
          Focus 2.
          assert (exists m, m |~> 0; F1 :: B; M) as Hyp.
          rewrite meq_swap_cons in H4.
          eapply height_preserving_weakning_sig3 with (D:=[F1]) in Hn1.
          rewrite union_comm_app in Hn1.
          
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H4);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_quest _ Ht); auto; resolve_rewrite.
          Focus 2.
          assert (exists m, m |~> 0; B; [F1]) as Hyp.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H4);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_bang _ Ht); auto; resolve_rewrite.  
          
          destruct (eq_dec F1 F0°); subst.
          assert (exists m, m |~> 0; B; F0° :: L) as Hyp. 
          rewrite H4 in H5.     
          refine (H0 _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0);
                refine (sig3_ccut _ _ _ Hn1 H5); 
                auto; resolve_rewrite]; resolve_max.
          
          destruct Hyp as [t Ht].
          
          refine (H _ _ _ _ _ _ _); 
            [ | change (0%nat) with (0+0)].
          Focus 2.
          refine (sig3_cut _ _ _ H2 Ht); auto. 
          inversion Hw. 
          resolve_max.

          simpl_cases2.
          assert (exists m, m |~> 0; B; F1 :: L) as Hyp.
          rewrite H4 in H5.
          refine (H0 _ _ _ _ _ _); 
            [ | 
              change (0%nat) with (0+0);
              refine (sig3_ccut _ _ _ Hn1 H5);
              auto]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_copy _ _ Ht); auto. 
Qed.

Theorem cut_elimination : forall B L n c, n |~> c ; B ; L ->
                                                        exists m, m |~> 0 ; B ; L.
Proof.
  intros.
  dependent induction n generalizing B L using strongind; induction c using strongind.
  + (* Case <0,0> *)
    eexists; eauto.
  + (* Case <0, S c> *)
    inversion H.
  + (* case <Sn, 0> *)
    inversion H0;subst;try (rewrite H2).
    ++ (* BOTTOM*) eexists. refine(sig3_bot _ _);eauto.
    ++ (* PAR *)  eexists. refine(sig3_par _ _);eauto.
    ++ (* TENSOR *) apply plus_is_O in H2.
       destruct H2;subst.
       eexists.
       assert(S(Init.Nat.max n0 m) |~> 0 + 0 ; B ; (F ** G) :: (M ++ N)).
       refine(sig3_tensor _ _ _);eauto.
       rewrite H3.
       eauto.
    ++ (* OPLUS F *)  eexists. refine(sig3_plus1 _ _);eauto.
    ++ (* OPLUS G *)  eexists. refine(sig3_plus2 _ _);eauto.
    ++ (* WITH *) apply plus_is_O in H2.
       destruct H2;subst.
       assert(S(Init.Nat.max n0 m) |~> 0 + 0 ; B ; (F & G) :: (M )).
       refine(sig3_with _ _ _);eauto.
       eexists.
       rewrite H3.
       eauto.
    ++ (* COPY *) eexists. refine(sig3_copy _ _ _);eauto.
    ++ (* QUEST *) eexists. refine(sig3_quest _ _);eauto.
    ++ (* BANG *) eexists. refine(sig3_bang _ _);eauto.
  + (* Case <Sn, Sc> *)
    rename H1 into IHn.

    inversion H0;subst.
    ++   (* bottom *)
      apply H in H3;auto.  destruct H3.
      eexists.
      rewrite H2.
      refine(sig3_bot _ _);eauto.

    ++   (* PAR *)
      apply H in H3;auto.  destruct H3.
      eexists.
      rewrite H2.
      refine(sig3_par _ _);eauto.

    ++
      (* TENSOR *)
      apply H in H4;auto. destruct H4.
      apply H in H5;auto. destruct H5.

      assert(S(Init.Nat.max x0 x) |~> (0+0); B; (F ** G) :: (M ++ N)).
      refine(sig3_tensor _ _ _ );eauto.
      
      eexists.
      rewrite H3.
      eauto. 
    ++ (* PLUS1 *)
      apply H in H3;auto.  destruct H3.
      eexists.
      rewrite H2.
      refine(sig3_plus1 _ _);eauto.

    ++ (* PLUS2 *)
      apply H in H3;auto.  destruct H3.
      eexists.
      rewrite H2.
      refine(sig3_plus2 _ _);eauto.

    ++ (* WITH *)
      apply H in H4;auto.  destruct H4.
      apply H in H5;auto.  destruct H5.

      assert(S(Init.Nat.max x0 x) |~> 0 + 0 ; B ; (F & G) :: M).
      refine(sig3_with _ _ _);eauto.
      
      eexists.
      rewrite H3.
      eauto. 
    ++ (* copy *)
      apply H in H4;auto.  destruct H4.
      eexists.
      refine(sig3_copy _ _ _);eauto.
    ++  (* quest *)
      apply H in H3;auto.  destruct H3.
      eexists.
      rewrite H2.
      refine(sig3_quest _ _);eauto.
    ++ (* bang *)
      apply H in H3;auto.  destruct H3.
      eexists.
      rewrite H2.
      refine(sig3_bang _ _);eauto.
    ++ (* CUT *)
      destruct H3.
    --
      apply H in H4;auto. destruct H4.
      apply H in H5;auto. destruct H5.
      
      assert(S(Init.Nat.max x0 x) |~> S(0 + 0) ; B ; L).
      eapply sig3_CUT.
      eapply  sig3_cut;eauto.

      
      apply cut_elimination_base in H6.
      destruct H6.
      eexists. eauto.
    --
      (* CCUT *)
      apply H in H4;auto. destruct H4.
      apply H in H5;auto. destruct H5.
      
      assert(S(Init.Nat.max x0 x) |~> S(0 + 0) ; B ; L).
      eapply sig3_CUT.
      eapply  sig3_ccut;eauto.

      apply cut_elimination_base in H6.
      destruct H6.
      eexists; eauto.  
Qed.

Theorem weak_consistency : forall n c, ~ sig3 n c [] [0].
Proof.
  intros.
  intro.
  apply cut_elimination in H.
  destruct H.
  inversion H; subst;
    try simpl_cases0.
  eapply DestructMulFalse; eauto.
Qed.

Lemma strong_cons : forall n c, ~ sig3 n c [] [].
Proof.
  intros.
  intro.
  apply cut_elimination in H.
  destruct H.
  inversion H; subst;
    try solve [eapply DestructMulFalse; eauto].
Qed. 

Theorem strong_consistency : forall n c, ~ sig3 n c [] [Bot].
Proof.
  intros.
  intro.
  apply cut_elimination in H.
  destruct H.
  inversion H; subst;
    try simpl_cases0.
  rewrite Hm in H1.
  eapply strong_cons; eauto.
  eapply DestructMulFalse; eauto.
Qed.

Theorem sig2h_then_sig3 : forall n B L, n |-- B ; L -> exists m, m |~> 0 ; B ; L.
Proof.
  intros.
  induction H; try destruct IHsig2h; try destruct IHsig2h1; try destruct IHsig2h2.
  eexists.
  eapply sig3_init; eauto.
  eexists.
  eapply sig3_one; eauto.
  eexists.
  eapply sig3_top; eauto.
  eexists.
  eapply sig3_bot; eauto.
  eexists.
  eapply sig3_par; eauto.
  eapply cut_elimination.
  eapply sig3_tensor; eauto.
  eexists.
  eapply sig3_plus1; eauto.
  eexists.
  eapply sig3_plus2; eauto.
  eapply cut_elimination.
  eapply sig3_with; eauto.    
  eexists.
  eapply sig3_copy; eauto.  
  eexists.
  eapply sig3_quest; eauto. 
  eexists.
  eapply sig3_bang; eauto.   
Qed.

Theorem sig3_then_sig2h : forall n B L, n |~> 0 ; B ; L -> exists m, m |-- B ; L.
Proof.
  intros.
  revert dependent B.
  revert dependent L.
  induction n using strongind; intros.
  inversion H; subst. 
  eexists.
  eapply sig2h_init; eauto.
  eexists.
  eapply sig2h_one; eauto.
  eexists.
  eapply sig2h_top; eauto.
  inversion H0; subst.
  assert (exists m, m |-- B; M) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];
    eexists.
  eapply sig2h_bot; eauto.
  assert (exists m, m |-- B; F :: G :: M) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];  
    eexists.
  eapply sig2h_par; eauto.
  cut_free.
  assert (exists m, m |-- B; F :: M) as Hyp1 by 
        solve [eapply H with (m0:=m); auto].
  assert (exists m, m |-- B; G :: N) as Hyp2 by 
        solve [eapply H with (m0:=n0); auto].
  destruct Hyp1 as [t1 Ht1];  
    destruct Hyp2 as [t2 Ht2]; 
    eexists.
  eapply sig2h_tensor; eauto.  
  assert (exists m, m |-- B; F :: M) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];   
    eexists.
  eapply sig2h_plus1; eauto.
  assert (exists m, m |-- B; G :: M) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];   
    eexists.
  eapply sig2h_plus2; eauto.
  cut_free.
  assert (exists m, m |-- B; F :: M) as Hyp1 by 
        solve [eapply H with (m0:=m); auto].
  assert (exists m, m |-- B; G :: M) as Hyp2 by 
        solve [eapply H with (m0:=n0); auto].
  destruct Hyp1 as [t1 Ht1];  
    destruct Hyp2 as [t2 Ht2]; 
    eexists.
  eapply sig2h_with; eauto.  
  assert (exists m, m |-- B; L0) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];      
    eexists.
  eapply sig2h_copy; eauto.  
  assert (exists m, m |--  F :: B; M) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];  
    eexists.
  eapply sig2h_quest; eauto.
  assert (exists m, m |--  B; [F]) as Hyp by solve [eapply H; eauto].
  destruct Hyp as [t Ht];   
    eexists.
  eapply sig2h_bang; eauto.
Qed.

Theorem sig3_then_sig2h' : forall B L, (exists n, n |~> 0 ; B ; L) -> exists m, m |-- B ; L.
Proof.
  intros.
  destruct H.
  eapply sig3_then_sig2h.
  eauto.
Qed.

Lemma exists_com : forall (A:Type) (P:A -> A -> Prop), (exists a b, P a b) <-> exists b a, P a b.
Proof.
  split; intros;
    do 2 destruct H;
    do 2 eexists; eauto.
Qed.

(** LL without cut equivalence with cut *)
Theorem sig2h_then_sig2hc : forall n B L, n |-- B ; L -> exists m, m |-c B ; L.
Proof.
  intros.
  apply sig2h_then_sig3 in H.
  apply sig2hc_iff_sig2hcc.
  apply sig3_iff_sig2hcc.
  apply exists_com.
  eexists 0%nat.
  auto.
Qed.

(** LL with cut equivalence without cut *)
Theorem sig2hc_then_sig2h : forall n B L, n |-c B ; L -> exists m, m |-- B ; L.
Proof.
  intros.
  apply sig2hc_then_sig2hcc in H.
  apply sig2hcc_then_sig3 in H.
  destruct H.
  apply cut_elimination in H.
  apply sig3_then_sig2h'. auto.
Qed.