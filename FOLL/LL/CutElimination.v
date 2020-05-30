(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Cut Elimination
Here we prove cut-elimination for linear logic and, as a corollary, we show the consistency of the logic
 *)

(*Add LoadPath "../". *)

Require Import Coq.Relations.Relations. 
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
(* Require Export StructuralRules. *)
Require Export LL.SequentCalculi.
Require Export LL.Eqset. 
Require Import LL.CutCases.


Module CElimination (DT : Eqset_dec_pol).
  Module Export Sys :=  CCases DT.

  Ltac simpl_duals H :=
    try rewrite one_bot in H;
    try rewrite bot_one in H; 
    try rewrite top_zero in H; 
    try rewrite zero_top in H;
    try rewrite atom_perp in H;
    try rewrite perp_atom in H;
    try rewrite tensor_par in H;
    try rewrite par_tensor in H;
    try rewrite with_plus in H;
    try rewrite plus_with in H;
    try rewrite bang_quest in H;
    try rewrite quest_bang in H.

  Theorem cut_aux B L M1 M2 F : 
    L =mul= M1 ++ M2 ->
    0 |~> 0 ; B ; F :: M1 ->
                  0 |~> 0 ; B ; F° :: M2 -> 
                                exists m, m |~> 0 ; B ; L.
  Proof.
    intros P Hn1 Hn2.    
    inversion Hn1; subst.
    * 
      apply axPair in H.
      destruct H;
        firstorder; subst.
    + 
      simpl_duals Hn2.
      inversion Hn2; subst.
    - (* init rule *)
      apply axPair in H.
      destruct H;
        firstorder; [lexp_contr H |].
      apply PerpEq in H; subst.
      eexists; eapply sig3_init.
      eauto.
    - (* contradiction *) 
      eapply resolvers2 in H; firstorder; lexp_contr H.
    - (* top rule *)
      simpl_cases2.
      top_commutes.
      + (* symmetric case *)   
        simpl_duals Hn2.
        inversion Hn2; subst.
    - (* init rule *)
      apply axPair in H.
      destruct H;
        firstorder; [|lexp_contr H].
      apply AtomEq in H; subst.
      eexists; eapply sig3_init.
      eauto.
    - (* contradiction *) 
      eapply resolvers2 in H; firstorder; lexp_contr H.
    - (* top rule *)
      simpl_cases2.
      top_commutes.
      *
        eapply resolvers2 in H; firstorder. 
        subst.
        simpl_duals Hn2.
        inversion Hn2; subst.
      + (* contradiction *)
        apply resolvers in H; firstorder; lexp_contr H.
      + (* contradiction *)  
        eapply resolvers2 in H; firstorder; lexp_contr H.
      + (* top rule *)  
        simpl_cases2.
        top_commutes.
        *  
          destruct (FEqDec F Top).  
      + 
        subst. simpl_cases4.   
        simpl_duals Hn2.
        inversion Hn2; subst.
    - (* contradiction *)
      apply resolvers in H0; firstorder; lexp_contr H0.
    - (* contradiction *) 
      eapply resolvers2 in H0; firstorder; lexp_contr H0.
    - (* top rule *)
      simpl_cases2.
      top_commutes.
      + (* top rule *) 
        simpl_cases2.
        top_commutes.
  Qed.       
  Arguments cut_aux[B L M1 M2 F]. 

  Theorem ccut_aux  B L M1 M2 F w :
    S w = Lexp_weight (! F) -> L =mul= M1 ++ M2 ->
    0 |~> 0 ; B ; ! F :: M1 -> 0 |~> 0 ; F° :: B ; M2 -> 
                                                   exists m, m |~> 0 ; B ; L.
  Proof.
    intros Hw P Hn1 Hn2.
    inversion Hn1; subst;
      [ apply resolvers in H; firstorder; lexp_contr H |
        apply resolvers2 in H; firstorder; lexp_contr H |
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
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_bot _ Ht); eauto.   
      + assert (exists m, m |~> 0; B; F :: G :: M) as Hyp by solve [eapply H; auto].
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_par _ Ht); resolve_rewrite. 
      + apply Nat.eq_add_1 in H2.
        destruct H2; destruct H1; subst.
        assert (exists m, m |~> 0; B; F :: M) as Hyp.
        refine (H _ _ _ _ H4); resolve_max.
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_tensor _ Ht H5); resolve_rewrite; auto. 
        assert (exists m, m |~> 0; B; G :: N) as Hyp.
        refine (H _ _ _ _ H5); resolve_max.
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_tensor _ H4 Ht); resolve_rewrite.        
      + assert (exists m, m |~> 0; B; F :: M) as Hyp by solve [eapply H; auto].
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_plus1 _ Ht); resolve_rewrite.  
      + assert (exists m, m |~> 0; B; G :: M) as Hyp by solve [eapply H; auto].
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_plus2 _ Ht); resolve_rewrite.  
      + apply Nat.eq_add_1 in H2.
        destruct H2; destruct H1; subst.
        assert (exists m, m |~> 0; B; F :: M) as Hyp.
        refine (H _ _ _ _ H4); resolve_max.
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_with _ Ht H5); resolve_rewrite. auto.  
        assert (exists m, m |~> 0; B; G :: M) as Hyp.
        refine (H _ _ _ _ H5); resolve_max.
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_with _ H4 Ht); resolve_rewrite.    
      + rewrite H3 in H4.
        assert (exists m, m |~> 0; B; F:: L) as Hyp by solve [eapply H; auto].
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_copy _ _ Ht); auto.
      + assert (exists m, m |~> 0; F:: B; M) as Hyp by solve [eapply H; auto].
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_quest _ Ht); auto.
      + assert (exists m, m |~> 0; B; [F]) as Hyp by solve [eapply H; auto].
        destruct Hyp as [t Ht]; eexists;
          refine (sig3_bang _ Ht); auto.
      + assert (exists m, m |~> 0; B; Subst FX t :: M) as Hyp by solve [eapply H; auto].
        destruct Hyp as [p Hp]; eexists; eapply sig3_ex; eauto. 
      + 
        assert (forall y : Term, exists m, m |~> 0; B; Subst FX y :: M) as Hyp.
        intro.
        assert (n |~> 1; B; Subst FX y :: M) by auto.
        eapply H; auto.
        apply fx_swap_sig3h in Hyp.   
        destruct Hyp as [p Hp];
          eexists; eapply sig3_fx; eauto.
      + (* caso CUT *)
        clear H0. clear H.
        revert dependent B.
        revert dependent L.
        revert dependent n.
        
        dependent induction w using strongind;
          
          dependent induction h using strongind; intros.
        
        * (* w=h=0 *) 
          inversion H3; subst.
          **
            cut_free.
            simpl in H0, H1.
            cut_free. 
            eapply cut_aux; eauto.
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
            caseLexp F; subst; simpl; try inversion Hw;
              simpl_duals Hn1; simpl_duals Hn2. 
            refine (aux_CUT_ap _ Hh _ P Hn1 Hn2); eauto.
            rewrite union_comm in P.
            rewrite Nat.add_comm in Hh.
            refine (aux_CUT_ap _ Hh _ _ Hn2 Hn1); eauto.
            rewrite union_comm in P.
            rewrite Nat.add_comm in Hh.
            refine (aux_CUT_bo _ Hh _ _ Hn2 Hn1); eauto.
            refine (aux_CUT_bo _ Hh _ _ Hn1 Hn2); eauto.
            rewrite union_comm in P.
            rewrite Nat.add_comm in Hh.
            refine (aux_CUT_tz _ Hh _ _ Hn2 Hn1); eauto. 
            refine (aux_CUT_tz _ Hh _ _ Hn1 Hn2); eauto.        
          **
            cut_free.
            simpl in H1.
            inversion H1.
        * (* h=0 e S w *)
          inversion H3; subst.
          **
            cut_free.
            simpl in H2.
            cut_free. 
            eapply cut_aux; eauto.
          **
            cut_free.
            simpl in H2.
            cut_free.          
            eapply ccut_aux; eauto.
        * inversion H3; subst; try cut_free.
          -- (** cut *)
            rename H2 into Hw, H4 into Hh.
            rename H5 into P, H6 into Hn1, H10 into Hn2.
            rename m into n1, n0 into n2. 
            rename M into M1, N into M2.
            clear H3. 
            caseLexp F; subst; simpl; try inversion Hw;
              simpl_duals Hn1; simpl_duals Hn2.
            refine (aux_CUT_tp _ _ _ _ P Hn1 Hn2); eauto. 
            rewrite union_comm in P.
            rewrite Nat.add_comm in Hh.
            refine (aux_CUT_tp _ _ _ _ P Hn2 _); eauto.
            rewrite <- !lweight_dual; auto.
            rewrite <- !Ng_involutive; auto.
            rewrite union_comm in P.
            rewrite Nat.add_comm in Hh.
            refine (aux_CUT_pw _ _ _ _ P Hn2 _); eauto.     
            rewrite <- !lweight_dual; auto.
            rewrite <- !Ng_involutive; auto.
            refine (aux_CUT_pw _ _ _ _ P Hn1 Hn2); eauto.
            refine (aux_CUT_bq _ _ _ _ P Hn1 Hn2); eauto.
            rewrite union_comm in P.
            rewrite Nat.add_comm in Hh.
            refine (aux_CUT_bq _ _ _ _ P Hn2 _); eauto.
            rewrite <- !lweight_dual; auto.
            rewrite <- !Ng_involutive; auto.
            refine (aux_CUT_ef _ _ Hw _ P Hn1 Hn2 ); eauto.
            refine (aux_CUT_fe _ _ Hw _ P Hn1 Hn2 ); eauto. 

          -- (** ccut *) 
            rename H2 into Hw, H4 into Hh.
            rename H5 into P, H6 into Hn1, H10 into Hn2.
            rename m into n1, n0 into n2.
            rename M into M1, N into M2. 
            
            inversion Hn1;subst. 
            eapply resolvers in H1; intuition; 
              lexp_contr H2.
            eapply resolvers2 in H1; intuition; 
              lexp_contr H2.
            
            (* Top Commutes *)
            simpl_cases2.
            eexists.
            rewrite P.
            rewrite H2.
            eapply sig3_top. eauto.
            
            (* Bot Commutes *)
            simpl_cases2.
            assert (exists m, m |~> 0 ; B; x ++ M2) as Hyp. 
            rewrite H1 in H2.
            refine (H0 _ _ _ _ _ _); 
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
                  refine (sig3_ccut _ _ _ H4 Hn2); 
                  auto; try resolve_rewrite];resolve_max.
            inversion Hh;  resolve_max.
            
            assert (exists m, m |~> 0 ; B; G :: (x ++ M2)) as Hyp2.
            rewrite H2 in H6; rewrite meq_swap_cons in H6;
              refine (H0 _ _ _ _ _ _); 
              [ | change (0%nat) with (plus 0 0); 
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
              [ | change (0%nat) with (plus 0 0); 
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
            rewrite union_comm in Hn2.
            refine (H0 _ _ _ _ _ _); 
              [ | change (0%nat) with (plus 0 0); 
                  refine (sig3_ccut _ _ _ H2 Hn2); 
                  auto; try resolve_rewrite]; resolve_max.
            destruct Hyp as [t Ht];
              eexists;
              refine (sig3_quest _ Ht); auto; resolve_rewrite.
            
            (* Bang Principal *) 
            eapply resolvers2 in H1; intuition.
            rewrite H5 in P, Hn1; clear H5.
            rewrite <- P in *. clear P.
            LexpSubst.
            
            inversion Hn2; subst; inversion Hh; try cut_free.
            eexists; eapply sig3_init; eassumption.
            eexists; eapply sig3_one; eassumption.
            eexists; eapply sig3_top; eassumption.
            assert (exists m : nat, m |~> 0; B; M) as Hyp.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H4);
                auto]; resolve_max.
            destruct Hyp as [t Ht];
              eexists;
              refine (sig3_bot _ Ht); auto; resolve_rewrite.
            assert (exists m, m |~> 0; B; F0 :: G :: M) as Hyp.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H4);
                auto]; resolve_max.
            destruct Hyp as [t Ht];
              eexists;
              refine (sig3_par _ Ht); auto; resolve_rewrite.     
            assert (exists m, m |~> 0; B; F0 :: M) as Hyp1.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H5);
                auto]; resolve_max.
            assert (exists m, m |~> 0; B; G :: N) as Hyp2.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H7);
                auto]; resolve_max.        
            destruct Hyp1 as [t1 Ht1];
              destruct Hyp2 as [t2 Ht2];
              eexists;
              refine (sig3_tensor _ Ht1 Ht2); auto; resolve_rewrite.
            assert (exists m, m |~> 0; B; F0 :: M) as Hyp.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H4);
                auto]; resolve_max.
            destruct Hyp as [t Ht];
              eexists;
              refine (sig3_plus1 _ Ht); auto; resolve_rewrite.   
            assert (exists m, m |~> 0; B; G :: M) as Hyp.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H4);
                auto]; resolve_max.
            destruct Hyp as [t Ht];
              eexists;
              refine (sig3_plus2 _ Ht); auto; resolve_rewrite.
            assert (exists m, m |~> 0; B; F0 :: M) as Hyp1.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H5);
                auto]; resolve_max.
            assert (exists m, m |~> 0; B; G :: M) as Hyp2.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H7);
                auto]; resolve_max.        
            destruct Hyp1 as [t1 Ht1];
              destruct Hyp2 as [t2 Ht2];
              eexists;
              refine (sig3_with _ Ht1 Ht2); auto; resolve_rewrite.
            
            2:{
              assert (exists m, m |~> 0; F0 :: B; M) as Hyp.
              rewrite meq_swap_cons in H4.
              eapply height_preserving_weakning_sig3 with (D:=[F0]) in Hn1.
              rewrite union_comm in Hn1.
            
              refine (H0 _ _ _ _ _ _); 
                [ | 
                  change (0%nat) with (plus 0 0);
                  refine (sig3_ccut _ _ _ Hn1 H4);
                  auto]; resolve_max.
              destruct Hyp as [t Ht];
                eexists;
                refine (sig3_quest _ Ht); auto; resolve_rewrite.
            }

            2:{
              assert (exists m, m |~> 0; B; [F0]) as Hyp.
              refine (H0 _ _ _ _ _ _); 
                [ | 
                  change (0%nat) with (plus 0 0);
                  refine (sig3_ccut _ _ _ Hn1 H4);
                  auto]; resolve_max.
              destruct Hyp as [t Ht];
                eexists;
                refine (sig3_bang _ Ht); auto; resolve_rewrite.
            }
            
            destruct (FEqDec F0 F°); subst.
            assert (exists m, m |~> 0; B; F° :: L) as Hyp. 
            rewrite H4 in H5.     
            refine (H0 _ _ _ _ _ _); 
              [ | change (0%nat) with (plus 0 0);
                  refine (sig3_ccut _ _ _ Hn1 H5); 
                  auto; resolve_rewrite]; resolve_max.
            
            destruct Hyp as [t Ht].
            
            refine (H _ _ _ _ _ _ _); 
              [ | change (0%nat) with (plus 0 0)].
            2:{  refine (sig3_cut _ _ _ H2 Ht); auto. }
            inversion Hw.  unfold Lexp_weight; auto.
            apply not_eqLExp_sym in n1.
            simpl_cases2.
            assert (exists m, m |~> 0; B; F0 :: L) as Hyp.
            rewrite H4 in H5.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H5);
                auto]; resolve_max.
            destruct Hyp as [t Ht];
              eexists;
              refine (sig3_copy _ _ Ht); auto.

            assert (exists m, m |~> 0; B; Subst FX t :: M) as Hyp.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H4);
                auto]; resolve_max.
            destruct Hyp as [p Hp];
              eexists;
              refine (sig3_ex _ Hp); auto; resolve_rewrite.     
            
            assert (forall y : Term, exists m, m |~> 0; B; Subst FX y :: M) as Hyp.
            intro.
            assert (n0 |~> 0; F° :: B; Subst FX y :: M) by auto.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ Hn1 H5);
                auto]; resolve_max.
            apply fx_swap_sig3h in Hyp.   
            destruct Hyp as [p Hp];
              eexists;
              refine (sig3_fx _ Hp); auto; resolve_rewrite. 
            
            simpl_cases2. 
            assert (exists m, m |~> 0; B; Subst FX t :: (x++M2)) as Hyp.
            rewrite H1 in H2.
            rewrite meq_swap_cons in H2.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ H2 Hn2) ;
                auto]; resolve_max.
            destruct Hyp as [p Hp];
              eexists;
              refine (sig3_ex _ Hp); auto; resolve_rewrite.      

            simpl_cases2. 
            assert (forall y : Term, exists m, m |~> 0; B; Subst FX y :: (x++M2)) as Hyp.
            intro.
            assert (n |~> 0; B; Subst FX y :: M) by auto.
            rewrite H1 in H5.
            rewrite meq_swap_cons in H5.
            refine (H0 _ _ _ _ _ _); 
              [ | 
                change (0%nat) with (plus 0 0);
                refine (sig3_ccut _ _ _ H5 Hn2) ;
                auto]; resolve_max.
            apply fx_swap_sig3h in Hyp.   
            destruct Hyp as [p Hp];
              eexists;
              refine (sig3_fx _ Hp); auto; resolve_rewrite. 
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
      ++ (* BOTTOM*) eexists. eapply sig3_bot;eauto.
      ++ (* PAR *)  eexists. eapply sig3_par;eauto.
      ++ (* TENSOR *) 
        cut_free.
        eexists.
        change (0%nat) with (plus 0 0).
        eapply sig3_tensor;eauto.
      ++ (* OPLUS F *)  eexists. eapply sig3_plus1; eauto.
      ++ (* OPLUS G *)  eexists. eapply sig3_plus2; eauto.
      ++ (* WITH *)
        cut_free.
        eexists.
        change (0%nat) with (plus 0 0).
        eapply sig3_with;eauto.
      ++ (* COPY *) eexists. eapply sig3_copy; eauto.
      ++ (* QUEST *) eexists. eapply sig3_quest; eauto.
      ++ (* BANG *) eexists. eapply sig3_bang; eauto.
      ++ (* EX *) eexists. eapply sig3_ex; eauto.
      ++ (* FX *) eexists. eapply sig3_fx; eauto.
    + (* Case <Sn, Sc> *)
      rename H1 into IHn.

      inversion H0;subst.
      ++   (* bottom *)
        apply H in H3; auto. destruct H3.
        eexists.
        eapply sig3_bot; eauto.

      ++   (* PAR *)
        apply H in H3;auto.  destruct H3.
        eexists.
        eapply sig3_par; eauto.

      ++
        (* TENSOR *)
        apply H in H4;auto. destruct H4.
        apply H in H5;auto. destruct H5.
        change (0%nat) with (plus 0 0).        
        eexists.
        eapply sig3_tensor;eauto.
      ++ (* PLUS1 *)
        apply H in H3;auto.  destruct H3.
        eexists.
        eapply sig3_plus1; eauto.

      ++ (* PLUS2 *)
        apply H in H3;auto.  destruct H3.
        eexists.
        eapply sig3_plus2; eauto.

      ++ (* WITH *)
        apply H in H4;auto.  destruct H4.
        apply H in H5;auto.  destruct H5.

        change (0%nat) with (plus 0 0).        
        eexists.
        eapply sig3_with;eauto.
      ++ (* copy *)
        apply H in H4;auto.  destruct H4.
        eexists.
        eapply sig3_copy; eauto.
      ++  (* quest *)
        apply H in H3;auto.  destruct H3.
        eexists.
        eapply sig3_quest;eauto.
      ++ (* bang *)
        apply H in H3;auto.  destruct H3.
        eexists.
        eapply sig3_bang; eauto.
      ++ (* ex *)
        apply H in H3;auto.  destruct H3.
        eexists.
        eapply sig3_ex; eauto.
      ++ (* fx *)
        assert (forall y : Term, exists m, m |~> 0; B; Subst FX y :: M) as Hyp.
        intro.
        assert (n |~> S c; B; Subst FX y :: M) by auto.
        eapply H; auto.
        apply fx_swap_sig3h in Hyp.   
        destruct Hyp as [p Hp].
        eexists.
        eapply sig3_fx;eauto.               
      ++ (* CUT *)
        destruct H3.
      --
        apply H in H4;auto. destruct H4.
        apply H in H5;auto. destruct H5.
        
        assert(Hc: S(Init.Nat.max x0 x) |~> S(0 + 0) ; B ; L).
        eapply sig3_CUT.
        eapply  sig3_cut;eauto.

        apply cut_elimination_base in Hc.
        destruct Hc.
        eexists. eauto.
      --
        (* CCUT *)
        apply H in H4;auto. destruct H4.
        apply H in H5;auto. destruct H5.
        
        assert(Hc: S(Init.Nat.max x0 x) |~> S(0 + 0) ; B ; L).
        eapply sig3_CUT.
        eapply  sig3_ccut;eauto.

        apply cut_elimination_base in Hc.
        destruct Hc.
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
End CElimination.
