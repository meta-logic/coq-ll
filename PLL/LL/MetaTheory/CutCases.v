(* This file is part of the Linear Logic  formalization in Coq: https://github.com/brunofx86/LL *)

(** ** Cut Cases

In this file we prove the cases for cut-elimination. Each lemma contains a case for the respective connective (and its dual). 
 *)


(* Require Export Tactics.
Set Implicit Arguments. *)

Require Import llTactics.

Lemma aux_CUT_ap n1 n2 h B L M1 M2 v:   
  (forall m : nat,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m, m |~> 0; B; L) ->
  S h = n1 + n2 -> 0%nat = lexp_weight (v ⁺) -> L =mul= M1 ++ M2 ->
  n1 |~> 0; B; v ⁺ :: M1 ->
               n2 |~> 0; B; v ⁻ :: M2 ->
                            exists m, m |~> 0 ; B; L.
Proof.
  intros H Hh Hw P Hn1 Hn2.
  inversion Hn1; subst; inversion Hh; try cut_free.
  * {
      inversion Hn2; subst; inversion Hh; try cut_free.
      - simpl_cases2.
        refine (tab_bot_right_zero _ P _ _ _ H4 H3 Hn1 _); eauto.
      - simpl_cases2;
          refine (tab_par_right_zero _ _ _ P _ H4 H3 Hn1 _); eauto.  
      - simpl_cases2;    
          refine (tab_tensor_right_zero _ _ _ P _ H3 H4 H6 Hn1 Hn2); eauto. 
      - simpl_cases2;
          refine (tab_plus1_right_zero _ _ _ P _ H4 H3 Hn1 Hn2); eauto.
      - simpl_cases2;
          refine (tab_plus2_right_zero _ _ _ P _ H4 H3 Hn1 Hn2); eauto.
      - simpl_cases2;  
          refine (tab_with_right_zero _ _ P _ H3 H4 H6 Hn1 Hn2); eauto.
      - refine (tab_copy_right_zero _ _ _ P H2 _ _ Hn1 _) ; eauto.
      - simpl_cases2;
          refine (tab_quest_right_zero _ _ _ P _ H4 H3 Hn1 _); eauto.
      - apply resolvers2 in H2; firstorder; inversion H2.                    
    }  
  * apply resolvers2 in H0; firstorder; inversion H0.
  * simpl_cases2.
    top_commutes.
  * simpl_cases2;
      refine (tab_bot_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_par_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_tensor_left_zero _ _ P _ H1 H2 H4 Hn1 _ ); eauto.
  * simpl_cases2;
      refine (tab_plus1_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus2_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_with_left_zero _ _ P _ H1 H2 H4 Hn1 _ ); eauto.
  * refine (tab_copy_left_zero _ _ _ P H0 H1 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_quest_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * apply resolvers2 in H0; firstorder; inversion H0.
Qed.
Arguments aux_CUT_ap [n1 n2 h B L M1 M2 v].

Lemma aux_CUT_tz n1 n2 h B L M1 M2:   
  (forall m : nat,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> 
                         exists m, m |~> 0; B; L) ->
  S h = n1 + n2 -> L =mul= M1 ++ M2 ->
  n1 |~> 0; B; ⊤ :: M1 ->
               n2 |~> 0; B; 0 :: M2 ->
                            exists m, m |~> 0 ; B; L.
Proof.
  intros H Hh P Hn1 Hn2.
  inversion Hn1; subst; inversion Hh; try cut_free. 
  * apply resolvers in H0; firstorder; inversion H0.
  * apply resolvers2 in H0; firstorder; inversion H0.
  * {
      simpl_cases4. 
      inversion Hn2; subst; inversion Hh; try cut_free.
      - simpl_cases2;
          refine (tab_bot_right_zero _ P _ _ _ H4 H3 Hn1 _); eauto.
      - simpl_cases2;
          refine (tab_par_right_zero _ _ _ P _ H4 H3 Hn1 _); eauto.  
      - simpl_cases2;    
          refine (tab_tensor_right_zero _ _ _ P _ H3 H4 H6 Hn1 Hn2); eauto. 
      - simpl_cases2;
          refine (tab_plus1_right_zero _ _ _ P _ H4 H3 Hn1 Hn2); eauto.
      - simpl_cases2;
          refine (tab_plus2_right_zero _ _ _ P _ H4 H3 Hn1 Hn2); eauto.
      - simpl_cases2;  
          refine (tab_with_right_zero _ _ P _ H3 H4 H6 Hn1 Hn2); eauto.
      - refine (tab_copy_right_zero _ _ _ P H2 _ _ Hn1 _) ; eauto.
      - simpl_cases2;
          refine (tab_quest_right_zero _ _ _ P _ H4 H3 Hn1 _); eauto.
      - apply resolvers2 in H2; firstorder; inversion H2.                    
    }  
    
  * simpl_cases2; 
      refine (tab_bot_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_par_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_tensor_left_zero _ _ P _ H1 H2 H4 Hn1 _ ); eauto.
  * simpl_cases2;
      refine (tab_plus1_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus2_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_with_left_zero _ _ P _ H1 H2 H4 Hn1 _ ); eauto.
  * refine (tab_copy_left_zero _ _ _ P H0 H1 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_quest_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * apply resolvers2 in H0; firstorder; inversion H0.    
Qed.
Arguments aux_CUT_tz [n1 n2 h B L M1 M2].

Lemma aux_CUT_bo n1 n2 h B L M1 M2:   
  (forall m : nat,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m, m |~> 0; B; L) ->
  S h = n1 + n2 -> L =mul= M1 ++ M2 ->
  n1 |~> 0; B; ⊥ :: M1 ->
               n2 |~> 0; B; 1 :: M2 ->
                            exists m, m |~> 0 ; B; L.
Proof.
  intros H Hh P Hn1 Hn2.
  inversion Hn1; subst; inversion Hh; try cut_free. 
  * apply resolvers in H0; firstorder; inversion H0.
  * apply resolvers2 in H0; firstorder; inversion H0.
  * simpl_cases2; 
      top_commutes.
  * {
      simpl_cases4. 
      inversion Hn2; subst; inversion Hh; try cut_free.
      - apply resolvers in H2; firstorder; inversion H2.
      - apply resolvers2 in H2; firstorder.
        eexists.
        rewrite P, H3, H0, union_nil.
        eauto.
      - simpl_cases2; top_commutes.
      - simpl_cases2;
          refine (tab_bot_right_unit' _ P _ _ H3 H4 Hn1 _ ); eauto.
      - simpl_cases2;
          refine (tab_par_right_unit' _ _ P _ H3 H4 Hn1 _); eauto.  
      - simpl_cases2;
          refine (tab_tensor_right_unit' _ _ P _ H3 H5 H7 Hn1 Hn2); eauto. 
      - simpl_cases2;
          refine (tab_plus1_right_unit' _ _ P _ H3 H4 Hn1 Hn2); eauto.
      - simpl_cases2;
          refine (tab_plus2_right_unit' _ _  P _ H3 H4 Hn1 Hn2); eauto.
      - simpl_cases2;  
          refine (tab_with_right_unit' _ _ P _ H3 H5 H7 Hn1 Hn2); eauto. 
      - refine (tab_copy_right_unit' _ _ P H2 _ H5 Hn1 _); eauto.
      - simpl_cases2.
        refine (tab_quest_right_unit' _ _ P _ H3 H4 Hn1 _); eauto.
      - apply resolvers2 in H2; firstorder; inversion H2.                    
    }  
  * simpl_cases2;
      refine (tab_par_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_tensor_left_zero _ _ P _ H1 H2 H4 Hn1 _ ); eauto.
  * simpl_cases2;
      refine (tab_plus1_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus2_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_with_left_zero _ _ P _ H1 H2 H4 Hn1 _ ); eauto.
  * refine (tab_copy_left_zero _ _ _ P H0 H1 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_quest_left_zero _ _ _ P _ H2 H1 Hn1 _); eauto.
  * apply resolvers2 in H0; firstorder; inversion H0.
Qed.
Arguments aux_CUT_bo [n1 n2 h B L M1 M2].

Lemma aux_CUT_tp n1 n2 w h B L F G M1 M2:   
  (forall m : nat,
      m <= w ->
      forall (h n : nat) (L B : Multiset),
        n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  (forall m : nat,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m, m |~> 0; B; L) ->
  w = lexp_weight F + lexp_weight G ->
  S h = n1 + n2 -> L =mul= M1 ++ M2 ->
  n1 |~> 0; B; (F ** G) :: M1 ->
               n2 |~> 0; B; (F° $ G°) :: M2 ->
                            exists m, m |~> 0 ; B; L.
Proof.
  intros H H0 Hw Hh P Hn1 Hn2.
  inversion Hn1; subst; inversion Hh; try cut_free.
  * apply resolvers in H1; firstorder; inversion H1.
  * apply resolvers2 in H1; firstorder; inversion H1.
  * simpl_cases2; top_commutes.
  * simpl_cases2; 
      refine (tab_bot_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_par_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * {
      destruct (eq_dec (F ** G) (F0 ** G0)) as [Te|notTe].
      rewrite <- Te in *.
      apply tns_eq in Te.
      destruct Te as [Te1 Te2].
      rewrite <- Te1, <- Te2 in *. 
      clear Te1. clear Te2. 
      + {
          simpl_cases4. (* Tensor é principal em Hn1 *)
          inversion Hn2; subst; inversion Hh; try cut_free.
          - apply resolvers in H1; firstorder; inversion H1.
          - apply resolvers2 in H1; firstorder; inversion H1.
          - simpl_cases2; top_commutes.
          - simpl_cases2;
              refine (tab_bot_right _ P _ _ H6 H4 Hn1 Hn2); eauto.
          - 
            destruct (eq_dec (F1 $ G1) (F° $ G°)) as [Te|notTe].
            rewrite Te in *.
            apply par_eq in Te.
            destruct Te as [Te1 Te2].
            rewrite Te1, Te2 in *. 
            clear Te1; clear Te2.
            *
              simpl_cases4. (* Par é principal em Hn2 *)
              rewrite meq_swap_cons in H4.
              assert (exists m, m |~> 0 ; B; F° :: (N ++ M0)) as Hyp.
              refine (H _ _ _ _ _ _ _);
                [|change (0%nat) with (0+0); 
                  refine (sig3_cut _ _ _ H5 H4); auto]; resolve_max.
              
              destruct Hyp as [p Hp].
              refine (H _ _ _ _ _ _ _);
                [|change (0%nat) with (0+0); 
                  refine (sig3_cut _ _ _ H3 Hp); auto]. 
              resolve_max.
              rewrite P, H1, H2.
              app_normalize.
            * simpl_cases2.  
              assert (exists m, m |~> 0 ; B; F1 :: G1 :: (x ++ M1)) as Hyp.
              rewrite meq_swap_cons in H4;
                rewrite H1 in H4. 
              rewrite union_rotate_cons in H4. 
              refine (H0 _ _ _ _ _ _); 
                [ | change (0%nat) with (0+0); 
                    refine (sig3_cut _ _ _ Hn1 H4); 
                    auto]. resolve_max.
              solve_permutation.
              destruct Hyp as [t Ht];
                eexists; refine (sig3_par _ Ht); auto;
                  resolve_rewrite.
          - simpl_cases2;
              refine (tab_tensor_right _ _ P _ H4 H6 H8 Hn1 Hn2); eauto. 
          - simpl_cases2;
              refine (tab_plus1_right _ _ P _ H6 H4 Hn1 Hn2); eauto.
          - simpl_cases2;
              refine (tab_plus2_right _ _  P _ H6 H4 Hn1 Hn2); eauto.
          - simpl_cases2;  
              refine (tab_with_right _ _ P _ _ H6 H8 Hn1 Hn2); eauto. 
          - refine (tab_copy_right _ _ P H1 _ H6 Hn1 _); eauto.
          - simpl_cases2;
              refine (tab_quest_right _ _ P _ H6 H4 Hn1 _); eauto.
          - apply resolvers2 in H1; firstorder; inversion H1.                    
        }
      +  
        symmetry in H2.
        simpl_cases2. 
        refine (tab_tensor_left_zero' _ _ P _ H1 H3 H5 Hn1 _); eauto. 
    }
    
  * simpl_cases2;
      refine (tab_plus1_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus2_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_with_left_zero' _ _ P _ H2 H3 H5 Hn1 _ ); eauto.
  * refine (tab_copy_left _ _ _ P H1 _ H3 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_quest_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * apply resolvers2 in H1; firstorder; inversion H1.
Qed.  
Arguments aux_CUT_tp [n1 n2 w h B L F G M1 M2].

Lemma aux_CUT_pw n1 n2 w h B L F G M1 M2:   
  (forall m : nat,
      m <= w ->
      forall (h n : nat) (L B : Multiset),
        n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  (forall m : nat,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m, m |~> 0; B; L) ->
  w = lexp_weight F + lexp_weight G ->
  S h = n1 + n2 -> L =mul= M1 ++ M2 ->
  n1 |~> 0; B; (F & G) :: M1 ->
               n2 |~> 0; B; (F° ⊕ G°) :: M2 ->
                            exists m, m |~> 0 ; B; L.
Proof.
  intros H H0 Hw Hh P Hn1 Hn2.
  inversion Hn1; subst; inversion Hh; try cut_free.
  * apply resolvers in H1; firstorder; inversion H1.
  * apply resolvers2 in H1; firstorder; inversion H1.
  * simpl_cases2; top_commutes.
  * simpl_cases2; 
      refine (tab_bot_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_par_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_tensor_left_zero' _ _ P _ H2 H3 H5 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus1_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus2_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * {
      destruct (eq_dec (F & G) (F0 & G0)) as [Te|notTe].
      rewrite <- Te in *.
      apply wth_eq in Te.
      destruct Te as [Te1 Te2].
      rewrite <- Te1, <- Te2 in *. 
      clear Te1; clear Te2. 
      + {
          simpl_cases4. (* With é principal em Hn1 *)
          inversion Hn2; subst; inversion Hh; try cut_free.
          - apply resolvers in H1; firstorder; inversion H1.
          - apply resolvers2 in H1; firstorder; inversion H1.
          - simpl_cases2; top_commutes.
          - simpl_cases2;
              refine (tab_bot_right _ P _ _ H6 H4 Hn1 Hn2); eauto.
          - simpl_cases2;
              refine (tab_par_right' _ _ P _ H6 H4 Hn1 _ ); eauto.
          - simpl_cases2;
              refine (tab_tensor_right _ _ P _ H4 H6 H8 Hn1 _ ); eauto.       
          - destruct (eq_dec (F° ⊕ G°) (F1 ⊕ G1)) as [Te|notTe].
            rewrite <- Te in *.
            apply pls_eq in Te.
            destruct Te as [Te1 Te2].
            rewrite <- Te1 in *. 
            clear Te1; clear Te2.
            *
              simpl_cases4. (* Plus1 é principal em Hn2 *)
              refine (H _ _ _ _ _ _ _);
                [|change (0%nat) with (0+0); 
                  refine (sig3_cut _ _ _ H3 H4); 
                  auto; resolve_rewrite ]; resolve_max.
            * symmetry in H1. simpl_cases2.
              refine (tab_plus1_right _ _ P _ H1 H4 Hn1 _ ); eauto.
          - destruct (eq_dec (F° ⊕ G°) (F1 ⊕ G1)) as [Te|notTe].
            rewrite <- Te in *.
            apply pls_eq in Te.
            destruct Te as [Te1 Te2].
            rewrite <- Te2 in *. 
            clear Te1; clear Te2.
            *
              simpl_cases4. (* Plus2 é principal em Hn2 *)
              refine (H _ _ _ _ _ _ _);
                [|change (0%nat) with (0+0); 
                  refine (sig3_cut _ _ _ H5 H4); 
                  auto; resolve_rewrite ]; resolve_max.
            * symmetry in H1. simpl_cases2.
              refine (tab_plus2_right _ _ P _ H1 H4 Hn1 _ ); eauto.        
          - simpl_cases2;  
              refine (tab_with_right _ _ P _ _ H6 H8 Hn1 Hn2); eauto. 
          - refine (tab_copy_right _ _ P H1 _ H6 Hn1 _); eauto.
          - simpl_cases2;
              refine (tab_quest_right _ _ P _ H6 H4 Hn1 _); eauto.
          - apply resolvers2 in H1; firstorder; inversion H1.                   
        }
      + symmetry in H2. simpl_cases2. 
        refine (tab_with_left_zero' _ _ P _ H1 H3 H5 Hn1 _); eauto. 
    }
  * refine (tab_copy_left _ _ _ _ _ _ H3 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_quest_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * apply resolvers2 in H1; firstorder; inversion H1.
Qed.
Arguments aux_CUT_pw [n1 n2 w h B L F G M1 M2].

Lemma aux_CUT_bq n1 n2 w h B L F M1 M2:   
  (forall m : nat,
      m <= w ->
      forall (h n : nat) (L B : Multiset),
        n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  (forall m : nat,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m, m |~> 0; B; L) ->
  w = lexp_weight F ->
  S h = n1 + n2 -> L =mul= M1 ++ M2 ->
  n1 |~> 0; B; (! F) :: M1 ->
               n2 |~> 0; B; (? F°) :: M2 ->
                            exists m, m |~> 0 ; B; L.
Proof.
  intros H H0 Hw Hh P Hn1 Hn2.
  inversion Hn1; subst; inversion Hh; try cut_free.
  * apply resolvers in H1; firstorder; inversion H1.
  * apply resolvers2 in H1; firstorder; inversion H1.
  * simpl_cases2; top_commutes.
  * simpl_cases2; 
      refine (tab_bot_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_par_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2.
    simpl_cases_tns.
    
    assert (exists m, m |~> 0 ; B; F0 :: (L1 ++ M2)) as Hyp. 
    rewrite HL1 in H3.
    rewrite meq_swap_cons in H3.
    refine (H0 _ _ _ _ _ _);
      [ | change (0%nat) with (0+0); refine (sig3_cut _ _ _ H3 Hn2); 
          auto; try resolve_rewrite]; resolve_max.
    
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H5); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M2)) as Hyp.
    rewrite HL2 in H5;
      rewrite meq_swap_cons in H5.
    refine (H0 _ _ _ _ _ _);
      [ | change (0%nat) with (0+0); refine (sig3_cut _ _ _ H5 Hn2); 
          auto; try resolve_rewrite]; resolve_max.
    
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ H3 Ht); auto; resolve_rewrite.  
  * simpl_cases2;
      refine (tab_plus1_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_plus2_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * simpl_cases2.
    assert (exists m, m |~> 0 ; B; F0 :: (M2 ++ x)) as Hyp1.
    rewrite H1 in H3; 
      rewrite meq_swap_cons in H3.
    refine (H0 _ _ _ _ _ _); 
      [ | change (0%nat) with (0+0); 
          refine (sig3_cut _ _ _ H3 Hn2); auto; 
          try resolve_rewrite; perm_simplify]; resolve_max.
    
    assert (exists m, m |~> 0 ; B; G :: (M2 ++ x)) as Hyp2.        
    rewrite H1 in H5; 
      rewrite meq_swap_cons in H5.
    refine (H0 _ _ _ _ _ _); 
      [ | change (0%nat) with (0+0); 
          refine (sig3_cut _ _ _ H5 Hn2); auto;
          try resolve_rewrite; perm_simplify]; resolve_max.

    destruct Hyp1 as [t1 Ht1];
      destruct Hyp2 as [t2 Ht2];
      
      eexists;
      refine (sig3_with _ Ht1 Ht2);
      resolve_rewrite. 
    rewrite <- app_comm_cons. solve_permutation.   
  * refine (tab_copy_left _ _ _ P _ _ _ Hn1 _); eauto.
  * simpl_cases2;
      refine (tab_quest_left _ _ _ P _ H3 H2 Hn1 _); eauto.
  * {
      apply resolvers2 in H1; firstorder; inversion H1. (* Bang é principal em Hn1 *)
      rewrite H3 in Hn1.
      rewrite <- H6 in *.
      clear H1; clear H6.
      inversion Hn2; subst; inversion Hh; try cut_free.
      - apply resolvers in H1; firstorder; inversion H1.
      - apply resolvers2 in H1; firstorder; inversion H1.
      - simpl_cases2; top_commutes. 
      - simpl_cases2;
          refine (tab_bot_right_unit  _ _ _ _ H3 H5 Hn1 Hn2); eauto.
      - simpl_cases2;
          refine (tab_par_right_unit _ _ _ _ H3 H5 Hn1 _ ); eauto.
      - simpl_cases2;
          refine (tab_tensor_right_unit _ _ _ _  H3 H6 H8 Hn1 _ ); eauto.       
      - simpl_cases2;
          refine (tab_plus1_right_unit _ _ _ _ H3 H5 Hn1 Hn2 ); eauto.       
      - simpl_cases2;
          refine (tab_plus2_right_unit _ _ _ _ H3 H5 Hn1 Hn2 ); eauto.       
      - simpl_cases2;
          refine (tab_with_right_unit _ _ _ _ H3 H6 H8 Hn1 _ ); eauto.       
      - refine (tab_copy_right_unit _ _ _ H1 _ _ Hn1 Hn2) ; eauto.  
      - destruct (eq_dec (? F0°) (? F1)) as [Te|notTe].
        rewrite <- Te in *; rewrite qst_eq in Te.
        rewrite <- Te in *. clear Te. 
        + simpl_cases4. (* Quest é principal em Hn2 *)
          eapply H0 with (m:=S n + n0); resolve_max.    
          change (0%nat) with (0+0);
            refine (sig3_ccut _ _ _ Hn1 H5); eauto.
        + symmetry in H1. simpl_cases2.
          assert (exists m, m |~> 0 ; F1 :: B ; x) as Hyp.
          eapply height_preserving_weakning_sig3 with (D:=[F1]) in Hn1;
            rewrite union_comm_app in Hn1. simpl in Hn1.
          rewrite H3 in H5.
          refine (H0 _ _ _ _ _ _); 
            [|change (0%nat) with (0+0); 
              refine (sig3_cut _ _ _ Hn1 H5); 
              auto; try resolve_rewrite]; resolve_max.
          destruct Hyp as [t Ht];
            eexists;
            refine (sig3_quest _ Ht); auto;
              resolve_rewrite.
      - apply resolvers2 in H1; firstorder; inversion H1.
    }
Qed.              
Arguments aux_CUT_bq [n1 n2 w h B L F M1 M2].
