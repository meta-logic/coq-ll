(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Cut Cases

In this file we prove the cases for cut-elimination. Each lemma contains a case for the respective connective (and its dual). 
 *)


(* Require Export Tactics.
Set Implicit Arguments. *)

(*Add LoadPath "../". *)
Require Import LL.CutTactics.

Module CCases (DT : Eqset_dec_pol).
  Module Export Sys :=  CTactics DT.

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

  Lemma aux_CUT_ap n1 n2 h B L M1 M2 v:   
    (forall m : nat,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m, m |~> 0; B; L) ->
    S h = n1 + n2 -> 0%nat = Lexp_weight (v ⁺) -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; v ⁺ :: M1 ->
                 n2 |~> 0; B; v ⁻ :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof.
    intros H Hh Hw P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free.
    * {
        inversion Hn2; subst; inversion Hh; try cut_free.
        - simpl_cases2.
          organizer.
          refine (tab_bot H _ Hw P H2 H4 H3 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_par H _ Hw P H2 H4 H3 Hn2 Hn1). omega.
        - simpl_cases2. 
          organizer.
          refine (tab_tensor _ _ _ P H2 H3 H4 H6 Hn2 Hn1); eauto.   
        - simpl_cases2.
          organizer.
          refine (tab_plus1 H _ Hw P H2 H4 H3 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_plus2 H _ Hw P H2 H4 H3 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.  
          refine (tab_with _ _ _ P H2 H3 H4 H6 Hn2 Hn1); eauto.   
        - simpl_cases2.
          organizer.
          refine (tab_copy H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_quest H _ Hw P H2 H4 H3 Hn2 Hn1). omega.
        - apply resolvers2 in H2; firstorder; lexp_contr H2.
        - simpl_cases2.
          organizer.
          refine (tab_ex H _ Hw P H2 H4 H3 Hn2 Hn1). omega.
        - simpl_cases2. 
          organizer.
          refine (tab_fx H _ Hw P H2 H4 H3 Hn2 Hn1). omega.   
      }  
    * apply resolvers2 in H0; firstorder; lexp_contr H0.
    * simpl_cases2.
      top_commutes.
    * simpl_cases2.  
      refine (tab_bot _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2.  
      refine (tab_par _ _ _ P _ H2 H1 Hn1 _); eauto.    
    * simpl_cases2.
      refine (tab_tensor _ _ _ P H0 H1 H2 H4 Hn1 _); eauto.   
    * simpl_cases2;
        refine (tab_plus1 _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_plus2 _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2.
      refine (tab_with _ _ _ P H0 H1 H2 H4 Hn1 Hn2); eauto.   
    * refine (tab_copy _ _ _ P H0 H1 H2 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_quest _ _ _ P _ H2 H1 Hn1 _); eauto.
    * apply resolvers2 in H0; firstorder; lexp_contr H0.
    * simpl_cases2. 
      refine (tab_ex H _ Hw P H0 H2 H1 Hn1 Hn2). omega.  
    * simpl_cases2. 
      refine (tab_fx H _ Hw P H0 H2 H1 Hn1 Hn2). omega.    
  Qed.
  Arguments aux_CUT_ap [n1 n2 h B L M1 M2 v].

  Lemma aux_CUT_tz n1 n2 h B L M1 M2:   
    (forall m : nat,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> 
                           exists m, m |~> 0; B; L) ->
    S h = n1 + n2 -> 0%nat = Lexp_weight (⊤) -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; ⊤ :: M1 ->
                 n2 |~> 0; B; 0 :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof.
    intros H Hh Hw P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free. 
    * apply resolvers in H0; firstorder;  lexp_contr H0.
    * apply resolvers2 in H0; firstorder;  lexp_contr H0. 
    * {
        simpl_cases4. 
        inversion Hn2; subst; inversion Hh; try cut_free.
        - simpl_cases2. organizer.
          refine (tab_bot H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.
        - simpl_cases2. 
          organizer.
          refine (tab_par H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.
        - simpl_cases2; organizer.
          refine (tab_tensor _ _ _ P H2 H3 H4 H6 Hn2 Hn1); eauto.   
        - simpl_cases2.
          organizer.
          refine (tab_plus1 H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.
        - simpl_cases2.
          organizer.
          refine (tab_plus2 H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.
        - simpl_cases2;  
            organizer.  
          refine (tab_with _ _ _ P H2 H3 H4 H6 Hn2 Hn1); eauto.   
        - simpl_cases2.
          organizer.
          refine (tab_copy H _ Hw P H2 H3 H4 Hn2 Hn1). 
          omega.
        - simpl_cases2.
          organizer.
          refine (tab_quest H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.
        - apply resolvers2 in H2; firstorder; lexp_contr H2.
        - simpl_cases2.
          organizer.
          refine (tab_ex H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.
        - simpl_cases2. 
          organizer.
          refine (tab_fx H _ Hw P H2 H4 H3 Hn2 Hn1). 
          omega.                       
      }    

    * simpl_cases2;
        refine (tab_bot _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_par _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_tensor _ _ _ P H0 H1 H2 H4 Hn1 _); eauto.   
    * simpl_cases2;
        refine (tab_plus1 _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_plus2 _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_with _ _ _ P H0 H1 H2 H4 Hn1 Hn2); eauto.   
    * refine (tab_copy _ _ _ P H0 H1 H2 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_quest _ _ _ P _ H2 H1 Hn1 _); eauto.
    * apply resolvers2 in H0; firstorder; lexp_contr H0.
    * simpl_cases2. 
      refine (tab_ex H _ Hw P H0 H2 H1 Hn1 Hn2). omega.  
    * simpl_cases2. 
      refine (tab_fx H _ Hw P H0 H2 H1 Hn1 Hn2). omega.    
  Qed. 
  Arguments aux_CUT_tz [n1 n2 h B L M1 M2].

  Lemma aux_CUT_bo n1 n2 h B L M1 M2:   
    (forall m : nat,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m, m |~> 0; B; L) ->
    S h = n1 + n2 -> 0%nat = Lexp_weight (⊥) -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; ⊥ :: M1 ->
                 n2 |~> 0; B; 1 :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof. 
    intros H Hh Hw P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free. 
    * apply resolvers in H0; firstorder;  lexp_contr H0.
    * apply resolvers2 in H0; firstorder;  lexp_contr H0. 
    * simpl_cases2; top_commutes.
    * {
        simpl_cases4. 
        inversion Hn2; subst; inversion Hh; try cut_free.
        - apply resolvers in H2; firstorder;  lexp_contr H2. 
        - apply resolvers2 in H2; firstorder.
          rewrite H3 in P. rewrite union_empty in P.
          rewrite <- P in H0.
          rewrite <- H0 in H1.
          eexists; eauto. 
        - simpl_cases2; top_commutes.  
        - simpl_cases2. organizer.
          refine (tab_bot H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - simpl_cases2. organizer.
          refine (tab_par H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - simpl_cases2; organizer.
          refine (tab_tensor _ _ _ P H2 H3 H5 H7 Hn2 Hn1) ; eauto. omega.   
        - simpl_cases2.
          organizer.
          refine (tab_plus1 H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_plus2 H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - simpl_cases2;  
            organizer.  
          refine (tab_with _ _ _ P H2 H3 H5 H7 Hn2 Hn1); eauto. omega.  
        - simpl_cases2.
          organizer.
          refine (tab_copy H _ Hw P H2 H4 H5 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_quest H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - apply resolvers2 in H2; firstorder; lexp_contr H2.
        - simpl_cases2.
          organizer.
          refine (tab_ex H _ Hw P H2 H3 H4 Hn2 Hn1). omega.
        - simpl_cases2. 
          organizer.
          refine (tab_fx H _ Hw P H2 H3 H4 Hn2 Hn1). omega.                       
      }    

    * simpl_cases2;
        refine (tab_par _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_tensor _ _ _ P H0 H1 H2 H4 Hn1 _); eauto.   
    * simpl_cases2;
        refine (tab_plus1 _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_plus2 _ _ _ P _ H2 H1 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_with _ _ _ P H0 H1 H2 H4 Hn1 Hn2); eauto.   
    * refine (tab_copy _ _ _ P H0 H1 H2 Hn1 _); eauto.
    * simpl_cases2;
        refine (tab_quest _ _ _ P _ H2 H1 Hn1 _); eauto.
    * apply resolvers2 in H0; firstorder; lexp_contr H0.
    * simpl_cases2. 
      refine (tab_ex H _ Hw P H0 H2 H1 Hn1 Hn2). omega.  
    * simpl_cases2. 
      refine (tab_fx H _ Hw P H0 H2 H1 Hn1 Hn2). omega.    
  Qed.
  Arguments aux_CUT_bo [n1 n2 h B L M1 M2].

  Lemma tensor_par_principal n m n0 B L F G N M M1 M2:     
    (forall m : nat,
        m <= Lexp_weight F + Lexp_weight G ->
        forall (h n : nat) (L B : Multiset),
          n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    L =mul= M1 ++ M2 ->
    S (max n m) |~> 0; B; F ** G :: M1 ->
                          S n0 |~> 0; B; F° $ G° :: M2 ->
                                         M1 =mul= M ++ N ->
                                         m |~> 0; B; F :: M ->
                                                     n |~> 0; B; G :: N ->
                                                                 n0 |~> 0; B; F° :: G° :: M2 -> exists m0 : nat, m0 |~> 0 + 0; B; L.
  Proof.
    intros.  
    rewrite meq_swap_cons in H6.
    assert (exists m, m |~> 0 ; B; F° :: (N ++ M2)) as Hyp.
    refine (H _ _ _ _ _ _ _);
      [|change (0%nat) with (0+0); 
        refine (sig3_cut _ _ _ H5 H6); auto]; resolve_max.
    destruct Hyp as [p Hp].
    
    refine (H _ _ _ _ _ _ _);
      [|change (0%nat) with (0+0); 
        refine (sig3_cut _ _ _ H4 Hp); auto]; resolve_max.
    rewrite H0, H3.
    solve_permutation.
  Qed.

  Arguments tensor_par_principal [n m n0 B L F G N M M1 M2].

  Lemma with_plus1_principal n m n0 B L F G M1 M2:     
    (forall m : nat,
        m <= Lexp_weight F + Lexp_weight G ->
        forall (h n : nat) (L B : Multiset),
          n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    L =mul= M1 ++ M2 ->
    S (max n m) |~> 0; B; F & G :: M1 ->
                          S n0 |~> 0; B; F° ⊕ G° :: M2 ->
                                         m |~> 0; B; F :: M1 ->
                                                     n |~> 0; B; G :: M1 ->
                                                                 n0 |~> 0; B; F° :: M2 -> exists m0 : nat, m0 |~> 0 + 0; B; L.
  Proof.
    intros.
    refine (H _ _ _ _ _ _ _);
      [|change (0%nat) with (0+0); 
        refine (sig3_cut _ _ _ H3 H5); auto]; resolve_max.
  Qed.

  Arguments with_plus1_principal [n m n0 B L F G M1 M2].

  Lemma with_plus2_principal n m n0 B L F G M1 M2:     
    (forall m : nat,
        m <= Lexp_weight F + Lexp_weight G ->
        forall (h n : nat) (L B : Multiset),
          n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    L =mul= M1 ++ M2 ->
    S (max n m) |~> 0; B; F & G :: M1 ->
                          S n0 |~> 0; B; F° ⊕ G° :: M2 ->
                                         m |~> 0; B; F :: M1 ->
                                                     n |~> 0; B; G :: M1 ->
                                                                 n0 |~> 0; B; G° :: M2 -> exists m0 : nat, m0 |~> 0 + 0; B; L.
  Proof.
    intros.
    refine (H _ _ _ _ _ _ _);
      [|change (0%nat) with (0+0); 
        refine (sig3_cut _ _ _ H4 H5); auto]; resolve_max.
  Qed.
  
  Arguments with_plus2_principal [n m n0 B L F G M1 M2].  
  
  Lemma bang_quest_principal n n0 B L F:     
    (forall m : nat,
        m <= n + S n0 ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S (Lexp_weight F); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    S n |~> 0; B; [! F] ->
                  S n0 |~> 0; B; ? F° :: L ->
                                 n |~> 0; B; [F] ->
                                             n0 |~> 0; F° :: B; L -> exists m0 : nat, m0 |~> 0; B; L.
  Proof.
    intros.
    refine (H _ _ _ _ _ _);
      [|change (0%nat) with (0+0); 
        refine (sig3_ccut _ _ _ H0 H3); auto]; resolve_max. 
  Qed.     

  Arguments bang_quest_principal [n n0 B L F].

  Lemma aux_CUT_tp n1 n2 w h B L F G M1 M2:   
    (forall m : nat,
        m <= w ->
        forall (h n : nat) (L B : Multiset),
          n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    (forall m : nat,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m, m |~> 0; B; L) ->
    w = Lexp_weight F + Lexp_weight G ->
    S h = n1 + n2 -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; (F ** G) :: M1 ->
                 n2 |~> 0; B; (F° $ G°) :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof.
    intros H H0 Hw Hh P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free.
    * apply resolvers in H1; firstorder; lexp_contr H1.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2; top_commutes.
    * simpl_cases2.
      refine (tab_bot H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_par H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    *
      destruct (FEqDec (F ** G) (F0 ** G0)) as [Te|notTe].
      rewrite <- Te in *.
      assert (F0 = F) by solve [eapply TensorEq1; eauto].
      assert (G0 = G) by solve [eapply TensorEq2; eauto].
      subst.
      clear Te. 
    + {
        simpl_cases4. (* Tensor é principal em Hn1 *)
        inversion Hn2; subst; inversion Hh; try cut_free.
        - apply resolvers in H1; firstorder; lexp_contr H1.
        - apply resolvers2 in H1; firstorder; lexp_contr H1.
        - simpl_cases2; top_commutes.
        - simpl_cases2. 
          organizer.
          
          refine (tab_bot H0 _ _ P H1 H6 H4 Hn2 Hn1); auto.
          omega.
          rewrite lweight_dual_plus; auto.
        - 
          destruct (FEqDec (F0 $ G0) (F° $ G°)) as [Te|notTe].
          rewrite Te in *.
          
          assert (F° = F0) by solve [eapply ParEq1; eauto].
          assert (G° = G0) by solve [eapply ParEq2; eauto].
          subst.
          clear Te.
          *
            simpl_cases4. (* Par é principal em Hn2 *)
            rewrite <- H1 in *.
            refine (tensor_par_principal H P Hn1 Hn2 H2 H3 H5 H4).
          * 
            simpl_cases2.
            organizer.
            refine (tab_par H0 _ _ P H6 H1 H4 Hn2 Hn1).
            omega.
            rewrite lweight_dual_plus; auto.
        - simpl_cases2.
          organizer.
          refine (tab_tensor H0 _ _ P H1 H4 H6 H8 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.
        - simpl_cases2.
          organizer.     
          refine (tab_plus1 H0 _ _ P H1 H6 H4 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.
        - simpl_cases2.
          organizer.     
          refine (tab_plus2 H0 _ _ P H1 H6 H4 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.
        - simpl_cases2.
          organizer.
          refine (tab_with H0 _ _ P H1 H4 H6 H8 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.
        - organizer.
          refine (tab_copy H0 _ _ P H1 H4 H6 Hn2 Hn1). 
          omega.
          rewrite lweight_dual_plus; auto.       
        - simpl_cases2.
          organizer.
          refine (tab_quest H0 _ _ P H1 H6 H4 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.        
        - apply resolvers2 in H1; firstorder; lexp_contr H1.  
        - simpl_cases2.
          organizer.
          refine (tab_ex H0 _ _ P H1 H6 H4 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.   
        - simpl_cases2.
          organizer.
          refine (tab_fx H0 _ _ P H1 H6 H4 Hn2 Hn1).
          omega.
          rewrite lweight_dual_plus; auto.                   
      }
    +  
      simpl_cases2. 
      refine (tab_tensor H0 _ _ P H1 H2 H3 H5 Hn1 Hn2); auto. 
      
      * simpl_cases2.
        refine (tab_plus1 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
      * simpl_cases2.
        refine (tab_plus2 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
      * simpl_cases2.
        refine (tab_with H0 _ _ P _ _ H3 H5 Hn1 Hn2); auto.
      * refine (tab_copy H0 _ _ P H1 H2 H3 Hn1 Hn2); auto.
      * simpl_cases2.
        refine (tab_quest H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
      * apply resolvers2 in H1; firstorder; lexp_contr H1.
      * simpl_cases2.
        refine (tab_ex H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
      * simpl_cases2.
        refine (tab_fx H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
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
    w = Lexp_weight F + Lexp_weight G ->
    S h = n1 + n2 -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; (F & G) :: M1 ->
                 n2 |~> 0; B; (F° ⊕ G°) :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof.
    intros H H0 Hw Hh P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free.
    * apply resolvers in H1; firstorder; lexp_contr H1.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2; top_commutes.
    * simpl_cases2.
      refine (tab_bot H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_par H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2. 
      refine (tab_tensor H0 _ _ P H1 H2 H3 H5 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus1 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus2 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * {
        destruct (FEqDec (F & G) (F0 & G0)) as [Te|notTe].
        rewrite <- Te in *.
        assert (F = F0) by solve [eapply WithEq1; eauto].
        assert (G = G0) by solve [eapply WithEq2; eauto].  
        rewrite <- H1, <- H4 in *. 
        clear H1; clear H4; clear Te. 
        + {
            simpl_cases4. (* With é principal em Hn1 *)
            inversion Hn2; subst; inversion Hh; try cut_free.
            - apply resolvers in H1; firstorder; lexp_contr H1.
            - apply resolvers2 in H1; firstorder; lexp_contr H1.
            - simpl_cases2; top_commutes.
            - simpl_cases2. 
              organizer.
              refine (tab_bot H0 _ _ P H1 H6 H4 Hn2 Hn1); auto.
              omega.
              rewrite lweight_dual_plus; auto.
            - simpl_cases2. 
              organizer.
              refine (tab_par H0 _ _ P H1 H6 H4 Hn2 Hn1); auto.
              omega.
              rewrite lweight_dual_plus; auto.       
            - simpl_cases2.
              organizer.
              refine (tab_tensor H0 _ _ P H1 H4 H6 H8 Hn2 Hn1).
              omega.
              rewrite lweight_dual_plus; auto.
            - destruct (FEqDec (F° ⊕ G°) (F1 ⊕ G1)) as [Te|notTe].
              rewrite <- Te in *.
              assert (F° = F1) by solve [eapply PlusEq1; eauto].
              assert (G° = G1) by solve [eapply PlusEq2; eauto].  
              rewrite <- H6, <- H7 in *. 
              clear H6; clear H7; clear Te. 
              *
                simpl_cases4. (* Plus1 é principal em Hn2 *)
                rewrite <- H2 in *.
                rewrite <- H1 in *.
                refine (with_plus1_principal H P Hn1 Hn2 H3 H5 H4).
              * simpl_cases2.
                
                simpl_cases2.
                organizer.     
                refine (tab_plus1 H0 _ _ P H1 H6 H4 Hn2 Hn1).
                omega.
                rewrite lweight_dual_plus; auto.
            - destruct (FEqDec (F° ⊕ G°) (F1 ⊕ G1)) as [Te|notTe].
              rewrite <- Te in *.
              assert (F° = F1) by solve [eapply PlusEq1; eauto].
              assert (G° = G1) by solve [eapply PlusEq2; eauto].  
              rewrite <- H6, <- H7 in *. 
              clear H6; clear H7; clear Te. 
              *
                simpl_cases4. (* Plus2 é principal em Hn2 *)
                rewrite <- H2 in *.
                rewrite <- H1 in *.
                refine (with_plus2_principal H P Hn1 Hn2 H3 H5 H4).
              * simpl_cases2.
                simpl_cases2.
                organizer.     
                refine (tab_plus2 H0 _ _ P H1 H6 H4 Hn2 Hn1).
                omega.
                rewrite lweight_dual_plus; auto.    
            - simpl_cases2.
              organizer.
              refine (tab_with H0 _ _ P H1 H4 H6 H8 Hn2 Hn1).
              omega.
              rewrite lweight_dual_plus; auto.
            - organizer.
              refine (tab_copy H0 _ _ P H1 H4 H6 Hn2 Hn1). 
              omega.
              rewrite lweight_dual_plus; auto.              
            - simpl_cases2.
              organizer.
              refine (tab_quest H0 _ _ P H1 H6 H4 Hn2 Hn1).
              omega.
              rewrite lweight_dual_plus; auto.        
            - apply resolvers2 in H1; firstorder; lexp_contr H1.  
            - simpl_cases2.
              organizer.
              refine (tab_ex H0 _ _ P H1 H6 H4 Hn2 Hn1).
              omega.
              rewrite lweight_dual_plus; auto.   
            - simpl_cases2.
              organizer.
              refine (tab_fx H0 _ _ P H1 H6 H4 Hn2 Hn1).
              omega.
              rewrite lweight_dual_plus; auto. 
          }
        +   simpl_cases2.    
            refine (tab_with H0 _ _ P _ _ H3 H5 Hn1 Hn2); auto.
      }

    * refine (tab_copy H0 _ _ P H1 H2 H3 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_quest H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2.
      refine (tab_ex H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_fx H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
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
    w = Lexp_weight F ->
    S h = n1 + n2 -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; (! F) :: M1 ->
                 n2 |~> 0; B; (? F°) :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof. 
    intros H H0 Hw Hh P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free.
    * apply resolvers in H1; firstorder; lexp_contr H1.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2; top_commutes.
    * simpl_cases2.
      refine (tab_bot H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_par H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2. 
      refine (tab_tensor H0 _ _ P H1 H2 H3 H5 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus1 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus2 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_with H0 _ _ P _ _ H3 H5 Hn1 Hn2); auto.
    * refine (tab_copy H0 _ _ P H1 H2 H3 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_quest H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
    * {
        apply resolvers2 in H1; firstorder.
        assert (F = F0) by solve [eapply BangEq; eauto]. 
        rewrite H3 in Hn1.
        rewrite <- H5 in *.
        clear H1; clear H5.
        inversion Hn2; subst; inversion Hh; try cut_free.
        - apply resolvers in H1; firstorder; lexp_contr H1.
        - apply resolvers2 in H1; firstorder; lexp_contr H1.
        - simpl_cases2; top_commutes. 
        - simpl_cases2.
          organizer.
          refine (tab_bot H0 _ _ P H1 H3 H5 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.
        - simpl_cases2. 
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.
          refine (tab_par H0 _ _ P H1 H3 H5 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.       
        - simpl_cases2.
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.
          refine (tab_tensor H0 _ _ P H1 H3 H6 H8 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.
        - simpl_cases2.
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.    
          refine (tab_plus1 H0 _ _ P H1 H3 H5 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.
        - simpl_cases2.
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.   
          refine (tab_plus2 H0 _ _ P H1 H3 H5 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.
        - simpl_cases2.
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.
          refine (tab_with H0 _ _ P H1 H3 H6 H8 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.
        - organizer.
          refine (tab_copy H0 _ _ P H1 H5 H6 Hn2 Hn1). 
          omega.
          rewrite lweight_dual; auto.       
        - destruct (FEqDec (? F°) (? F1)) as [Te|notTe].
          rewrite <- Te in *.
          assert (F° = F1) by solve [eapply QuestEq; eauto]. 
          rewrite <- H3 in *.
          clear Te; clear H3.
          + simpl_cases4. (* Quest é principal em Hn2 *)
            simpl in P.
            rewrite <- H1 in *.
            rewrite <- P in *.
            refine (bang_quest_principal H0 Hn1 Hn2 H2 H5).
          + 
            simpl_cases2.
            organizer.
            refine (tab_quest H0 _ _ P H1 H3 H5 Hn2 Hn1).
            omega.
            rewrite lweight_dual; auto.     
        - apply resolvers2 in H1; firstorder; lexp_contr H1.  
        - simpl_cases2.
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.
          refine (tab_ex H0 _ _ P H1 H3 H5 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.   
        - simpl_cases2.
          rewrite (Ng_involutive (! F)) in Hn1;
            rewrite union_comm in P.
          refine (tab_fx H0 _ _ P H1 H3 H5 Hn2 Hn1).
          omega.
          rewrite lweight_dual; auto.
      }
    * simpl_cases2.
      refine (tab_ex H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_fx H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
  Qed.              

  Arguments aux_CUT_bq [n1 n2 w h B L F M1 M2].

  Lemma aux_CUT_ef n1 n2 w h B L FX M1 M2:   
    (forall m : nat,
        m <= w ->
        forall (h n : nat) (L B : Multiset),
          n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    (forall m : nat,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m, m |~> 0; B; L) ->
    S w = Lexp_weight (E{ FX}) ->
    S h = n1 + n2 -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; E{ FX} :: M1 ->
                 n2 |~> 0; B; (E{ FX})° :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof. 
    intros H H0 Hw Hh P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free.
    * apply resolvers in H1; firstorder; lexp_contr H1.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2; top_commutes.
    * simpl_cases2.
      refine (tab_bot H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_par H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2. 
      refine (tab_tensor H0 _ _ P H1 H2 H3 H5 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus1 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus2 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_with H0 _ _ P _ _ H3 H5 Hn1 Hn2); auto.
    * refine (tab_copy H0 _ _ P H1 H2 H3 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_quest H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * {
        destruct (FEqDec (E{ FX}) (E{ FX0})).
        assert (FX = FX0) by solve [eapply ExEq; eauto]. 
        subst. simpl_cases4.
        rewrite <- H1 in *.
        clear e; clear H1. (* Ex é principal em Hn1 *)
        inversion Hn2; subst; inversion Hh; try cut_free.
        - apply resolvers in H1; firstorder; lexp_contr H1.
        - apply resolvers2 in H1; firstorder; lexp_contr H1.
        - simpl_cases2; top_commutes. 
        - simpl_cases2.
          organizer.
          refine (tab_bot H0 _ Hw P H1 H4 H3 Hn2 Hn1).
          omega.
        - simpl_cases2. 
          organizer.
          refine (tab_par H0 _ Hw P H1 H4 H3 Hn2 Hn1).
          omega.    
        - simpl_cases2.
          organizer.
          refine (tab_tensor H0 _ Hw P H1 H3 H4 H6 Hn2 Hn1).
          omega.
        - simpl_cases2.
          organizer.   
          refine (tab_plus1 H0 _ Hw P H1 H4 H3 Hn2 Hn1).
          omega.
        - simpl_cases2.
          organizer.   
          refine (tab_plus2 H0 _ Hw P H1 H4 H3 Hn2 Hn1).
          omega.
        - simpl_cases2.
          organizer.
          refine (tab_with H0 _ Hw P H1 H3 H4 H6 Hn2 Hn1).
          omega.
        - organizer.
          refine (tab_copy H0 _ Hw P H1 H3 H4 Hn2 Hn1). 
          omega.    
        - simpl_cases2.
          organizer.
          refine (tab_quest H0 _ Hw P H1 H4 H3 Hn2 Hn1).
          omega.   
        - apply resolvers2 in H1; firstorder; lexp_contr H1.
        - simpl_cases2.
          organizer. 
          refine (tab_ex H0 _ Hw P H1 H4 H3 Hn2 Hn1).
          omega.
        - destruct (FEqDec ((E{ FX0})°) (F{ FX})).
          + 
            rewrite e in *.
            simpl_cases4.
            assert (n0 |~> 0; B; (Subst FX t) :: M0) by auto.
            assert (Subst FX0 t = (Subst FX t)°) by solve [apply SubsDual; auto].
            rewrite H5 in H2.
            rewrite H1 in *.
            rewrite union_comm in P.
            eapply H.
            
            2:{
            change (0%nat) with (0+0).
            refine (sig3_cut _ _ P H4 H2); auto.
            }
            eapply WeightEF; eauto.       
            
          + simpl_cases2.
            organizer. 
            refine (tab_fx H0 _ Hw P H1 H4 H3 Hn2 Hn1).
            omega.
        - simpl_cases2.  
          refine (tab_ex H0 _ Hw P H1 H3 H2 Hn1 Hn2).
          omega.
      }
    * simpl_cases2.
      refine (tab_fx H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
  Qed.              

  Arguments aux_CUT_ef [n1 n2 w h B L FX M1 M2].

  Lemma aux_CUT_fe n1 n2 w h B L FX M1 M2:   
    (forall m : nat,
        m <= w ->
        forall (h n : nat) (L B : Multiset),
          n ~> 0; m; h; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    (forall m : nat,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m, m |~> 0; B; L) ->
    S w = Lexp_weight (F{ FX}) ->
    S h = n1 + n2 -> L =mul= M1 ++ M2 ->
    n1 |~> 0; B; F{ FX} :: M1 ->
                 n2 |~> 0; B; (F{ FX})° :: M2 ->
                              exists m, m |~> 0 ; B; L.
  Proof. 
    intros H H0 Hw Hh P Hn1 Hn2.
    inversion Hn1; subst; inversion Hh; try cut_free.
    * apply resolvers in H1; firstorder; lexp_contr H1.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2; top_commutes.
    * simpl_cases2.
      refine (tab_bot H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_par H0 _ _ P H1 H3 H2 Hn1 Hn2); auto.
    * simpl_cases2. 
      refine (tab_tensor H0 _ _ P H1 H2 H3 H5 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus1 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_plus2 H0 _ _ P H1 H3 H2 Hn1 Hn2); auto. 
    * simpl_cases2.
      refine (tab_with H0 _ _ P _ _ H3 H5 Hn1 Hn2); auto.
    * refine (tab_copy H0 _ _ P H1 H2 H3 Hn1 Hn2); auto.
    * simpl_cases2.
      refine (tab_quest H0 _ _ P _ H3 H2 Hn1 Hn2); auto.
    * apply resolvers2 in H1; firstorder; lexp_contr H1.
    * simpl_cases2.  
      refine (tab_ex H0 _ Hw P H1 H3 H2 Hn1 Hn2).
      omega.
    * {
        destruct (FEqDec (F{ FX}) (F{ FX0}) ).
        rewrite e in *. clear e.
        simpl_cases4. (*  rewrite dEx in Hn2. *)
        inversion Hn2; subst; inversion Hh; try cut_free.
        - apply resolvers in H3; firstorder; lexp_contr H3.
        - apply resolvers2 in H3; firstorder; lexp_contr H3.
        - simpl_cases2; top_commutes.  
        - simpl_cases2. organizer.
          refine (tab_bot _ _ Hw P H3 H4 H5 Hn2 _); eauto.  
          omega.
        - simpl_cases2. organizer.
          refine (tab_par _ _ Hw P H3 H4 H5 Hn2 _); eauto. omega.
        - simpl_cases2. organizer.
          refine (tab_tensor H0 _ Hw P H3 H4 H6 H8 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_plus1 _ _ Hw P H3 H4 H5 Hn2 _); eauto. omega.
        - simpl_cases2.
          organizer.
          refine (tab_plus2 _ _ Hw P H3 H4 H5 Hn2 _); eauto. omega.
        - simpl_cases2. organizer.
          refine (tab_with H0 _ Hw P H3 H4 H6 H8 Hn2 Hn1). omega.
        - simpl_cases2.
          organizer.
          refine (tab_copy _ _ Hw P H3 H5 H6 Hn2 _); eauto. omega.
        - simpl_cases2.
          organizer.
          refine (tab_quest _ _ Hw P H3 H4 H5 Hn2 _); eauto. omega.
        - apply resolvers2 in H3; firstorder.
          lexp_contr H3.
        - 
          destruct (FEqDec (F{ FX0})° (E{ FX1})).
          -- rewrite e in H3.
             simpl_cases4.
             assert (n |~> 0; B; Subst FX0 t :: M) by auto.
             assert (Subst FX0 t = (Subst FX1 t)°) by solve [apply SubsDual'; auto].
             rewrite H6 in H4.
             rewrite H1, H3 in *.
             rewrite union_comm in P.
             eapply H.
             
             2: {
               change (0%nat) with (0+0).
               refine (sig3_cut _ _ P H5 H4); auto.
               }
             eapply WeightFE; eauto.
          -- simpl_cases2. organizer.
             refine (tab_ex H0 _ Hw P H3 H4 H5 Hn2 Hn1 ). omega.
        - simpl_cases2. 
          organizer.
          refine (tab_fx H0 _ Hw P H3 H4 _ Hn2 Hn1); auto. omega. 
        - simpl_cases2. 
          refine (tab_fx H0 _ Hw P H1 H3 _ Hn1 Hn2); auto. 
      }        
  Qed.

  Arguments aux_CUT_fe [n1 n2 w h B L FX M1 M2].
End CCases.
