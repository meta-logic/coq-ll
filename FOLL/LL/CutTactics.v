(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Tactics
Some tactics to automatize part of the proof of cut-elimination 
 *)

(*Add LoadPath "../". *)
Require Export LL.SequentCalculiBasicTheory.
Require Export Coq.Init.Logic.
Require Export Coq.Arith.Wf_nat.
Require Export Coq.Program.Equality.
Require Export Coq.Arith.Plus.
Require Export Lia.
Export ListNotations.
Set Implicit Arguments.

#[local] Hint Resolve Nat.le_max_r: core .
#[local] Hint Resolve Nat.le_max_l: core .

Module CTactics (DT : Eqset_dec_pol).
  Module Export Sys :=  SqBasic DT.
  (*Module SLL := SqSystems NatSet.
    Export SLL.*)

  Ltac aux_bases :=
    match goal with
    | [ Hcut : 0%nat = plus ?n1 ?n2 |- _ ] =>
      refine (proj1 (Nat.eq_add_0 _ _) (symmetry Hcut))
    | [ Hcut : plus ?n1 ?n2 = 0%nat |- _ ] =>
      refine (proj1 (Nat.eq_add_0 _ _) Hcut)
    end.

  Ltac simpl_bases :=
    match goal with
    | [ Hcut : 0%nat = plus ?n1 ?n2 |- _ ] => 
      assert (n1 = 0%nat /\ n2 = 0%nat) as n1n2 by aux_bases;
      destruct n1n2 as [n1_0 n2_0]; subst
    | [ Hcut : plus ?n1 ?n2 = 0%nat |- _ ] => 
      assert (n1 = 0%nat /\ n2 = 0%nat) as n1n2 by aux_bases;
      destruct n1n2 as [n1_0 n2_0]; subst
    end.

  Ltac cut_free :=
    simpl_bases;
    match goal with
    | [ H: 0%nat = plus 0 0 |- _ ] => clear H
    | [ H: plus 0 0 = 0%nat |- _ ] => clear H
    end.

  Ltac simpl_cases0 := 
    match goal with
    | [ H : ?a :: ?M1 =mul= [?b] |- _ ] => 
      apply resolvers2 in H;
      let He := fresh "He" in 
      let Hm := fresh "Hm" in   
      (destruct H as [He Hm]); lexp_contr He
    | [ H : [?b] =mul= ?a :: ?M1 |- _ ] => 
      symmetry in H; simpl_cases0 
    | [ H : [?a] =mul= [?b] |- _ ] => 
      apply resolvers3 in H   
    end.

  Ltac simpl_cases1 := 
    match goal with
    | [ H : ?a :: ?M1 =mul= [?b ; ?c] |- _ ] => 
      apply resolvers in H;
      destruct H as [Hb|Hc];[
        lexp_contr Hb|
        lexp_contr Hc]
    end.

  Ltac simpl_cases2 := 
    repeat
      match goal with
      | [ H' : ?a <> ?b, H : ?a :: ?M1 =mul= ?b :: ?M  |- _ ] => 
        assert (exists L, M  =mul= a :: L /\  M1 =mul= b :: L) 
          by solve [apply seconda_sec'; auto]
        ; clear H; clear H' 
      | [ H : ?a :: ?M1 =mul= ?b :: ?M  |- _ ] => 
        assert (exists L, M  =mul= a :: L /\  M1 =mul= b :: L) as Hyp
            by solve [apply seconda_sec'; 
                      [intro Hs; inversion Hs as [Hj]; lexp_contr Hj | auto]]
        ; clear H
      | [ H' : ?a <> ?b, H : ?b :: ?M1 =mul= ?a :: ?M  |- _ ] => 
        symmetry in H
      | [ H : exists x, _ |- _ ] =>  
        destruct H    
      | [ H : _ /\ _ |- _ ] => 
        destruct H    
      end.

  Ltac simpl_cases4 := 
    match goal with
    | [ H : ?a :: ?M1 =mul= ?a :: ?M |- _ ] => 
      apply right_union in H 
    end. 

  Ltac simpl_cases5 := 
    match goal with
    | [ H : [?a] =mul= [?b] |- _ ] => 
      solve [apply se_i3 in H; inversion H]
    end.

  Ltac simpl_cases_tns := 
    match goal with
    | [ P : ?L =mul= ?M1 ++ ?M2,
            H0 : ?M ++ ?N =mul= ?a :: ?x, 
                 H3 : ?T =mul= (?F ** ?G) :: ?x |- _ ] => 
      assert ((exists L1, M =mul= a :: L1) \/ (exists L2, N =mul= a :: L2)) as Hten by 
            solve [eapply solsls; eauto];
      destruct Hten as [Hten1 | Hten2]; 
      [ destruct Hten1 as [L1 HL1]; assert (x =mul= N ++ L1) by solve [eapply solsls2; eauto] | 
        destruct Hten2 as [L2 HL2]; rewrite union_comm in H0;
        assert (x =mul= M ++ L2) by solve [eapply solsls2; eauto]; rewrite union_comm in H0
      ]
    end.


  Ltac normalizeAll :=
    match goal with
    | [ H : ?C ⁻ :: ?L1 =mul= [?A ⁺; ?A ⁻] |- _ ] => 
      rewrite pair_app in H; apply aunion_comm in H      
    end.       

  Ltac solve_cont := 
    match goal with
    | [ H : (?v ⁺) <> (?A ⁺), H1: ?v ⁺ :: ?M1 =mul= [?A ⁺; ?A ⁻] |- _ ] => 
      change ( v ⁺ :: M1) with ([v ⁺] ++ M1) in H1; apply meq_cons_In in H1; 
      apply member_due in H1; auto; 
      apply member_unit in H1; lexp_contr H1
    | [ H : (?v ⁻) <> (?A ⁻), H1: ?v ⁻ :: ?M1 =mul= [?A ⁻; ?A ⁺] |- _ ] => 
      change ( v ⁻ :: M1) with ([v ⁻] ++ M1) in H1; apply meq_cons_In in H1; 
      apply member_due in H1; auto; 
      apply member_unit in H1; lexp_contr H1
    | [ H : (?v ⁺) = (?A ⁺) |- _ ] => subst
    | [ H : (?v ⁻) = (?A ⁻) |- _ ] => subst     
    | [ H : ?A ⁻ :: ?M =mul= [?A ⁻; ?A ⁺] |- _ ] =>  
      apply se_i2 in H; auto; destruct H
    | [ H : ?A ⁺ :: ?M =mul= [?A ⁺; ?A ⁻] |- _ ] =>       
      apply se_i2 in H; auto; destruct H      
    end.    

  Ltac broken := 
    try normalizeAll;
    match goal with
    | [ H : ?v :: ?M1 =mul= [?A ⁺; ?A ⁻] |- _ ] => 
      destruct (eqA_dec (v) (A ⁺))
    | [  H: ?v :: ?M1 =mul= [?A ⁻; ?A ⁺] |- _ ] => 
      destruct (eqA_dec (v) (A ⁻))
    end.  


  (* Ltac cat_jump := 
match goal with
  | [ P : ?L =mul= ?M1 U ?M2, H0 : ?M1 =mul= {{?A ⁻}}, Hn2 : ?n |-- ?B; {{?A ⁻}} U ?M2 |- _ ] => 
     solve [eexists; rewrite P, H0; exact Hn2]  
 end.
   *)

  (************************************************)

  Ltac resolve_rewrite :=
    repeat
      match goal with
      | [ P : ?M =mul= _ |- _ ] => 
        rewrite P; auto; try solve_permutation    
      end.

  Ltac resolve_max :=
    simpl;
    try lia.

  Lemma tab_top L B M1 M2 T:
    L =mul= M1 ++ M2 -> 
    M1 =mul= ⊤ :: T -> exists m, m |~> 0; B; L.
  Proof.
    intros P H.
    rewrite H in P;
      change ((⊤ :: T) ++ M1) with (⊤ :: (T ++ M1)) in P.
    eexists; refine (sig3_top _ P).
  Qed.

  Ltac top_commutes :=
    match goal with
    | [  
      P : ?L =mul= ?M1 ++ ?M2,
          H : ?M1 =mul= ⊤ :: ?x |- _ ] => 
      refine (tab_top _ _ P H)
    | [  
      P : ?L =mul= ?M1 ++ ?M2,
          H : ?M2 =mul= ⊤ :: ?x |- _ ] =>  
      rewrite union_comm in P;
      refine (tab_top _ _ P H)
    end.

  Lemma tab_bot_0 L B M1 M2 M T h n1 n2 a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= ⊥ :: T ->  
    n1 |~> 0 ; B; M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; T ++ M2) as Hyp.
    rewrite PM in H.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0);
          refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite].
    resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_bot _ Ht); auto; try resolve_rewrite.     
  Qed.
  Arguments tab_bot_0 [L B M1 M2 M T h n1 n2 a].

  Lemma tab_bot_S L B M1 M2 M T h w n1 n2 a :
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= ⊥ :: T ->  
    n1 |~> 0 ; B; M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; T ++ M2) as Hyp.
    rewrite PM in H.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0);
          refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite].
    resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_bot _ Ht); auto; try resolve_rewrite.  
  Qed.
  Arguments tab_bot_S [L B M1 M2 M T h w n1 n2 a].

  Lemma tab_bot L B M1 M2 M T h w n1 n2 a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= ⊥ :: T ->  
    n1 |~> 0 ; B; M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_bot_0; eauto.
    - eapply tab_bot_S; eauto.
  Qed.
  Arguments tab_bot [L B M1 M2 M T h w n1 n2 a].

  Lemma union_rotate_cons a b c M : (a :: b :: c :: M) =mul= (c :: a :: b :: M).
  Proof. change ((a :: b :: c :: M) =mul= (c :: a :: b :: M)) with 
             (([a] ++ [b] ++ [c] ++ M) =mul= ([c] ++ [a] ++ [b] ++ M)). solve_meq. Qed.
  
  Lemma tab_par_0 L B M1 M2 M T h  n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F $ G) :: T ->  
    n1 |~> 0 ; B; F :: G :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M2)) as Hyp.
    rewrite PM in H.
    rewrite union_rotate_cons in H.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_par _ Ht); auto;
        resolve_rewrite.
  Qed.
  Arguments  tab_par_0 [L B M1 M2 M T h  n1 n2 F G a].
  
  Lemma tab_par_S L B M1 M2 M T h w n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F $ G):: T ->  
    n1 |~> 0 ; B; F :: G :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M2)) as Hyp.
    rewrite PM in H.
    rewrite union_rotate_cons in H.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_par _ Ht); auto;
        resolve_rewrite.
  Qed.
  Arguments tab_par_S [L B M1 M2 M T h w n1 n2 F G a].

  Lemma tab_par L B M1 M2 M T h w n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F $ G):: T ->  
    n1 |~> 0 ; B; F :: G :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_par_0; eauto.
    - eapply tab_par_S; eauto.
  Qed.
  Arguments tab_par [L B M1 M2 M T h w n1 n2 F G a].

  Lemma tab_plus1_0 L B M1 M2 M T h n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F ⊕ G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; F :: (T ++ M2)) as Hyp.

    rewrite PM in H.
    rewrite meq_swap in H; auto.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); 
          refine (sig3_cut _ _ _ H Hn2); auto; 
          resolve_rewrite];
      resolve_max.

    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_plus1 _ Ht); auto.
    resolve_rewrite. 
  Qed.
  Arguments tab_plus1_0 [L B M1 M2 M T h n1 n2 F G a].
  
  Lemma tab_plus1_S L B M1 M2 M T h w n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F ⊕ G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; F :: (T ++ M2)) as Hyp.

    rewrite PM in H.
    rewrite meq_swap in H; auto.

    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); 
          refine (sig3_cut _ _ _ H Hn2); auto; 
          resolve_rewrite];
      resolve_max.

    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_plus1 _ Ht); auto.
    resolve_rewrite.
  Qed.
  Arguments  tab_plus1_S [L B M1 M2 M T h w n1 n2 F G a].

  Lemma tab_plus1 L B M1 M2 M T h w n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F ⊕ G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_plus1_0; eauto.
    - eapply tab_plus1_S; eauto.
  Qed.
  Arguments tab_plus1 [L B M1 M2 M T h w n1 n2 F G a].

  Lemma tab_plus2_0 L B M1 M2 M T h n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F ⊕ G) :: T ->  
    n1 |~> 0 ; B; G :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; G :: (T ++ M2)) as Hyp.

    rewrite PM in H.
    rewrite meq_swap in H; auto.

    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); 
          auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      eapply sig3_plus2 with (F:=F) (G:=G) (M:=T ++ M2). 
    resolve_rewrite.
    eauto.
  Qed.
  Arguments tab_plus2_0 [L B M1 M2 M T h n1 n2 F G a].
  
  Lemma tab_plus2_S L B M1 M2 M T h w n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F ⊕ G) :: T ->  
    n1 |~> 0 ; B; G :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; G :: (T ++ M2)) as Hyp.

    rewrite PM in H.
    rewrite meq_swap in H; auto.

    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); 
          auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      eapply sig3_plus2 with (F:=F) (G:=G) (M:=T ++ M2). 
    resolve_rewrite.
    eauto.
  Qed.
  Arguments tab_plus2_S [L B M1 M2 M T h w n1 n2 F G a]. 

  Lemma tab_plus2 L B M1 M2 M T h w n1 n2 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F ⊕ G) :: T ->  
    n1 |~> 0 ; B; G :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_plus2_0; eauto.
    - eapply tab_plus2_S; eauto.
  Qed.
  Arguments tab_plus2 [L B M1 M2 M T h w n1 n2 F G a].

  Theorem height_preserving_weakning_sig3: forall n c B D L, 
      n |~> c ; B; L -> n |~> c ; B ++ D; L.
  Proof.
    induction n as [|n'] using strongind; 
      intros c B D L Hsig3;
      inversion Hsig3; subst.
    + eapply sig3_init; eassumption.
    + eapply sig3_one; eassumption.
    + eapply sig3_top; eassumption.
    + eapply sig3_bot; eauto.
    + eapply sig3_par; eauto.
    +
      case (Nat.max_spec n m); intros Hmax;
        destruct Hmax as [lt Hmax].
      refine (sig3_tensor H1 _ _);
        apply H with (D:=D); auto;
          rewrite  Hmax; try apply Nat.succ_le_mono; auto.
      refine (sig3_tensor H1 _ _);
        apply H with (D:=D); auto;
          rewrite Hmax; auto.
    + eapply sig3_plus1; eauto.
    + eapply sig3_plus2; eauto.
    +
      case (Nat.max_spec n m); intros Hmax;
        destruct Hmax as [lt Hmax].
      refine (sig3_with H1 _ _);
        apply H with (D:=D); auto;
          rewrite  Hmax; try apply Nat.succ_le_mono; auto.
      refine (sig3_with H1 _ _);
        apply H with (D:=D); auto;
          rewrite Hmax; auto.
    +
      assert (B ++ D =mul= (F :: B0) ++ D) by auto.
      eapply sig3_copy; eauto.
    +
      assert (F :: B ++ D = (F :: B) ++ D) by auto.
      eapply sig3_quest; eauto.
      rewrite H0; eauto.   
    + eapply sig3_bang; eauto. 
    + eapply sig3_ex; eauto.
    + eapply sig3_fx; eauto.
    +
      inversion H1; subst;
        eapply sig3_CUT.
      eapply sig3_cut with (F:=F); eauto.

      eapply sig3_ccut with (F:=F); eauto.
      change (F° :: B ++ D) with ((F° :: B) ++ D).
      eapply H; auto.
  Qed.

  Theorem sig3_exchange: forall n c B1 B2 L1 L2, B1 =mul= B2 -> L1 =mul= L2 -> 
                                                 n |~> c ; B1 ; L1 ->  n |~> c ; B2 ; L2.
  Proof.
    intros.
    rewrite <- H, <- H0; auto.
  Qed.

  Lemma ClassicalSet : forall n c B L F, 
      n |~> c ; F :: B ; L -> n |~> c ; F :: F :: B ; L.
  Proof.
    intros.
    change (F :: F :: B) with ([F] ++ F :: B).
    rewrite union_comm.
    apply height_preserving_weakning_sig3.
    auto.
  Qed.

  Lemma ClassicalSet' : forall n c B L F, 
      n |~> c ; F :: F :: B ; L -> n |~> c ; F :: B ; L .
  Proof.
    induction n as [|n'] using strongind; 
      intros c B L F Hsig3;
      inversion Hsig3; subst ;
        [refine (sig3_init _ H) | refine (sig3_one _ H) | 
         refine (sig3_top _ H) | refine (sig3_bot H1 _); auto | 
         refine (sig3_par H1 _); auto | | | | | | | | | |].
    + 
      case (Nat.max_spec n m); intros Hmax;
        destruct Hmax as [lt Hmax].
      refine (sig3_tensor H1 _ _);
        apply H ; auto;
          rewrite  Hmax; try apply Nat.succ_le_mono; auto.
      refine (sig3_tensor H1 _ _);
        apply H; auto;
          rewrite Hmax; auto.
    +
      refine (sig3_plus1 H1 _).
      apply H; auto.
    +
      refine (sig3_plus2 H1 _).
      apply H; auto.
    +
      case (Nat.max_spec n m); intros Hmax;
        destruct Hmax as [lt Hmax].
      refine (sig3_with H1 _ _);
        apply H; auto;
          rewrite  Hmax; try apply Nat.succ_le_mono; auto.
      refine (sig3_with H1 _ _);
        apply H; auto;
          rewrite Hmax; auto.
    +
      destruct (FEqDec F0 F); subst.
      refine (sig3_copy _ H2 _); auto.
      remember (F :: B) as D.
      assert (exists L, B0 =mul= F :: L /\ D =mul= F0 :: L)
        by solve [apply seconda_sec'; [auto|auto]].
      clear H1.
      repeat destruct H0.
      apply eq_then_meq in HeqD.
      rewrite HeqD in H3.
      refine (sig3_copy H1 H2 _).
      rewrite HeqD.
      apply H; auto.   
    +
      refine (sig3_quest H1 _).
      change (F0 :: F :: B) with ([F0] ++ F :: B).
      rewrite union_comm.
      change ((F :: B) ++ [F0]) with (F :: (B ++ [F0])).
      apply H; auto.
      assert (F0 :: F :: F :: B =mul= F :: F :: B ++ [F0]) by
          solve_permutation.
      eapply sig3_exchange; eauto; rewrite union_empty; auto.
    +
      refine (sig3_bang H1 _).
      apply H; auto.
    +
      assert (n' |~> c; F :: B; Subst FX t :: M).
      eapply H; auto.
      eapply sig3_ex; eauto.
    +
      assert (forall x : Term, n' |~> c; F :: B; Subst FX x :: M). 
      intro.
      eapply H; auto.
      eapply sig3_fx; eauto.
    +
      inversion H1; subst.
      ++  
        assert (m |~> c1; F :: B; F0 :: M).
        eapply H; auto.
        assert (n |~> c2; F :: B; F0° :: N).
        eapply H; auto.
        eapply sig3_CUT.
        eapply sig3_cut; eauto.   
      ++  
        assert (m |~> c1; F :: B; ! F0 :: M).
        eapply H; auto.
        assert (n |~> c2; F::(F0°::B);  N).
        eapply H; auto.
        rewrite union_rotate_cons; auto.
        eapply sig3_CUT.
        eapply sig3_ccut; eauto.
        rewrite meq_swap; eauto.    
  Qed.

  Lemma tab_quest_0 L B M1 M2 M T h n1 n2 F a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (? F) :: T ->  
    n1 |~> 0 ; F :: B; M -> 
                       S n1 |~> 0 ; B; a :: M1 ->
                                       n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; F :: B ; T ++ M2) as Hyp. rewrite PM in H; 
                                                            eapply height_preserving_weakning_sig3 with (D:=[F]) in Hn2;
                                                            rewrite union_comm in Hn2.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_quest _ Ht); auto;
        resolve_rewrite. 
  Qed.
  Arguments tab_quest_0 [L B M1 M2 M T h n1 n2 F a].
  
  Lemma tab_quest_S L B M1 M2 M T h w n1 n2 F a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (? F) :: T ->  
    n1 |~> 0 ; F :: B; M -> 
                       S n1 |~> 0 ; B; a :: M1 ->
                                       n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; F :: B ; T ++ M2) as Hyp.
    rewrite PM in H; 
      eapply height_preserving_weakning_sig3 with (D:=[F]) in Hn2;
      rewrite union_comm in Hn2.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_quest _ Ht); auto;
        resolve_rewrite. 
  Qed.
  Arguments tab_quest_S [L B M1 M2 M T h w n1 n2 F a].

  Lemma tab_quest L B M1 M2 M T h w n1 n2 F a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (? F) :: T ->  
    n1 |~> 0 ; F :: B; M -> 
                       S n1 |~> 0 ; B; a :: M1 ->
                                       n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
  Proof.
    intros HI Hei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_quest_0; eauto.
    - eapply tab_quest_S; eauto.
  Qed.
  Arguments tab_quest [L B M1 M2 M T h w n1 n2 F a].


  Lemma tab_copy_0 L L0 B B0 M1 M2 h n1 n2 F a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    B =mul= F :: B0 ->
    L0 =mul= F :: (a :: M1) ->
    n1 |~> 0 ; B; L0 -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PB PP H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B ; F :: L) as Hyp.
    rewrite meq_swap_cons in PP.
    rewrite PP in H.  
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_copy _ _ Ht); auto;
        resolve_rewrite.
  Qed.

  Arguments tab_copy_0 [L L0 B B0 M1 M2 h n1 n2 F a].
  
  Lemma tab_copy_S L L0 B B0 M1 M2 h w n1 n2 F a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    B =mul= F :: B0 ->
    L0 =mul= F :: (a :: M1) ->
    n1 |~> 0 ; B; L0 -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PB PP H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B ; F :: L) as Hyp.
    rewrite meq_swap_cons in PP.
    rewrite PP in H.  
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_copy _ _ Ht); auto;
        resolve_rewrite.
  Qed.
  Arguments tab_copy_S [L L0 B B0 M1 M2 h w n1 n2 F a].

  Lemma tab_copy L L0 B B0 M1 M2 h w n1 n2 F a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    B =mul= F :: B0 ->
    L0 =mul= F :: (a :: M1) ->
    n1 |~> 0 ; B; L0 -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PB PP H Hn1 Hn2.
    induction w.
    - eapply tab_copy_0; eauto.
    - eapply tab_copy_S; eauto.
  Qed.
  Arguments tab_copy [L L0 B B0 M1 M2 h w n1 n2 F a].

  Lemma tab_tensor_S L B M1 M2 M N T h n1 n2 n3 w F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h =  plus (max n2 n1) n3 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M ++ N =mul= a :: T ->
    M1 =mul= (F ** G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  n2 |~> 0 ; B; G :: N -> 
                                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                         n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
  Proof.
    intros HI Hh Wei PL PM PM1 H1 H2 Hn1 Hn2.
    simpl_cases_tns.
    
    assert (exists m, m |~> 0 ; B; F :: (L1 ++ M2)) as Hyp.
    
    rewrite HL1 in H1. 
    rewrite meq_swap_cons in H1.

    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); 
          auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M2)) as Hyp.
    
    rewrite HL2 in H2. 
    rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H2 Hn2); 
          auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ H1 Ht); auto; resolve_rewrite.  
  Qed.
  Arguments tab_tensor_S [L B M1 M2 M N T h n1 n2 n3 w F G a].

  Lemma tab_tensor_0 L B M1 M2 M N T h n1 n2 n3 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus (max n2 n1) n3 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M ++ N =mul= a :: T ->
    M1 =mul= (F ** G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  n2 |~> 0 ; B; G :: N -> 
                                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                         n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
  Proof.
    intros HI Hh Wei PL PM PM1 H1 H2 Hn1 Hn2.
    simpl_cases_tns.
    
    assert (exists m, m |~> 0 ; B; F :: (L1 ++ M2)) as Hyp.
    
    rewrite HL1 in H1. 
    rewrite meq_swap_cons in H1.

    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); 
          auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M2)) as Hyp.
    
    rewrite HL2 in H2. 
    rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H2 Hn2); 
          auto; try resolve_rewrite];
      resolve_max.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ H1 Ht); auto; resolve_rewrite.  
  Qed.
  Arguments tab_tensor_0 [L B M1 M2 M N T h n1 n2 n3 F G a].

  Lemma tab_tensor L B M1 M2 M N T h n1 n2 n3 F G w a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus (max n2 n1) n3 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M ++ N =mul= a :: T ->
    M1 =mul= (F ** G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  n2 |~> 0 ; B; G :: N -> 
                                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                         n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
  Proof.
    intros HI Hh Wei PL PM PM1 H1 H2 Hn1 Hn2.
    induction w.
    - eapply tab_tensor_0; eauto.
    - eapply tab_tensor_S; eauto.
  Qed.
  Arguments tab_tensor [L B M1 M2 M N T h n1 n2 n3 F G w a].

  Lemma tab_with_0 L B M1 M2 M T h n1 n2 n3 F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus (max n2 n1) n3 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F & G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  n2 |~> 0 ; B; G :: M -> 
                                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                         n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
  Proof.
    intros HI Hh Wei PL PM PM1 H1 H2 Hn1 Hn2.
    assert (exists m, m |~> 0 ; B; F :: (M2 ++ T)) as Hyp1.
    rewrite PM in H1; 
      rewrite meq_swap_cons in H1.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); auto; 
          try resolve_rewrite; perm_simplify];
      resolve_max.

    assert (exists m, m |~> 0 ; B; G :: (M2 ++ T)) as Hyp2.        
    rewrite PM in H2; rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H2 Hn2); auto;
          try resolve_rewrite; perm_simplify];
      resolve_max.

    destruct Hyp1 as [t1 Ht1];
      destruct Hyp2 as [t2 Ht2];

      eexists;
      refine (sig3_with _ Ht1 Ht2);
      resolve_rewrite; eauto. 
  Qed.
  Arguments tab_with_0 [L B M1 M2 M T h n1 n2 n3 F G a].

  Lemma tab_with_S L B M1 M2 M T h n1 n2 n3 w F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus (max n2 n1) n3 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F & G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  n2 |~> 0 ; B; G :: M -> 
                                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                         n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hh Wei PL PM PM1 H1 H2 Hn1 Hn2.
    
    assert (exists m, m |~> 0 ; B; F :: (T ++ M2)) as Hyp1.
    rewrite PM in H1; 
      rewrite  meq_swap_cons in H1.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); auto; 
          try resolve_rewrite; perm_simplify];
      resolve_max.

    assert (exists m, m |~> 0 ; B; G :: (T ++ M2)) as Hyp2.
    rewrite PM in H2; 
      rewrite  meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H2 Hn2); auto;
          try resolve_rewrite; perm_simplify];
      resolve_max.

    destruct Hyp1 as [t1 Ht1];
      destruct Hyp2 as [t2 Ht2];

      eexists;
      refine (sig3_with _ Ht1 Ht2);
      resolve_rewrite.
  Qed.
  Arguments tab_with_S [L B M1 M2 M T h n1 n2 n3 w F G a]. 

  Lemma tab_with L B M1 M2 M T h n1 n2 n3 w F G a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus (max n2 n1) n3 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= (F & G) :: T ->  
    n1 |~> 0 ; B; F :: M -> 
                  n2 |~> 0 ; B; G :: M -> 
                                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                         n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hh Wei PL PM PM1 H1 H2 Hn1 Hn2.
    induction w.
    - eapply tab_with_0; eauto.
    - eapply tab_with_S; eauto.
  Qed.
  Arguments tab_with [L B M1 M2 M T h n1 n2 n3 w F G a].

  Lemma tab_ex_0 L B M1 M2 M T t h n1 n2 FX a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= E{ FX} :: T ->  
    n1 |~> 0 ; B; Subst FX t :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B ; Subst FX t :: T ++ M2) as Hyp.
    rewrite PM in H.
    rewrite meq_swap_cons in H.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max. 
    destruct Hyp as [p Hp];
      eexists;
      refine (sig3_ex _ Hp); auto;
        resolve_rewrite.
  Qed.
  Arguments tab_ex_0 [L B M1 M2 M T t h n1 n2 FX a].

  Lemma tab_ex_S L B M1 M2 M T t h w n1 n2 FX a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= E{ FX} :: T ->  
    n1 |~> 0 ; B; Subst FX t :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, m |~> 0 ; B ; Subst FX t :: T ++ M2) as Hyp.
    rewrite PM in H.
    rewrite meq_swap_cons in H.
    refine (HI _ _ _ _ _ _); 
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
      resolve_max. 
    destruct Hyp as [p Hp];
      eexists;
      refine (sig3_ex _ Hp); auto;
        resolve_rewrite. Qed.
  Arguments tab_ex_S [L B M1 M2 M T t h w n1 n2 FX a].

  Lemma tab_ex L B M1 M2 M T t h w n1 n2 FX a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= E{ FX} :: T ->  
    n1 |~> 0 ; B; Subst FX t :: M -> 
                  S n1 |~> 0 ; B; a :: M1 ->
                                  n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_ex_0; eauto.
    - eapply tab_ex_S; eauto.
  Qed.
  Arguments tab_ex [L B M1 M2 M T t h w n1 n2 FX a].

  Lemma tab_fx_0 L B M1 M2 M T h n1 n2 FX a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    0%nat = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= F{ FX} :: T ->  
    (forall x : Term, n1 |~> 0; B; [Subst FX x] ++ M )-> 
    S n1 |~> 0 ; B; a :: M1 ->
                    n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, forall y : Term, m |~> 0; B; [Subst FX y] ++ (T++M2)) as Hyp.
    eapply fx_swap_sig3h. intro.
    assert (n1 |~> 0; B; a :: T ++ [Subst FX x] ) as Hy.
    rewrite <- union_perm_left''.
    rewrite union_comm.
    rewrite <- PM. auto.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0);
          refine (sig3_cut _ _ _ Hy Hn2); auto; try resolve_rewrite].
    resolve_max. eauto.
    destruct Hyp as [p Hp];
      
      eexists.
    refine (sig3_fx _ Hp). resolve_rewrite.
  Qed.    
  Arguments tab_fx_0 [L B M1 M2 M T h n1 n2 FX a].

  Lemma tab_fx_S L B M1 M2 M T w h n1 n2 FX a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    S w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= F{ FX} :: T ->  
    (forall x : Term, n1 |~> 0; B; [Subst FX x] ++ M )-> 
    S n1 |~> 0 ; B; a :: M1 ->
                    n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    assert (exists m, forall y : Term, m |~> 0; B; [Subst FX y] ++ (T++M2)) as Hyp.
    eapply fx_swap_sig3h. intro.
    assert (n1 |~> 0; B; a :: T ++ [Subst FX x] ) as Hy.
    rewrite <- union_perm_left''.
    rewrite union_comm.
    rewrite <- PM. auto.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0);
          refine (sig3_cut _ _ _ Hy Hn2); auto; try resolve_rewrite].
    resolve_max. eauto.
    destruct Hyp as [p Hp];
      
      eexists.
    refine (sig3_fx _ Hp). resolve_rewrite.
  Qed.    
  Arguments tab_fx_S [L B M1 M2 M T w h n1 n2 FX a].

  Lemma tab_fx L B M1 M2 M T w h n1 n2 FX a:
    (forall m,
        m <= h ->
        forall (n : nat) (L B : Multiset),
          n ~> 0; w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
    h = plus n1 n2 ->
    w = Lexp_weight a ->
    L =mul= M1 ++ M2 -> 
    M =mul= a :: T ->
    M1 =mul= F{ FX} :: T ->  
    (forall x : Term, n1 |~> 0; B; [Subst FX x] ++ M )-> 
    S n1 |~> 0 ; B; a :: M1 ->
                    n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
  Proof.
    intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
    induction w.
    - eapply tab_fx_0; eauto.
    - eapply tab_fx_S; eauto.
  Qed.
  Arguments tab_fx [L B M1 M2 M T w h n1 n2 FX a].

  Ltac organizer :=
    match goal with
    | [ Hw : ?w = Lexp_weight (?a), 
             P : ?L =mul= ?M1 ++ ?M2,
                 Hn1 : ?n |~> ?c; ?B; ?a :: ?M1 |- _ ] => 
      rewrite (Ng_involutive a) in Hn1;
      rewrite (lweight_dual a) in Hw;
      rewrite union_comm in P  
    | [ P : ?L =mul= ?M1 ++ ?M2,
            Hn1 : ?n |~> ?c; ?B; ?a :: ?M1,
                                 Hn2 : ?n' |~> ?c'; ?B'; ?a' :: ?M2' |- exists m0 : nat, m0 |~> ?d; ?B; ?L ] => 
      rewrite (Ng_involutive a) in Hn1;
      rewrite union_comm in P
    end.
End CTactics.
