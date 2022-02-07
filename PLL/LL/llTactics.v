
(* This file is part of the Linear Logic  formalization in Coq: https://github.com/brunofx86/LL *)

(** ** Tactics
Some tactics to automatize part of the proofs. 
 *)
Require Export LL.MetaTheory.StructuralRules.
Require Export Coq.Init.Logic.
Require Export Coq.Arith.Wf_nat.
Require Export Coq.Program.Equality.
Require Export Coq.Arith.PeanoNat.
Require Export Lia.
Export ListNotations.
Set Implicit Arguments.

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
    (destruct H as [He Hm]);
    inversion He
  | [ H : [?b] =mul= ?a :: ?M1 |- _ ] => 
    symmetry in H; simpl_cases0 
  | [ H : [?a] =mul= [?b] |- _ ] => 
    apply resolvers3 in H;
    inversion H     
  end.

Ltac simpl_cases1 := 
  match goal with
  | [ H : ?a :: ?M1 =mul= [?b ; ?c] |- _ ] => 
    apply resolvers in H;
    destruct H as [Hb|Hc];[
      inversion Hb|
      inversion Hc]
  end.

Ltac simpl_cases2 := 
  repeat
    match goal with
    | [ H' : ?b <> ?a, H : ?a :: ?M1 =mul= ?b :: ?M  |- _ ] => 
      assert (exists L, M  =mul= a :: L /\  M1 =mul= b :: L) 
        by solve [apply seconda_sec'; auto]
      ; clear H; clear H' 
    | [ H : ?a :: ?M1 =mul= ?b :: ?M  |- _ ] => 
      assert (exists L, M  =mul= a :: L /\  M1 =mul= b :: L) 
        by solve [apply seconda_sec'; [intro Hsec; inversion Hsec | auto]]
      ; clear H  
    | [ H : ex _ |- _ ] =>  
      destruct H    
    | [ H : _ /\ _ |- _ ] => 
      destruct H    
    end.

(* Ltac simpl_cases3 := 
repeat
match goal with
  | [ H : ?a :: ?L =mul= [?a] |- _ ] => 
    apply union_empty in H; rewrite H in *; clear H 
end.
 *)
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
      destruct Hten2 as [L2 HL2]; rewrite union_comm_app in H0;
      assert (x =mul= M ++ L2) by solve [eapply solsls2; eauto]; rewrite union_comm_app in H0
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
    apply member_unit in H1; inversion H1
  | [ H : (?v ⁻) <> (?A ⁻), H1: ?v ⁻ :: ?M1 =mul= [?A ⁻; ?A ⁺] |- _ ] => 
    change ( v ⁻ :: M1) with ([v ⁻] ++ M1) in H1; apply meq_cons_In in H1; 
    apply member_due in H1; auto; 
    apply member_unit in H1; inversion H1
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
    destruct (eq_dec (v) (A ⁺))
  | [  H: ?v :: ?M1 =mul= [?A ⁻; ?A ⁺] |- _ ] => 
    destruct (eq_dec (v) (A ⁻))
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

Lemma tab_top_left L B M1 M2 T:
  L =mul= M1 ++ M2 -> 
  M1 =mul= ⊤ :: T -> exists m, m |~> 0; B; L.
Proof.
  intros P H.
  rewrite H in P;
    change ((⊤ :: T) ++ M1) with (⊤ :: (T ++ M1)) in P.
  eexists; refine (sig3_top _ P).
Qed.

Lemma tab_top_right L B M1 M2 T:
  L =mul= M1 ++ M2 -> 
  M2 =mul= ⊤ :: T -> exists m, m |~> 0; B; L.
Proof.
  intros P H.
  rewrite union_comm_app in P.
  rewrite H in P;
    change ((⊤ :: T) ++ M1) with (⊤ :: (T ++ M1)) in P.  
  eexists; refine (sig3_top _ P).
Qed.


Ltac top_commutes :=
  match goal with
  | [  
    P : ?L =mul= ?M1 ++ ?M2,
        H : ?M1 =mul= ⊤ :: ?x |- _ ] => 
    refine (tab_top_left _ _ P H)
  | [  
    P : ?L =mul= ?M1 ++ ?M2,
        H : ?M2 =mul= ⊤ :: ?x |- _ ] =>  
    refine (tab_top_right _ _ P H)
  end.

(* Ltac very_easy := start_proof;
      try simpl_cases0;
      try broken; try solve_cont;
      try simpl_cases2;
      try top_commutes; try simpl_cases0.
 *)

Lemma tab_bot_left L B M1 M2 M T h w n1 n2 a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  S w = lexp_weight a ->
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
Arguments tab_bot_left[L B M1 M2 M T h w n1 n2 a].

Lemma tab_bot_left_zero L B M1 M2 M T h n1 n2 a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  0%nat = lexp_weight a ->
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
Arguments tab_bot_left_zero [L B M1 M2 M T h n1 n2 a].

Lemma tab_bot_right_zero L B M1 M2 M T h n a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  L =mul= M1 ++ M2 -> 
  h = n ->
  0%nat = lexp_weight a ->
  M =mul= a° :: T ->
  M2 =mul= ⊥ :: T ->  
  n |~> 0 ; B; M -> 
               0 |~> 0 ; B; a :: M1 ->
                            S n |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
Proof.
  intros HI PL Hhei Hwei PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; M1 ++ T) as Hyp.
  rewrite PM in H.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0);
        refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite].
  resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_bot _ Ht); auto; try resolve_rewrite.  
Qed.
Arguments tab_bot_right_zero [L B M1 M2 M T h n a].

Lemma tab_bot_right L B M1 M2 M T n1 n2 n3 F G a:
  (forall m,
      m <= max n2 n1 + S n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight F + lexp_weight G); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  L =mul= M1 ++ M2 -> 
  S (lexp_weight F + lexp_weight G) = lexp_weight a ->
  M =mul= a° :: T ->
  M2 =mul= ⊥ :: T ->  
  n3 |~> 0 ; B; M -> 
                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                         S n3 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
Proof.
  intros HI PL Hwei PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; M1 ++ T) as Hyp.
  rewrite PM in H.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0);
        refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite].
  resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_bot _ Ht); auto; try resolve_rewrite.  
Qed.
Arguments tab_bot_right [L B M1 M2 M T n1 n2 n3 F G a].

Lemma tab_bot_right_unit' L B M1 M2 M T n1 n2 a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  L =mul= M1 ++ M2 -> 
  0%nat = lexp_weight a ->
  M =mul= a° :: T ->
  M2 =mul= ⊥ :: T ->  
  n2 |~> 0 ; B; M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
Proof.
  intros HI PL Hwei PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; M1 ++ T) as Hyp.
  rewrite PM in H.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0);
        refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite].
  resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_bot _ Ht); auto; try resolve_rewrite.  
Qed.

Arguments tab_bot_right_unit' [L B M1 M2 M T n1 n2 a].

Lemma tab_bot_right_unit L B M1 M2 M T n1 n2 F a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight F); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  L =mul= M1 ++ M2 -> 
  S (lexp_weight F) = lexp_weight a ->
  M =mul= a° :: T ->
  M2 =mul= ⊥ :: T ->  
  n2 |~> 0 ; B; M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
Proof.
  intros HI PL Hwei PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; M1 ++ T) as Hyp.
  rewrite PM in H.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0);
        refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite].
  resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_bot _ Ht); auto; try resolve_rewrite. 
Qed.
Arguments tab_bot_right_unit [L B M1 M2 M T n1 n2 F a].

(*
Lemma tab_bot_right' L B M1 M2 M T n1 n2 F G a:
(forall m,
    m <= n1 + S n2 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight F + lexp_weight G); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  L =mul= M1 ++ M2 -> 
  S (lexp_weight F + lexp_weight G) = lexp_weight a ->
  M =mul= a° :: T ->
  M2 =mul= ⊥ :: T ->  
  n2 |~> 0 ; B; M -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S n2 |~> 0 ; B; a° :: M2 -> exists m, m |~> 0; B; L.
Proof.
  intros HI PL Hwei PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; M1 ++ T) as Hyp.
  rewrite PM in H.
  refine (HI _ _ _ _ _ _);
   [ | change (0%nat) with (plus 0 0);
       refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite].
   resolve_max.
    destruct Hyp as [t Ht];
  eexists;
  refine (sig3_bot _ Ht); auto; try resolve_rewrite.  
Qed.

Ltac bot_commutes:=
match goal with
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> ?c1 ; ?B; ?M,
      Hn2 : ?n0' |~> ?c2 ; ?B; {{?a}} U ?M2,
      Hn1 : ?n' |~> ?c1 ; ?B; {{?b}} U ?M1,
      H0 : ?M =mul= {{?b}} U ?x0,
      H4 : ?M1 =mul= {{⊥}} U ?x0 |- _ ] =>  
      solve [refine (tab_bot_left _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max; try lia]
 | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> ?c2 ; ?B; ?M,
      Hn2 : ?n0' |~> ?c2 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> ?c1 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?b}} U ?x0,
      H4 : ?M2 =mul= {{⊥}} U ?x0  |- _ ] =>  
      solve [refine (tab_bot_right _ _ _ _ _ P _ _ H4 H1 Hn1 Hn2); eauto; resolve_max; try lia]  end.
 *)

Lemma union_rotate_cons a b c M : (a :: b :: c :: M) =mul= (c :: a :: b :: M).
Proof. change ((a :: b :: c :: M) =mul= (c :: a :: b :: M)) with 
       (([a] ++ [b] ++ [c] ++ M) =mul= ([c] ++ [a] ++ [b] ++ M)). solve_meq. Qed.

Lemma tab_par_left_zero L B M1 M2 M T h  n1 n2 F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  0%nat = lexp_weight a ->
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

Lemma tab_par_left L B M1 M2 M T h w n1 n2 F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  S w = lexp_weight a ->
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
Arguments tab_par_left [L B M1 M2 M T h w n1 n2 F G a].

Lemma tab_par_right_zero L B M1 M2 M T h n F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  h = n ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F $ G) :: T ->  
  n |~> 0 ; B; F :: G :: M -> 
               0 |~> 0 ; B; a :: M1 ->
                            S n |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M1)) as Hyp.
  change (F :: G :: M) with ([F] ++ [G] ++ M) in H.
  change (a° :: T) with ([a°] ++ T) in PM. 
  rewrite union_assoc_app in H.
  rewrite union_comm_app in H. 
  rewrite PM in H.
  rewrite <- union_assoc_app in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
    resolve_max.
  app_normalize_aux.
  rewrite <- (my_p _ _ _ M1).
  solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_par _ Ht); auto;
      resolve_rewrite.
Qed.


(*
Lemma tab_par_right L B M1 M2 M T n1 n2 n3 F G a:
(forall m,
    m <= max n2 n1 + S n3 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight F + lexp_weight G); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight F + lexp_weight G) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F $ G):: T ->  
  n3 |~> 0 ; B; F :: G :: M -> 
  S (max n2 n1) |~> 0 ; B; a :: M1 ->
  S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M1)) as Hyp.
  rewrite union_comm in H;
  rewrite PM in H;
  try rewrite union_assoc_app in H. 
      refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_par _ Ht); auto;
  resolve_rewrite.
Qed.
Arguments tab_par_right [L B M1 M2 M T n1 n2 n3 F G a].
 *)

Lemma tab_par_right' L B M1 M2 M T n1 n2 F1 F2 F G a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight F1 + lexp_weight F2); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight F1 + lexp_weight F2) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F $ G):: T ->  
  n2 |~> 0 ; B; F :: G :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite union_rotate_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite]. 
  resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_par _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_par_right' [L B M1 M2 M T n1 n2 F1 F2 F G a].

Lemma tab_par_right_unit' L B M1 M2 M T n1 n2 F G a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F $ G):: T ->  
  n2 |~> 0 ; B; F :: G :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite union_rotate_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
    resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_par _ Ht); auto;
      resolve_rewrite.  
Qed.
Arguments tab_par_right_unit' [L B M1 M2 M T n1 n2 F G a].

Lemma tab_par_right_unit L B M1 M2 M T n1 n2 F1 F G a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight F1); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight F1) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F $ G):: T ->  
  n2 |~> 0 ; B; F :: G :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite union_rotate_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
    resolve_max.  solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_par _ Ht); auto;
      resolve_rewrite.   
Qed.
Arguments tab_par_right_unit [L B M1 M2 M T n1 n2 F1 F G a].
(*
Ltac par_commutes :=
match goal with
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; ?B; ({{?F}} U {{?G}}) U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?a}} U ?x0,
      H4 : ?M1 =mul= {{?F $ ?G}} U ?x0 |- _ ] =>  
      solve [refine (tab_par_left _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max; try lia]   
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; ?B; ({{?F}} U {{?G}}) U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?b}} U ?x0,
      H4 : ?M2 =mul= {{?F $ ?G}} U ?x0 |- _ ] =>  
      solve [refine (tab_par_right _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max; try lia] 
        end.
 *)
Lemma tab_plus1_left_zero L B M1 M2 M T h n1 n2 F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  0%nat = lexp_weight a ->
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
  resolve_rewrite; eauto.
Qed.
Arguments tab_plus1_left_zero [L B M1 M2 M T h n1 n2 F G a].

Lemma tab_plus1_left L B M1 M2 M T h w n1 n2 F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  S w = lexp_weight a ->
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
  resolve_rewrite; eauto.
Qed.
Arguments  tab_plus1_left [L B M1 M2 M T h w n1 n2 F G a].

Lemma tab_plus1_right_zero L B M1 M2 M T h n F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = n ->  
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n |~> 0 ; B; F :: M -> 
               0 |~> 0 ; B; a :: M1 ->
                            S n |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (T ++ M1)) as Hyp.

  rewrite PM in H.
  rewrite meq_swap in H; auto.

  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max.
  solve_permutation.

  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus1 _ Ht); auto.
  resolve_rewrite; eauto.
Qed.
Arguments tab_plus1_right_zero [L B M1 M2 M T h n F G a].

Lemma tab_plus1_right L B M1 M2 M T n1 n2 n3 F G I J a:
  (forall m,
      m <= max n2 n1 + S n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n3 |~> 0 ; B; F :: M -> 
                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                         S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (T ++ M1)) as Hyp.

  rewrite PM in H.
  rewrite meq_swap in H; auto.

  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max.
  solve_permutation.

  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus1 _ Ht); auto.
  resolve_rewrite; eauto.
Qed.
Arguments tab_plus1_right [L B M1 M2 M T n1 n2 n3 F G I J a].
(*
Lemma tab_plus1_right' L B M1 M2 M T n1 n2 F G I J a:
(forall m,
    m <= n1 + S n2 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; {{F}} U (T U M1)) as Hyp.
  rewrite union_comm in H;
  rewrite PM in H;
  try rewrite union_assoc_app in H. 
      refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); 
         refine (sig3_cut _ _ _ Hn1 H); auto; 
         resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_plus1 _ Ht); auto;
  resolve_rewrite.
Qed.
 *)

Lemma tab_plus1_right_unit' L B M1 M2 M T n1 n2 F G a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (T ++ M1)) as Hyp.

  rewrite PM in H.
  rewrite meq_swap in H; auto.

  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max.
  solve_permutation.

  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus1 _ Ht); auto.
  resolve_rewrite; eauto.
Qed.

Arguments tab_plus1_right_unit' [L B M1 M2 M T n1 n2 F G a].

Lemma tab_plus1_right_unit L B M1 M2 M T n1 n2 F G I a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (T ++ M1)) as Hyp.

  rewrite PM in H.
  rewrite meq_swap in H; auto.

  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max.
  solve_permutation.

  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus1 _ Ht); auto.
  resolve_rewrite; eauto.
Qed.
Arguments tab_plus1_right_unit [L B M1 M2 M T n1 n2 F G I a].
(*
Ltac plus1_commutes :=
match goal with
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; ?B; {{?F}} U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?a}} U ?x0,
      H4 : ?M1 =mul= {{?F ⊕ ?G}} U ?x0 |- _ ] =>  
      solve [refine (tab_plus1_left _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max; try lia]   
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; ?B; {{?F}} U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?b}} U ?x0,
      H4 : ?M2 =mul= {{?F ⊕ ?G}} U ?x0 |- _ ] =>  
      solve [refine (tab_plus1_right _ _ _ _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max; try lia] 
        end.
 *)

Lemma tab_plus2_left_zero L B M1 M2 M T h n1 n2 F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  0%nat = lexp_weight a ->
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
Arguments tab_plus2_left_zero [L B M1 M2 M T h n1 n2 F G a].

Lemma tab_plus2_left L B M1 M2 M T h w n1 n2 F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  S w = lexp_weight a ->
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
Arguments tab_plus2_left [L B M1 M2 M T h w n1 n2 F G a]. 

Lemma tab_plus2_right_zero L B M1 M2 M T h n F G a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = n ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n |~> 0 ; B; G :: M -> 
               0 |~> 0 ; B; a :: M1 ->
                            S n |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite meq_swap_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus2 _ Ht); auto;
      resolve_rewrite; eauto.
Qed.
Arguments tab_plus2_right_zero [L B M1 M2 M T h n F G a].

Lemma tab_plus2_right L B M1 M2 M T n1 n2 n3 F G I J a:
  (forall m,
      m <= max n2 n1 + S n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n3 |~> 0 ; B; G :: M -> 
                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                         S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite meq_swap_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus2 _ Ht); auto;
      resolve_rewrite; eauto.
Qed.
Arguments tab_plus2_right [L B M1 M2 M T n1 n2 n3 F G I J a].
(*
Lemma tab_plus2_right' L B M1 M2 M T n1 n2 F G I J a:
(forall m,
    m <= n1 + S n2 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n2 |~> 0 ; B; G :: M -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; {{G}} U (T U M1)) as Hyp.
  rewrite union_comm in H;
  rewrite PM in H;
  try rewrite union_assoc_app in H. 
      refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); 
         refine (sig3_cut _ _ _ Hn1 H); auto; 
         resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_plus2 _ Ht); auto;
  resolve_rewrite.
Qed.
 *)
Lemma tab_plus2_right_unit' L B M1 M2 M T n1 n2 F G a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n2 |~> 0 ; B; G :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.  
  assert (exists m, m |~> 0 ; B; G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite meq_swap_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus2 _ Ht); auto;
      resolve_rewrite; eauto.
Qed.
Arguments tab_plus2_right_unit' [L B M1 M2 M T n1 n2 F G a].

Lemma tab_plus2_right_unit L B M1 M2 M T n1 n2 F G I a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F ⊕ G) :: T ->  
  n2 |~> 0 ; B; G :: M -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; G :: (T ++ M1)) as Hyp.
  rewrite PM in H.
  rewrite meq_swap_cons in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); auto; 
        resolve_rewrite];
    resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_plus2 _ Ht); auto;
      resolve_rewrite; eauto.
Qed.
Arguments tab_plus2_right_unit [L B M1 M2 M T n1 n2 F G I a].
(*
Ltac plus2_commutes :=
match goal with
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; ?B; {{?G}} U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?a}} U ?x0,
      H4 : ?M1 =mul= {{?F ⊕ ?G}} U ?x0 |- _ ] =>  
      solve [refine (tab_plus2_left _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max;  try lia]   
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; ?B; {{?G}} U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?b}} U ?x0,
      H4 : ?M2 =mul= {{?F ⊕ ?G}} U ?x0 |- _ ] =>  
      solve [refine (tab_plus2_right _ _ _ _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max;  try lia] 
        end.
 *)
Lemma tab_quest_left_zero L B M1 M2 M T h n1 n2 F a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  0%nat = lexp_weight a ->
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
    rewrite union_comm_app in Hn2.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_quest _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_quest_left_zero [L B M1 M2 M T h n1 n2 F a].

Lemma tab_quest_left L B M1 M2 M T h w n1 n2 F a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  S w = lexp_weight a ->
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
    rewrite union_comm_app in Hn2.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H Hn2); auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_quest _ Ht); auto;
      resolve_rewrite.  
Qed.
Arguments tab_quest_left [L B M1 M2 M T h w n1 n2 F a].

Lemma tab_quest_right_zero L B M1 M2 M T h n F a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = n ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (? F) :: T ->  
  n |~> 0 ; F :: B; M -> 
                    0 |~> 0 ; B; a :: M1 ->
                                 S n |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Hhei Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; F :: B ; M1 ++ T) as Hyp.
  rewrite PM in H; 
    eapply height_preserving_weakning_sig3 with (D:=[F]) in Hn1;
    rewrite union_comm_app in Hn1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_quest _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_quest_right_zero [L B M1 M2 M T h n F a].

Lemma tab_quest_right L B M1 M2 M T n1 n2 n3 F I J a:
  (forall m,
      m <= max n2 n1 + S n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (? F) :: T ->  
  n3 |~> 0 ; F :: B; M -> 
                     S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                              S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; F :: B ; M1 ++ T) as Hyp.
  rewrite PM in H; 
    eapply height_preserving_weakning_sig3 with (D:=[F]) in Hn1;
    rewrite union_comm_app in Hn1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_quest _ Ht); auto;
      resolve_rewrite.  
Qed.
Arguments tab_quest_right [L B M1 M2 M T n1 n2 n3 F I J a].
(*
Lemma tab_quest_right' L B M1 M2 M T n1 n2 F I J a:
(forall m,
    m <= n1 + S n2 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (? F) :: T ->  
  n2 |~> 0 ; F :: B; M -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; F :: B ; M1 ++ T) as Hyp.
  rewrite PM in H; 
  eapply height_preserving_weakning_sig3 with (D:={{F}}) in Hn1;
  rewrite union_comm in Hn1.
      refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_quest _ Ht); auto;
  resolve_rewrite.
Qed.
 *)
Lemma tab_quest_right_unit' L B M1 M2 M T n1 n2 F a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (? F) :: T ->  
  n2 |~> 0 ; F :: B; M -> 
                     S n1 |~> 0 ; B; a :: M1 ->
                                     S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; F :: B ; M1 ++ T) as Hyp.
  rewrite PM in H; 
    eapply height_preserving_weakning_sig3 with (D:=[F]) in Hn1;
    rewrite union_comm_app in Hn1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_quest _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_quest_right_unit' [L B M1 M2 M T n1 n2 F a].

(*
Lemma tab_quest_right_unit L B M1 M2 M T n1 n2 F I a:
(forall m,
    m <= n1 + S n2 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (? F) :: T ->  
  n2 |~> 0 ; F :: B; M -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H Hn1 Hn2.
  assert (exists m, m |~> 0 ; F :: B ; M1 ++ T) as Hyp.
  rewrite PM in H; 
  eapply height_preserving_weakning_sig3 with (D:={{F}}) in Hn1;
  rewrite union_comm in Hn1.
      refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_quest _ Ht); auto;
  resolve_rewrite.
Qed.

Ltac quest_commutes :=
match goal with
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; {{?F}} U ?B; ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?a}} U ?x0,
      H4 : ?M1 =mul= {{Quest ?F}} U ?x0 |- _ ] =>  
      solve [refine (tab_quest_left _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max;  try lia]   
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?n |~> 0 ; {{?F}} U ?B; ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H0 : ?M =mul= {{?b}} U ?x0,
      H4 : ?M2 =mul= {{Quest ?F}} U ?x0 |- _ ] =>  
      solve [refine (tab_quest_right _ _ _ _ _ _ P _ H4 H1 Hn1 Hn2); eauto; resolve_max;  try lia] 
        end.
 *)
Lemma tab_copy_left_zero L L0 B B0 M1 M2 h n1 n2 F a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  0%nat = lexp_weight a ->
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

Arguments tab_copy_left_zero [L L0 B B0 M1 M2 h n1 n2 F a].

Lemma tab_copy_left L L0 B B0 M1 M2 h w n1 n2 F a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S w; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus n1 n2 ->
  S w = lexp_weight a ->
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
Arguments tab_copy_left [L L0 B B0 M1 M2 h w n1 n2 F a].

Lemma tab_copy_right_zero L L0 B B0 M1 M2 h n F a:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = n ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  B =mul= F :: B0 ->
  L0 =mul= F :: a° :: M2 ->
  n |~> 0 ; B; L0 -> 
               0 |~> 0 ; B; a :: M1 ->
                            S n |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Hhei Wei PL PB PP H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B ; F :: L) as Hyp.
  rewrite meq_swap_cons in PP.
  rewrite PP in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); 
        auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_copy _ _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_copy_right_zero [L L0 B B0 M1 M2 h n F a].

Lemma tab_copy_right L L0 B B0 M1 M2 n1 n2 n3 F I J a:
  (forall m,
      m <= max n2 n1 + S n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  B =mul= F :: B0 ->
  L0 =mul= F :: a° :: M2 ->
  n3 |~> 0 ; B; L0 -> 
                S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                         S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PB PP H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B ; F :: L) as Hyp.
  rewrite meq_swap_cons in PP.
  rewrite PP in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); 
        auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_copy _ _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_copy_right [L L0 B B0 M1 M2 n1 n2 n3 F I J a].
(*
Lemma tab_copy_right' L B M1 M2 n1 n2 F I J a:
(forall m,
    m <= n1 + S n2 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  F € B ->
  n2 |~> 0 ; B; {{F}} U (a° :: M2) -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PP H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B ; {{F}} U L) as Hyp.
 rewrite union_perm_left in H.
      refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H); auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_copy _ Ht); auto;
  resolve_rewrite.
Qed.
 *)

Lemma tab_copy_right_unit' L L0 B B0 M1 M2 n1 n2 F a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  B =mul= F :: B0 ->
  L0 =mul= F :: a° :: M2 ->
  n2 |~> 0 ; B; L0 -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PB PP H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B ; F :: L) as Hyp.
  rewrite meq_swap_cons in PP.
  rewrite PP in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); 
        auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_copy _ _ Ht); auto;
      resolve_rewrite.
Qed.
Arguments tab_copy_right_unit' [L L0 B B0 M1 M2 n1 n2 F a].

Lemma tab_copy_right_unit L L0 B B0 M1 M2 n1 n2 F I a:
  (forall m,
      m <= n1 + S n2 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  B =mul= F :: B0 ->
  L0 =mul= F :: a° :: M2 ->
  n2 |~> 0 ; B; L0 -> 
                S n1 |~> 0 ; B; a :: M1 ->
                                S n2 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PB PP H Hn1 Hn2.
  assert (exists m, m |~> 0 ; B ; F :: L) as Hyp.
  rewrite meq_swap_cons in PP.
  rewrite PP in H.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); 
        refine (sig3_cut _ _ _ Hn1 H); 
        auto; try resolve_rewrite];
    resolve_max.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_copy _ _ Ht); auto;
      resolve_rewrite.
Qed.

Arguments tab_copy_right_unit [L L0 B B0 M1 M2 n1 n2 F I a].
(*
Ltac copy_commutes :=
match goal with
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H4 : ?F € ?B,
      H5 : ?n |~> 0 ; ?B;  {{?F}} U ({{?a}} U ?M1),
      Hn2 : ?n' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n0 |~> 0 ;?B; {{?a}} U ?M1 |- _ ] => 
      solve [refine (tab_copy_left _ _ _ P H4 _ Hn1 Hn2); eauto; resolve_max; try lia]   
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H4 : ?F € ?B,
      H5 : ?n |~> 0 ; ?B;  {{?F}} U ({{?b}} U ?M2),
      Hn2 : ?n' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n0 |~> 0 ;?B; {{?a}} U ?M1 |- _ ] => 
      solve [refine (tab_copy_right _ _ _ _ _ _ P H4 _ Hn1 Hn2); eauto; resolve_max; try lia] 
        end. 


Lemma simplHyp n0 n1 n2: n0 + S (max n2 n1) = max n2 n1 + S n0.
Proof.
  resolve_max.
Qed.

Lemma simplHyp2 n0 n1 n2 m0: max n0 m0 + S (max n2 n1) = max n2 n1 + S (max n0 m0).
Proof.
  resolve_max.
Qed.
 *)
Lemma tab_tensor_left_zero' L B M1 M2 M N T n1 n2 n3 F G I J a:
  (forall m,
      m <= max n2 n1 + n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a :: T ->
  M1 =mul= (F ** G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
                n2 |~> 0 ; B; G :: N -> 
                              S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                       n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
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
Arguments tab_tensor_left_zero' [L B M1 M2 M N T n1 n2 n3 F G I J a].

Lemma tab_tensor_left_zero L B M1 M2 M N T n1 n2 n3 F G a:
  (forall m,
      m <= max n2 n1 + n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a :: T ->
  M1 =mul= (F ** G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
                n2 |~> 0 ; B; G :: N -> 
                              S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                       n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
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
Arguments tab_tensor_left_zero [L B M1 M2 M N T n1 n2 n3 F G a].
(*
Lemma tab_tensor_left L B M1 M2 M N T n1 n2 n3 F G I J a:
(forall m,
    m <= max n2 n1 + S n3 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a :: T ->
  M1 =mul= (F ** G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
  n2 |~> 0 ; B; G :: N -> 
  S (max n2 n1) |~> 0 ; B; a :: M1 ->
  S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  simpl_cases_tns.
  
  assert (exists m, m |~> 0 ; B; {{F}} U (L1 U M2)) as Hyp.
  
  rewrite HL1 in H1;
     rewrite union_perm_left in H1.
      refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); 
       auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
  
  assert (exists m, m |~> 0 ; B; {{G}} U (L2 U M2)) as Hyp.
  
  rewrite HL2 in H2;
     rewrite union_perm_left in H2.
      refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H2 Hn2); 
       auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_tensor _ H1 Ht); auto; resolve_rewrite.  
Qed.

Lemma tab_tensor_left' L B M1 M2 M N T n1 n2 n3 F G I a:
(forall m,
    m <= max n2 n1 + S n3 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a :: T ->
  M1 =mul= (F ** G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
  n2 |~> 0 ; B; G :: N -> 
  S (max n2 n1) |~> 0 ; B; a :: M1 ->
  S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  simpl_cases_tns.
  
  assert (exists m, m |~> 0 ; B; {{F}} U (L1 U M2)) as Hyp.
  
  rewrite HL1 in H1;
     rewrite union_perm_left in H1.
      refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); 
       auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
  
  assert (exists m, m |~> 0 ; B; {{G}} U (L2 U M2)) as Hyp.
  
  rewrite HL2 in H2;
     rewrite union_perm_left in H2.
      refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H2 Hn2); 
       auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_tensor _ H1 Ht); auto; resolve_rewrite.  
Qed.
 *)

Lemma tab_tensor_right_zero L B M1 M2 M N T h n1 n2 n3 F G a x:
  (forall m,
      m <= h ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; x; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  h = plus (max n2 n1) n3 ->
  x = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a° :: T ->
  M2 =mul= (F ** G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
                n2 |~> 0 ; B; G :: N -> 
                              n3 |~> 0 ; B; a :: M1 ->
                                            S (max n2 n1) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Hhei Wei PL PM PM1 H1 H2 Hn1 Hn2.
  induction x; induction n3.
  
  * 
    simpl_cases_tns. 
    assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
    
    rewrite HL1 in H1. 
    rewrite meq_swap_cons in H1.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max.
    solve_permutation.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
    
    rewrite HL2 in H2;
      rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max. solve_permutation.
    destruct Hyp as [t Ht];
      eexists.
    refine (sig3_tensor _ H1 Ht); auto. rewrite PL, PM1, H. solve_permutation.
  *
    simpl_cases_tns.
    
    assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
    
    rewrite HL1 in H1;
      rewrite meq_swap_cons in H1.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max. solve_permutation.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
    
    rewrite HL2 in H2;
      rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max. solve_permutation.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ H1 Ht);  auto. rewrite PL, PM1, H. solve_permutation.
  * 
    simpl_cases_tns. 
    assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
    
    rewrite HL1 in H1. 
    rewrite meq_swap_cons in H1.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max.
    solve_permutation.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
    
    rewrite HL2 in H2;
      rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max. solve_permutation.
    destruct Hyp as [t Ht];
      eexists.
    refine (sig3_tensor _ H1 Ht); auto. rewrite PL, PM1, H. solve_permutation.
  *
    simpl_cases_tns.
    
    assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
    
    rewrite HL1 in H1;
      rewrite meq_swap_cons in H1.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max. solve_permutation.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
    
    assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
    
    rewrite HL2 in H2;
      rewrite meq_swap_cons in H2.
    refine (HI _ _ _ _ _ _);
      [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
          auto; try resolve_rewrite].
    rewrite Hhei; resolve_max. solve_permutation.
    destruct Hyp as [t Ht];
      eexists;
      refine (sig3_tensor _ H1 Ht);  auto. rewrite PL, PM1, H. solve_permutation.
Qed. 
Arguments tab_tensor_right_zero [L B M1 M2 M N T h n1 n2 n3 F G a x]. 

Lemma tab_tensor_right L B M1 M2 M N T n1 n2 n3 n4 F G I J a:
  (forall m,
      m <= max n2 n1 + S (max n4 n3) ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a° :: T ->
  M2 =mul= (F ** G) :: T ->  
  n3 |~> 0 ; B; F :: M -> 
                n4 |~> 0 ; B; G :: N -> 
                              S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                       S (max n4 n3) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  simpl_cases_tns. 
  assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
  
  rewrite HL1 in H1. 
  rewrite meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
        auto; try resolve_rewrite].
  resolve_max.
  solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
  
  assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
  
  rewrite HL2 in H2;
    rewrite meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
        auto; try resolve_rewrite].
  resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists.
  refine (sig3_tensor _ H1 Ht); auto. rewrite PL, PM1, H. solve_permutation.
Qed.
Arguments tab_tensor_right [L B M1 M2 M N T n1 n2 n3 n4 F G I J a]. 

(*
Lemma tab_tensor_right' L B M1 M2 M N T n1 n2 n3 F G I J a:
(forall m,
    m <= n1 + S (max n3 n2) ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a° :: T ->
  M2 =mul= (F ** G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
  n3 |~> 0 ; B; G :: N -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S (max n3 n2) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  simpl_cases_tns.
  
  assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
  
  rewrite HL1 in H1;
     rewrite union_perm_left in H1.
      refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
       auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
  
  assert (exists m, m |~> 0 ; B; {{G}} U (L2 U M1)) as Hyp.
  
  rewrite HL2 in H2;
     rewrite union_perm_left in H2.
      refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
       auto; try resolve_rewrite];
     resolve_max.
  destruct Hyp as [t Ht];
  eexists;
  refine (sig3_tensor _ H1 Ht); auto; resolve_rewrite.  
Qed.
 *)
Lemma tab_tensor_right_unit' L B M1 M2 M N T n1 n2 n3 F G a:
  (forall m,
      m <= n1 + S (max n3 n2) ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a° :: T ->
  M2 =mul= (F ** G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
                n3 |~> 0 ; B; G :: N -> 
                              S n1 |~> 0 ; B; a :: M1 ->
                                              S (max n3 n2) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  simpl_cases_tns. 
  assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
  
  rewrite HL1 in H1. 
  rewrite meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
        auto; try resolve_rewrite].
  resolve_max.
  solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
  
  assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
  
  rewrite HL2 in H2;
    rewrite meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
        auto; try resolve_rewrite].
  resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists.
  refine (sig3_tensor _ H1 Ht); auto. rewrite PL, PM1, H. solve_permutation.
Qed.
Arguments tab_tensor_right_unit' [L B M1 M2 M N T n1 n2 n3 F G a].

Lemma tab_tensor_right_unit L B M1 M2 M N T n1 n2 n3 F G I a:
  (forall m,
      m <= n1 + S (max n3 n2) ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M ++ N =mul= a° :: T ->
  M2 =mul= (F ** G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
                n3 |~> 0 ; B; G :: N -> 
                              S n1 |~> 0 ; B; a :: M1 ->
                                              S (max n3 n2) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L.
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  simpl_cases_tns. 
  assert (exists m, m |~> 0 ; B; F :: (L1 ++ M1)) as Hyp.
  
  rewrite HL1 in H1. 
  rewrite meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); 
        auto; try resolve_rewrite].
  resolve_max.
  solve_permutation.
  destruct Hyp as [t Ht];
    eexists;
    refine (sig3_tensor _ Ht H2); auto; resolve_rewrite.
  
  assert (exists m, m |~> 0 ; B; G :: (L2 ++ M1)) as Hyp.
  
  rewrite HL2 in H2;
    rewrite meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _);
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); 
        auto; try resolve_rewrite].
  resolve_max. solve_permutation.
  destruct Hyp as [t Ht];
    eexists.
  refine (sig3_tensor _ H1 Ht); auto. rewrite PL, PM1, H. solve_permutation.
Qed.
Arguments tab_tensor_right_unit [L B M1 M2 M N T n1 n2 n3 F G I a].
(*
Ltac tensor_commutes :=
match goal with
 | [ 
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?m  |~> 0 ; ?B; {{?F}} U ?M,
      H2 : ?n |~> 0 ; ?B; {{?G}} U ?N,
      Hn1 : ?n0' |~> 0 ; ?B; {{?a}} U ?M1,
      Hn2 : ?n' |~> 0 ; ?B; {{?b}} U ?M2,
      H0 : ?M U ?N =mul= {{?a}} U ?x,
      H4 : ?M1 =mul= {{?F ** ?G}} U ?x |- _ ] =>   
      solve [refine (tab_tensor_left _ _ _ _ P _ H4 H1 H2 Hn1 Hn2); eauto; resolve_max;  try lia]   
   | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?m  |~> 0 ; ?B; {{?F}} U ?M,
      H2 : ?n |~> 0 ; ?B; {{?G}} U ?N,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H5 : ?M U ?N =mul= {{?b}} U ?x,
      H4 : ?M2 =mul= {{?F ** ?G}} U ?x |- _ ] =>
      solve [refine (tab_tensor_right _ _ _ _ _ _ P _ H4 H1 H2 Hn1 Hn2); eauto; resolve_max; try lia] 
   end.
 *)
Lemma tab_with_left_zero' L B M1 M2 M T n1 n2 n3 F G I J a:
  (forall m,
      m <= max n2 n1 + n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a :: T ->
  M1 =mul= (F & G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
                n2 |~> 0 ; B; G :: M -> 
                              S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                       n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
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
Arguments tab_with_left_zero' [L B M1 M2 M T n1 n2 n3 F G I J a].

Lemma tab_with_left_zero L B M1 M2 M T n1 n2 n3 F G  a:
  (forall m,
      m <= max n2 n1 + n3 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a :: T ->
  M1 =mul= (F & G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
                n2 |~> 0 ; B; G :: M -> 
                              S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                       n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
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
Arguments tab_with_left_zero [L B M1 M2 M T n1 n2 n3 F G a].
(*      
Lemma tab_with_left L B M1 M2 M T n1 n2 n3 F G I J a:
(forall m,
    m <= max n2 n1 + S n3 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a :: T ->
  M1 =mul= (F & G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
  n2 |~> 0 ; B; G :: M -> 
  S (max n2 n1) |~> 0 ; B; a :: M1 ->
  S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; {{F}} U (M2 U T)) as Hyp1.
  rewrite PM in H1; 
  rewrite union_perm_left in H1.
  refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); auto; 
     try resolve_rewrite; perm_simplify];
     resolve_max.
       
  assert (exists m, m |~> 0 ; B; {{G}} U (M2 U T)) as Hyp2.        
  rewrite PM in H2; rewrite union_perm_left in H2;
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

Lemma tab_with_left' L B M1 M2 M T n1 n2 n3 F G I a:
(forall m,
    m <= max n2 n1 + S n3 ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a :: T ->
  M1 =mul= (F & G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
  n2 |~> 0 ; B; G :: M -> 
  S (max n2 n1) |~> 0 ; B; a :: M1 ->
  S n3 |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; {{F}} U (M2 U T)) as Hyp1.
  rewrite PM in H1; 
  rewrite union_perm_left in H1.
  refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ H1 Hn2); auto; 
     try resolve_rewrite; perm_simplify];
     resolve_max.
       
  assert (exists m, m |~> 0 ; B; {{G}} U (M2 U T)) as Hyp2.        
  rewrite PM in H2; rewrite union_perm_left in H2;
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
 *)

Lemma tab_with_right_zero L B M1 M2 M T n1 n2 F G  a:
  (forall m,
      m <= max n2 n1 ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F & G) :: T ->  
  n1 |~> 0 ; B; F :: M -> 
                n2 |~> 0 ; B; G :: M -> 
                              0 |~> 0 ; B; a :: M1 ->
                                           S (max n2 n1) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (M1 ++ T)) as Hyp1.
  rewrite PM in H1; 
    rewrite  meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); auto; 
        try resolve_rewrite; perm_simplify];
    resolve_max.
  
  assert (exists m, m |~> 0 ; B; G :: (M1 ++ T)) as Hyp2.        
  rewrite PM in H2; 
    rewrite  meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); auto;
        try resolve_rewrite; perm_simplify];
    resolve_max.

  destruct Hyp1 as [t1 Ht1];
    destruct Hyp2 as [t2 Ht2];
    
    eexists;
    refine (sig3_with _ Ht1 Ht2);
    resolve_rewrite.   
Qed.
Arguments tab_with_right_zero [L B M1 M2 M T n1 n2 F G a].

Lemma tab_with_right L B M1 M2 M T n1 n2 n3 n4 F G I J a:
  (forall m,
      m <= max n2 n1 + S (max n4 n3) ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F & G) :: T ->  
  n3 |~> 0 ; B; F :: M -> 
                n4 |~> 0 ; B; G :: M -> 
                              S (max n2 n1) |~> 0 ; B; a :: M1 ->
                                                       S (max n4 n3) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (M1 ++ T)) as Hyp1.
  rewrite PM in H1; 
    rewrite  meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); auto; 
        try resolve_rewrite; perm_simplify];
    resolve_max.
  
  assert (exists m, m |~> 0 ; B; G :: (M1 ++ T)) as Hyp2.        
  rewrite PM in H2; 
    rewrite  meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); auto;
        try resolve_rewrite; perm_simplify];
    resolve_max.

  destruct Hyp1 as [t1 Ht1];
    destruct Hyp2 as [t2 Ht2];
    
    eexists;
    refine (sig3_with _ Ht1 Ht2);
    resolve_rewrite.   
Qed.
Arguments tab_with_right [L B M1 M2 M T n1 n2 n3 n4 F G I J a]. 
(*
Lemma tab_with_right' L B M1 M2 M T n1 n2 n3 F G I J a:
(forall m,
    m <= n1 + S (max n3 n2) ->
    forall (n : nat) (L B : Multiset),
    n ~> 0; S (lexp_weight I + lexp_weight J); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I + lexp_weight J) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F & G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
  n3 |~> 0 ; B; G :: M -> 
  S n1 |~> 0 ; B; a :: M1 ->
  S (max n3 n2) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; {{F}} U (M1 ++ T)) as Hyp1.
  rewrite PM in H1; 
  rewrite union_perm_left in H1.
  refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); auto; 
     try resolve_rewrite; perm_simplify];
     resolve_max.
       
  assert (exists m, m |~> 0 ; B; {{G}} U (M1 ++ T)) as Hyp2.        
  rewrite PM in H2; rewrite union_perm_left in H2;
  refine (HI _ _ _ _ _ _); 
     [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); auto;
     try resolve_rewrite; perm_simplify];
     resolve_max.

  destruct Hyp1 as [t1 Ht1];
  destruct Hyp2 as [t2 Ht2];
 
  eexists;
  refine (sig3_with _ Ht1 Ht2);
  resolve_rewrite.   
Qed.
 *)

Lemma tab_with_right_unit' L B M1 M2 M T n1 n2 n3 F G a:
  (forall m,
      m <= n1 + S (max n3 n2) ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; 0; m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  0%nat = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F & G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
                n3 |~> 0 ; B; G :: M -> 
                              S n1 |~> 0 ; B; a :: M1 ->
                                              S (max n3 n2) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (M1 ++ T)) as Hyp1.
  rewrite PM in H1; 
    rewrite  meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); auto; 
        try resolve_rewrite; perm_simplify];
    resolve_max.
  
  assert (exists m, m |~> 0 ; B; G :: (M1 ++ T)) as Hyp2.        
  rewrite PM in H2; 
    rewrite  meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); auto;
        try resolve_rewrite; perm_simplify];
    resolve_max.

  destruct Hyp1 as [t1 Ht1];
    destruct Hyp2 as [t2 Ht2];
    
    eexists;
    refine (sig3_with _ Ht1 Ht2);
    resolve_rewrite.   
Qed.
Arguments tab_with_right_unit' [L B M1 M2 M T n1 n2 n3 F G a].

Lemma tab_with_right_unit L B M1 M2 M T n1 n2 n3 F G I a:
  (forall m,
      m <= n1 + S (max n3 n2) ->
      forall (n : nat) (L B : Multiset),
        n ~> 0; S (lexp_weight I); m; B; L -> exists m0 : nat, m0 |~> 0; B; L) ->
  S (lexp_weight I) = lexp_weight a ->
  L =mul= M1 ++ M2 -> 
  M =mul= a° :: T ->
  M2 =mul= (F & G) :: T ->  
  n2 |~> 0 ; B; F :: M -> 
                n3 |~> 0 ; B; G :: M -> 
                              S n1 |~> 0 ; B; a :: M1 ->
                                              S (max n3 n2) |~> 0 ; B; a° :: M2 -> exists m : nat, m |~> 0; B; L. 
Proof.
  intros HI Wei PL PM PM1 H1 H2 Hn1 Hn2.
  assert (exists m, m |~> 0 ; B; F :: (M1 ++ T)) as Hyp1.
  rewrite PM in H1; 
    rewrite  meq_swap_cons in H1.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H1); auto; 
        try resolve_rewrite; perm_simplify];
    resolve_max.
  
  assert (exists m, m |~> 0 ; B; G :: (M1 ++ T)) as Hyp2.        
  rewrite PM in H2; 
    rewrite  meq_swap_cons in H2.
  refine (HI _ _ _ _ _ _); 
    [ | change (0%nat) with (plus 0 0); refine (sig3_cut _ _ _ Hn1 H2); auto;
        try resolve_rewrite; perm_simplify];
    resolve_max.

  destruct Hyp1 as [t1 Ht1];
    destruct Hyp2 as [t2 Ht2];
    
    eexists;
    refine (sig3_with _ Ht1 Ht2);
    resolve_rewrite.
Qed.
Arguments tab_with_right_unit [L B M1 M2 M T n1 n2 n3 F G I a].
(*
Ltac with_commutes :=
match goal with
 | [ 
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?m |~> 0 ; ?B; {{?F}} U ?M,
      H2 : ?n |~> 0 ; ?B; {{?G}} U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H5 : ?M =mul= {{?a}} U ?x,
      H4 : ?M1 =mul= {{?F & ?G}} U ?x |- _ ] =>   
      solve [refine (tab_with_left _ _ _ _ P _ H4 H1 H2 Hn1 Hn2); eauto; resolve_max;  try lia]   
  | [  
      P : ?L =mul= ?M1 U ?M2,
      H1 : ?m |~> 0 ; ?B; {{?F}} U ?M,
      H2 : ?n |~> 0 ; ?B; {{?G}} U ?M,
      Hn2 : ?n0' |~> 0 ; ?B; {{?b}} U ?M2,
      Hn1 : ?n' |~> 0 ; ?B; {{?a}} U ?M1,
      H5 : ?M =mul= {{?b}} U ?x,
      H4 : ?M2 =mul= {{?F & ?G}} U ?x |- _ ] =>
      solve [refine (tab_with_right _ _ _ _ _ _ P _ H4 H1 H2 Hn1 Hn2); eauto; resolve_max; try lia] 
        end.


Lemma bang_eq : forall x y, eqLExp (! x) (! y) -> eqLExp x y.
Proof.
  intros; auto.
Qed.

Ltac simpl_bangs := 
match goal with
  | [ H :  {{Bang ?a}} U ?M =mul= {{Bang ?b}} |- _ ] => 
    apply resolvers2 in H;
    destruct H as [Hb1 Hb2];
    rewrite Hb2 in *; rewrite nil_union in *; rewrite union_nil in *;
    clear Hb2; apply bang_eq in Hb1; try rewrite <- Hb1 in *; clear Hb1
end. *)
