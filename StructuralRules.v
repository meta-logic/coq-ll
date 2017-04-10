(* This file is part of the Linear Logic  formalization in Coq: https://github.com/brunofx86/LL *)

(** ** Structural Rules

We prove that, for all systems, multiset-equivalent contexts prove the same theorems (exchange rule). We also prove that the classical context admits the usual weakening and contraction rules (preserving the height of the derivation). 

*)
Require Export SequentCalculi.
Require Export Coq.Arith.PeanoNat.
Set Implicit Arguments.

(** *** Simple Lemmas *)

Theorem sig2h_nil: forall n B L,
    n |-- B; L ->  n |-- B; L ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.
Theorem sig2h_cnil: forall n B L,
    n |-- B; L ->  n |-- B ++ [] ; L.
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

Theorem sig2hc_nil: forall n B L,
    n |-c B; L ->  n |-c B; L ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.
Theorem sig2hc_cnil: forall n B L,
    n |-c B; L ->  n |-c B ++ [] ; L.
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

Theorem sig2hcc_nil: forall n B L,
    n |-cc B; L ->  n |-cc B; L ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.
Theorem sig2hcc_cnil: forall n B L,
    n |-cc B; L ->  n |-cc B ++ [] ; L.
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

Theorem sig3_nil: forall n c B L,
    n |~> c ; B; L ->  n |~> c ; B; L ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.
Theorem sig3_cnil: forall n c B L,
    n |~> c ; B; L ->  n |~> c ; B ++ [] ; L.
Proof.
  intros; rewrite app_nil_r; auto.
Qed.
(* End Simple Lemmas *)

Hint Resolve sig2h_nil sig2hc_nil sig2hcc_nil sig3_nil 
              sig2h_cnil sig2hc_cnil sig2hcc_cnil sig3_cnil.
              
(** *** Exchange Rule
*)
Theorem sig2h_exchange: forall n B1 B2 L1 L2, B1 =mul= B2 -> L1 =mul= L2 -> 
    n |-- B1; L1 ->  n |-- B2; L2.
Proof.
  intros.
  rewrite <- H, <- H0; auto.
Qed.

Theorem sig2hc_exchange: forall n B1 B2 L1 L2, B1 =mul= B2 -> L1 =mul= L2 -> 
    n |-c B1; L1 ->  n |-c B2; L2.
Proof.
  intros.
  rewrite <- H, <- H0; auto.
Qed.

Theorem sig2hcc_exchange: forall n B1 B2 L1 L2, B1 =mul= B2 -> L1 =mul= L2 -> 
    n |-cc B1; L1 ->  n |-cc B2; L2.
Proof.
  intros.
  rewrite <- H, <- H0; auto.
Qed.


Theorem sig3_exchange: forall n c B1 B2 L1 L2, B1 =mul= B2 -> L1 =mul= L2 -> 
  n |~> c ; B1 ; L1 ->  n |~> c ; B2 ; L2.
Proof.
  intros.
  rewrite <- H, <- H0; auto.
Qed.

Arguments sig2h_exchange [n B1 B2 L1 L2].
Arguments sig2hc_exchange [n B1 B2 L1 L2].
Arguments sig2hcc_exchange [n B1 B2 L1 L2].
Arguments sig3_exchange [n c B1 B2 L1 L2].

Hint Resolve sig2h_exchange
             sig2hc_exchange
             sig2hcc_exchange
             sig3_exchange : exchanges.
             
(* End LLExchange. *)



(** *** Weakening
*)

Theorem height_preserving_weakning_sig2h: forall n B D L, 
        n |-- B; L -> n |-- B ++ D; L.
Proof.
  induction n as [|n'] using strongind; 
  intros B D L Hsig2h;
  inversion Hsig2h; subst.
  +
  refine (sig2h_init _ H).
  +
  refine (sig2h_one _ H).
  +
  refine (sig2h_top _ H).
  +
  refine (sig2h_bot H1 _); auto. 
  +
  refine (sig2h_par H1 _); auto.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2h_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig2h_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  +
  refine (sig2h_plus1 H1 _).
  apply H with (D:=D); auto.
  +
  refine (sig2h_plus2 H1 _).
  apply H with (D:=D); auto.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2h_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig2h_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  +
  assert (B ++ D =mul= (F :: B0) ++ D) by auto.
  refine (sig2h_copy H0 H2 _).
  apply H with (D:=D); auto.  
  +
  refine (sig2h_quest H1 _).
  assert (F :: B ++ D = (F :: B) ++ D) by auto.
  rewrite H0.
  apply H with (D:=D); auto.   
  +
  refine (sig2h_bang H1 _).
  apply H with (D:=D); auto. 
Qed.

Theorem height_preserving_weakning_sig2h': forall n B L, n |-- []; L -> n |-- B; L.
Proof.
  intros.
  assert (B = [] ++ B ) by auto.
  rewrite H0.
  apply height_preserving_weakning_sig2h; auto.
Qed.

Theorem height_preserving_weakning_sig2hc: forall n B D L, 
        n |-c B; L -> n |-c B ++ D; L.
Proof.
  induction n as [|n'] using strongind; 
  intros B D L Hsig2hc;
  inversion Hsig2hc; subst.
  +
  refine (sig2hc_init _ H).
  +
  refine (sig2hc_one _ H).
  +
  refine (sig2hc_top _ H). 
  +
  refine (sig2hc_bot H1 _); auto. 
  +
  refine (sig2hc_par H1 _); auto.
  +
  refine (sig2hc_cut H1 _ _); auto.
  eapply H with (L:= F :: M); auto.  
  eapply H with (L:=  F° :: N); auto. 
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2hc_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig2hc_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  +
  refine (sig2hc_plus1 H1 _).
  apply H with (D:=D); auto.
  +
  refine (sig2hc_plus2 H1 _).
  apply H with (D:=D); auto.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2hc_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig2hc_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  +
  assert (B ++ D =mul= (F :: B0) ++ D) by auto.
  refine (sig2hc_copy H0 H2 _).
  apply H with (D:=D); auto.  
  +
  refine (sig2hc_quest H1 _).
  assert (F :: B ++ D = (F :: B) ++ D) by auto.
  rewrite H0.
  apply H with (D:=D); auto.    
  +
  refine (sig2hc_bang H1 _).
  apply H with (D:=D); auto. 
Qed.

Theorem height_preserving_weakning_sig2hc': forall n B L, n |-c []; L -> n |-c B; L.
Proof.
  intros.
  assert (B = [] ++ B ) by auto.
  rewrite H0.
  apply height_preserving_weakning_sig2hc; auto.
Qed.

Theorem height_preserving_weakning_sig2hcc: forall n B D L, 
        n |-cc B; L -> n |-cc B ++ D; L.
Proof.
  induction n as [|n'] using strongind; 
  intros B D L Hsig2hcc;
  inversion Hsig2hcc; subst.
  +
  refine (sig2hcc_init _ H).
  +
  refine (sig2hcc_one _ H).
  +
  refine (sig2hcc_top _ H). 
  +
  refine (sig2hcc_bot H1 _); auto. 
  +
  refine (sig2hcc_par H1 _); auto.
  +
  refine (sig2hcc_cut H1 _ _); auto.
  eapply H with (L:= F :: M); auto. 
  eapply H with (L:= F° :: N); auto. 
  
  +
  refine (sig2hcc_ccut H1 _ _).
  eapply H with (L:= (! F) :: M); auto.
  change (F° :: B ++ D) with ( (F° :: B) ++ D).
  eapply H; auto.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2hcc_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig2hcc_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  +
  refine (sig2hcc_plus1 H1 _).
  apply H with (D:=D); auto.
  +
  refine (sig2hcc_plus2 H1 _).
  apply H with (D:=D); auto.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2hcc_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig2hcc_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  +
  assert (B ++ D =mul= (F :: B0) ++ D) by auto.
  refine (sig2hcc_copy H0 H2 _).
  apply H with (D:=D); auto.  
  +
  refine (sig2hcc_quest H1 _).
  assert (F :: B ++ D = (F :: B) ++ D) by auto.
  rewrite H0.
  apply H with (D:=D); auto.    
  +
  refine (sig2hcc_bang H1 _).
  apply H with (D:=D); auto. 
Qed.

Theorem height_preserving_weakning_sig2hcc': forall n B L, n |-cc []; L -> n |-cc B; L.
Proof.
  intros.
  assert (B = [] ++ B ) by auto.
  rewrite H0.
  apply height_preserving_weakning_sig2hcc; auto.
Qed.

Ltac init := 
match goal with
  | [ H : ?L =mul= [?A ⁺; ?A ⁻] |- 0 |~> 0; ?B; ?L ] => eapply sig3_init; eauto
  | [ H : ?L =mul= [?A ⁻; ?A ⁺] |- 0 |~> 0; ?B; ?L ] => eapply sig3_init; eauto
  | [ H : _ |- 0 |~> 0; ?B; [?A ⁺; ?A ⁻] ] => eapply sig3_init; eauto
  | [ H : _ |- 0 |~> 0; ?B; [?A ⁻; ?A ⁺] ] => eapply sig3_init; eauto  
  end.

Ltac one := 
match goal with
  | [ H : ?L =mul= [1] |- 0 |~> 0; ?B; ?L ] => eapply sig3_one; eauto
  | [ H : _ |- 0 |~> 0; ?B; [1] ] => eapply sig3_one; eauto
  end.

Lemma member_top L B: member Top L -> 0 |~> 0; B; L.
Proof.
  intros.
  apply member_then_meq in H.
  destruct H.
  eapply sig3_top; rewrite H; auto.
Qed.

Ltac top := 
try solve [eapply sig3_top; simpl in *; eauto];
match goal with
(*   | [ H : ?L =mul= ⊤ :: ?M |- 0 |~> 0; ?B; ?L ] => eapply sig3_top; eauto
  | [ H : ?L =mul= ?M ++ [⊤] |- 0 |~> 0; ?B; ?L ] => eapply sig3_top; eauto *)
  | [ H : ?L =mul= _ |- 0 |~> 0; ?B; ?L ] => 
        try assert (member Top L) by solve [rewrite H; auto];
        eapply member_top; auto
  | [ H : _ |- 0 |~> 0; ?B; ?L ] => try assert (member Top L) by auto;
        eapply member_top; auto

  end.
  
Ltac bot := 
try solve [eapply sig3_bot; simpl in *; eauto].

Ltac par := 
try solve [eapply sig3_par; simpl in *; eauto].

Ltac plus1 := 
try solve [eapply sig3_plus1; simpl in *; eauto].

Ltac plus2 := 
try solve [eapply sig3_plus2; simpl in *; eauto].

Ltac bang := 
try solve [eapply sig3_bang; simpl in *; eauto].

Theorem height_preserving_weakning_sig3: forall n c B D L, 
        n |~> c ; B; L -> n |~> c ; B ++ D; L.
Proof.
  induction n as [|n'] using strongind; 
  intros c B D L Hsig3;
  inversion Hsig3; subst.
  + init.
  + one.
  + top.
  + bot.
  + par. 
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig3_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
  refine (sig3_tensor H1 _ _);
  apply H with (D:=D); auto;    
  rewrite Hmax; auto.
  + plus1.
  + plus2.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig3_with H1 _ _);
  apply H with (D:=D); auto;    
  rewrite  Hmax; try apply Gt.gt_S_le; auto.
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
  + bang.
    +
    inversion H1; subst;
    eapply sig3_CUT.
    eapply sig3_cut with (F:=F); eauto.
    
    eapply sig3_ccut with (F:=F); eauto.
    change (F° :: B ++ D) with ((F° :: B) ++ D).
    eapply H; auto.
Qed.

Theorem height_preserving_weakning_sig3': forall n c B L, n |~> c ; []; L -> n |~> c ; B; L.
Proof.
  intros.
  assert (B = [] ++ B ) by auto.
  rewrite H0.
  apply height_preserving_weakning_sig3; auto.
Qed.

(* End height_preserving. *)

(*******************************************************************)
(*                   IDEMPOTENCE: CLASSIC SET                      *)
(*******************************************************************)
    
Lemma ClassicalSet : forall n B L F, n |-- F :: B ; L -> n |-- F :: F :: B ; L .
Proof.
  intros.
  change (F :: F :: B) with ([F] ++ F :: B).
  rewrite union_comm_app.
  apply height_preserving_weakning_sig2h.
  auto. 
Qed.
  
Lemma ClassicalSet' : forall n B L F, n |-- F :: F :: B ; L -> n |-- F :: B ; L .
Proof.
  induction n as [|n'] using strongind; 
  intros B L F Hsig2h;
  inversion Hsig2h; subst ;
  [refine (sig2h_init _ H) | refine (sig2h_one _ H) | refine (sig2h_top _ H) | refine (sig2h_bot H1 _); auto | 
  refine (sig2h_par H1 _); auto | | | | | | |  ].
  + 
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2h_tensor H1 _ _);
  apply H ; auto;    
  rewrite  Hmax; try apply gt_S_le; auto.
  refine (sig2h_tensor H1 _ _);
  apply H; auto;    
  rewrite Hmax; auto.
  +
  refine (sig2h_plus1 H1 _).
  apply H; auto.
  +
  refine (sig2h_plus2 H1 _).
  apply H; auto.
  +
  case (Nat.max_spec n m); intros Hmax;
  destruct Hmax as [lt Hmax].
  refine (sig2h_with H1 _ _);
  apply H; auto;    
  rewrite  Hmax; try apply gt_S_le; auto.
  refine (sig2h_with H1 _ _);
  apply H; auto;    
  rewrite Hmax; auto.
  + 
  destruct (LExp_eq_dec F0 F); subst.
  refine (sig2h_copy _ H2 _); auto.
  remember (F :: B) as D.
  assert (exists L, B0 =mul= F :: L /\ D =mul= F0 :: L)
  by solve [apply seconda_sec'; [auto|auto]].
 clear H1.
  repeat destruct H0.
  apply eq_then_meq in HeqD.
  rewrite HeqD in H3. 
  refine (sig2h_copy H1 H2 _).
  rewrite HeqD.
  apply H; auto.   
  +
  refine (sig2h_quest H1 _).
  change (F0 :: F :: B) with ([F0] ++ F :: B).
  rewrite union_comm_app.
  change ((F :: B) ++ [F0]) with (F :: (B ++ [F0])).
  apply H; auto.
  assert (F0 :: F :: F :: B =mul= F :: F :: B ++ [F0]) by
  solve_permutation.
  eapply sig2h_exchange; eauto.
  +
  refine (sig2h_bang H1 _).
  apply H; auto. 
Qed.

