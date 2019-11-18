(* This file is part of the Linear Logic  formalization in Coq: https://github.com/brunofx86/LL *)

(** ** Linear Logic Sequent Calculi
We formalize different sequent calculi for Classical Linear Logic: two
sided, one sided and dyadic systems. Some systems also make explicit
the measures (e.g., height of derivation) needed for the
cut-elimination proof.

All the systems internalize the exchange rule. For instance,
the typical rule for [⊤] 
<< 
--------------- ⊤ 
|-- Gamma , ⊤ 
>>

is defined as

[ forall Gamma M, Gamma =mul= {{Top}} U M -> |-- Gamma ]

The considered systems are: 

 - [cls] (notation [D |-- L]): two sided system without cut rule. 
   Structural rules (weakening and contraction)
   are explicit in the system (see e.g., [cls_questc]).

 - [sig1] (notation [|-- L]): one sided system without cut
   rule. Structural rules (weakening and contraction) are explicit in
   the system.

 - [sig2] (notation [|-- B ; L]): dyadic, one sided system without cut
   rule. [B] is the classical context and [L] the
   linear context. There are no structural rules. Those rules are
   proved to be admissible in the classical context (see e.g., Theorem
   [height_preserving_weakning_sig2h]).

 - [sig2h] (notation [n |-- B ; L]): similar to [sig2] but the height
   of the derivation [n] is explicit. This is useful in proofs that
   require induction on the height of the derivation.

 - [sig2hc] (notation [n '|-c' B ';' L]): dyadic, one sided system
   with cut rule.

 - [sig2hcc] (notation [n '|-cc' B ';' L]): adds to [sig2hc] the
   following cut rule (for the classical context)

<<
|-- B; M, !F   |-- B, F° ; N
----------------------------- CCUT
|-- B ; M, N
>>

  - [sig3] (notation [n => c ; B ; L]) : where we make explicit the
    number of times the cut rules (CUT or CCUT) were used in the
    derivation. It makes also explicit the measures used in the proof
    of cut-elimination: height of the cut and complexity of the cut
    formula (see [sig3_cut_general]).

 *)


Require Export Syntax.
Require Export MultisetLL.
Require Export StrongInduction.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Equality.
Require Export List.
Export ListNotations.
Set Implicit Arguments.

Hint Resolve Max.le_max_r Max.le_max_l : core .

(** Dyadic system  (one-sided) *)
Reserved Notation " '|--' B ';' L" (at level 80).
Inductive sig2: list lexp -> list lexp -> Prop :=

| sig2_init : forall B L A, L =mul= (A ⁺) :: [A ⁻] -> |-- B ; L
| sig2_one : forall B L, L =mul= [1] -> |-- B ; L 
| sig2_top : forall B L M, L =mul= Top :: M -> |-- B ; L
| sig2_bot : forall B L M , L =mul= Bot :: M -> |-- B ; M -> |-- B ; L
| sig2_par : forall B L M F G , L =mul= (F $ G) :: M -> |-- B ; F :: G :: M -> |-- B ; L 
| sig2_tensor : forall B L M N F G , 
    L =mul= (F ** G) :: (M ++ N)  ->
    |-- B ; F :: M ->
            |-- B ; G :: N ->  |-- B ; L
| sig2_plus1: forall B L M F G , L =mul= (F ⊕ G) :: M -> |-- B ; F :: M -> |-- B ; L 
| sig2_plus2: forall B L M F G , L =mul= (F ⊕ G) :: M -> |-- B ; G :: M -> |-- B ; L 
| sig2_with: forall B L M F G , 
    L =mul= (F & G) :: M ->
    |-- B ; F :: M ->
            |-- B ; G :: M ->  |-- B ; L
| sig2_copy: forall B D L M F , 
    D =mul= F :: B -> L =mul= F :: M ->
    |-- D ; L -> 
            |-- D ; M 

| sig2_quest: forall B L M F , L =mul= (? F) :: M  ->
                               |-- F :: B ; M -> 
                                            |-- B ; L
                                                      
| sig2_bang: forall B F L , L =mul= [! F] ->
                            |--  B ; [F] ->
                                     |--  B ; L
                                                
where "|-- B ; L" := (sig2 B L).

Lemma sig2_der_compat : forall B1 B2 L1 L2, B1 =mul= B2 -> L1 =mul= L2 -> |-- B1 ; L1 -> |-- B2 ; L2.
Proof.
  intros B1 B2 L1 L2 PB PL H.
  revert dependent B2.
  revert dependent L2.  
  induction H; intros;
    try rewrite PB in *;
    try rewrite PL in *. assert (L =mul= L). reflexivity. rewrite H in PL. 
  eapply sig2_init; eassumption.
  eapply sig2_one; eassumption.
  eapply sig2_top; eassumption.
  assert (|-- B2 ; M) by solve [apply IHsig2; auto].
  eapply sig2_bot; eassumption.
  assert (|-- B2 ; (F :: G :: M)) by solve [apply IHsig2; auto].
  eapply sig2_par; eassumption.
  assert (|-- B2 ; F :: M) by solve [apply IHsig2_1; auto].
  assert (|-- B2 ; G :: N) by solve [apply IHsig2_2; auto].
  eapply sig2_tensor; eassumption.
  assert (|-- B2 ; F :: M) by solve [apply IHsig2; auto]. 
  eapply sig2_plus1; eassumption.
  assert (|-- B2 ; G :: M) by solve [apply IHsig2; auto]. 
  eapply sig2_plus2; eassumption.
  assert (|-- B2 ; F :: M) by solve [apply IHsig2_1; auto].
  assert (|-- B2 ; G :: M) by solve [apply IHsig2_2; auto].
  eapply sig2_with; eassumption.  
  assert (|-- B2 ; L) by solve [apply IHsig2; auto].
  eapply sig2_copy; eassumption.  
  assert (|-- F :: B2; M) by solve [apply IHsig2; auto].
  eapply sig2_quest; eassumption.  
  assert (|-- B2; [F]) by solve [apply IHsig2; auto].
  eapply sig2_bang; eassumption.        
Qed.

Instance sig2_der_morphism :
  Proper (meq ==> meq ==> iff) (sig2).
Proof.
  unfold Proper; unfold respectful. 
  intros B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (sig2_der_compat PB PL H).
  refine (sig2_der_compat (symmetry PB) (symmetry PL) H).
Qed.


(** Dyadic system with explicit heights of derivations *)
Reserved Notation " n '|--' B ';' L" (at level 80).
Inductive sig2h: nat -> list lexp -> list lexp -> Prop :=

| sig2h_init : forall B L A, L =mul= (A ⁺) :: [A ⁻] -> 0 |-- B ; L
| sig2h_one : forall B L, L =mul= [1] -> 0 |-- B ; L 
| sig2h_top : forall B L M, L =mul= Top :: M -> 0 |-- B ; L
| sig2h_bot : forall B L M n, L =mul= Bot :: M -> n |-- B ; M -> S n |-- B ; L
| sig2h_par : forall B L M F G n, L =mul= (F $ G) :: M -> n |-- B ; F :: G :: M -> S n |-- B ; L 
| sig2h_tensor : forall B L M N F G n m, 
    L =mul= (F ** G) :: (M ++ N)  ->
    m |-- B ; F :: M ->
              n |-- B ; G :: N -> S (max n m) |-- B ; L
| sig2h_plus1: forall B L M F G n, L =mul= (F ⊕ G) :: M -> n |-- B ; F :: M -> S n |-- B ; L 
| sig2h_plus2: forall B L M F G n, L =mul= (F ⊕ G) :: M -> n |-- B ; G :: M -> S n |-- B ; L 
| sig2h_with: forall B L M F G n m, 
    L =mul= (F & G) :: M ->
    m |-- B ; F :: M ->
              n |-- B ; G :: M -> S (max n m) |-- B ; L
| sig2h_copy: forall B D L M F n, 
    D =mul= F :: B -> L =mul= F :: M ->
    n |-- D ; L -> 
              S n|-- D ; M 


| sig2h_quest : forall B L M F n, L =mul= (? F) :: M  ->
                                  n |-- F :: B ; M -> 
                                                 S n |-- B ; L
                                                               
| sig2h_bang : forall B F L n, L =mul= [! F] ->
                               n |--  B ; [F] ->
                                          S n |--  B ; L
                                                         
where "n |-- B ; L" := (sig2h n B L).

Lemma sig2h_der_compat : forall n (B1 B2 L1 L2 : list lexp), B1 =mul= B2 -> L1 =mul= L2 -> n |-- B1 ; L1 -> n |-- B2 ; L2.
Proof.
  intros n B1 B2 L1 L2 PB PL H.
  revert L1 L2 PL B1 B2 PB H;
    induction n using strongind; intros.
  - inversion H; subst. 
    +
      refine (sig2h_init _ (transitivity (symmetry PL) H0)). 
    +
      refine (sig2h_one _ (transitivity (symmetry PL) H0)).
    +
      refine (sig2h_top _ (transitivity (symmetry PL) H0)).
  - inversion H0; subst; try rewrite PL in H3; try rewrite PL in H2;
      try rewrite PB in H3; try rewrite PB in H2.
    +
      refine (sig2h_bot H2 _); auto.
      apply H with (L1:= M) (B1:=B1); auto.
    +
      refine (sig2h_par H2 _); auto.
      apply H with (L1:= F :: G :: M) (B1:=B1); auto.
    +
      refine (sig2h_tensor H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: N) (B1:=B1); auto.
    +
      refine (sig2h_plus1 H2 _).
      apply H with (L1:= F :: M) (B1:=B1); auto. 
    +
      refine (sig2h_plus2 H2 _).
      apply H with (L1:= G :: M) (B1:=B1); auto. 
    +
      refine (sig2h_with H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: M) (B1:=B1); auto.
    + 
      refine (sig2h_copy H2 H3 _).   
      apply H with (L1:= L) (B1:=B1); auto. 
    +
      refine (sig2h_quest H2 _).
      apply H with (L1:= M) (B1:= F :: B1); auto. 
    +
      refine (sig2h_bang H2 _).
      apply H with (L1:= [F]) (B1:=B1); auto. 
Qed.

Generalizable All Variables.
Instance sig2h_der_morphism :
  Proper (meq ==> meq ==> iff) (sig2h n).
Proof.
  unfold Proper; unfold respectful. 
  intros n B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (sig2h_der_compat PB PL H).
  refine (sig2h_der_compat (symmetry PB) (symmetry PL) H).
Qed.

(** Dyadic system + Cut rule *)
Reserved Notation "n '|-c' B ';' L" (at level 80).
Inductive sig2hc: nat -> list lexp -> list lexp -> Prop :=

| sig2hc_init : forall B L A, L =mul= (A ⁺) :: [A ⁻] -> 0 |-c B ; L
| sig2hc_one : forall B L, L =mul= [1] -> 0 |-c B ; L 
| sig2hc_top : forall B L M, L =mul= Top :: M -> 0 |-c B ; L
| sig2hc_bot : forall B L M n, L =mul= Bot :: M -> n |-c B ; M -> S n |-c B ; L
| sig2hc_par : forall B L M F G n, L =mul= (F $ G) :: M -> n |-c B ; F :: G :: M -> S n |-c B ; L 
| sig2hc_cut : forall B L M N F m n, 
    L =mul= (M ++ N)  ->
    m|-c B ; F :: M ->
             n|-c B ; F° :: N -> S (max n m)|-c B ; L
| sig2hc_tensor : forall B L M N F G n m, 
    L =mul= (F ** G) :: (M ++ N)  ->
    m |-c B ; F :: M ->
              n |-c B ; G :: N -> S (max n m) |-c B ; L
| sig2hc_plus1: forall B L M F G n, L =mul= (F ⊕ G) :: M -> n |-c B ; F :: M -> S n |-c B ; L 
| sig2hc_plus2: forall B L M F G n, L =mul= (F ⊕ G) :: M -> n |-c B ; G :: M -> S n |-c B ; L 
| sig2hc_with: forall B L M F G n m, 
    L =mul= (F & G) :: M ->
    m |-c B ; F :: M ->
              n |-c B ; G :: M -> S (max n m) |-c B ; L
                                                        
| sig2hc_copy: forall B D L M F n, 
    D =mul= F :: B -> L =mul= F :: M ->
    n |-c D ; L -> 
              S n|-c D ; M 

| sig2hc_quest : forall B L M F n, L =mul= (? F) :: M  ->
                                   n |-c F :: B ; M -> 
                                                  S n |-c B ; L
                                                                
| sig2hc_bang : forall B F L n, L =mul= [! F] ->
                                n |-c  B ; [F] ->
                                           S n |-c  B ; L
                                                          
where "n |-c B ; L" := (sig2hc n B L).

Lemma sig2hc_der_compat : forall n (B1 B2 L1 L2 : list lexp), B1 =mul= B2 -> L1 =mul= L2 -> n |-c B1 ; L1 -> n |-c B2 ; L2.
Proof.
  intros n B1 B2 L1 L2 PB PL H.
  revert L1 L2 PL B1 B2 PB H;
    induction n using strongind; intros.
  - inversion H; subst. 
    +
      refine (sig2hc_init _ (transitivity (symmetry PL) H0)). 
    +
      refine (sig2hc_one _ (transitivity (symmetry PL) H0)).
    +
      refine (sig2hc_top _ (transitivity (symmetry PL) H0)).
  - inversion H0; subst; try rewrite PL in H3; try rewrite PL in H2;
      try rewrite PB in H3; try rewrite PB in H2.
    +
      refine (sig2hc_bot H2 _); auto.
      apply H with (L1:= M) (B1:=B1); auto.
    +
      refine (sig2hc_par H2 _); auto.
      apply H with (L1:= F :: G :: M) (B1:=B1); auto.
    +
      refine (sig2hc_cut H2 _ _).
      eapply H with (L1:= F :: M) (B1:=B1); auto.
      eapply H with (L1:= F° :: N) (B1:=B1); auto.
    +
      refine (sig2hc_tensor H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: N) (B1:=B1); auto.
    +
      refine (sig2hc_plus1 H2 _).
      apply H with (L1:= F :: M) (B1:=B1); auto. 
    +
      refine (sig2hc_plus2 H2 _).
      apply H with (L1:= G :: M) (B1:=B1); auto. 
    +
      refine (sig2hc_with H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: M) (B1:=B1); auto.
    + 
      refine (sig2hc_copy H2 H3 _).   
      apply H with (L1:= L) (B1:=B1); auto. 
    +
      refine (sig2hc_quest H2 _).
      apply H with (L1:= M) (B1:= F :: B1); auto. 
    +
      refine (sig2hc_bang H2 _).
      apply H with (L1:= [F]) (B1:=B1); auto. 
Qed.

Generalizable All Variables.
Instance sig2hc_der_morphism :
  Proper (meq ==> meq ==> iff) (sig2hc n).
Proof.
  unfold Proper; unfold respectful. 
  intros n B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (sig2hc_der_compat PB PL H).
  refine (sig2hc_der_compat (symmetry PB) (symmetry PL) H).
Qed.

(** Dyadic system + Cut  + Cut! rules *)
Reserved Notation " n '|-cc' B ';' L" (at level 80).
Inductive sig2hcc: nat -> list lexp -> list lexp -> Prop :=

| sig2hcc_init : forall B L A, L =mul= (A ⁺) :: [A ⁻] -> 0 |-cc B ; L
| sig2hcc_one : forall B L, L =mul= [1] -> 0 |-cc B ; L 
| sig2hcc_top : forall B L M, L =mul= Top :: M -> 0 |-cc B ; L
| sig2hcc_bot : forall B L M n, L =mul= Bot :: M -> n |-cc B ; M -> S n |-cc B ; L
| sig2hcc_par : forall B L M F G n, L =mul= (F $ G) :: M -> n |-cc B ; F :: G :: M -> S n |-cc B ; L 
| sig2hcc_cut : forall B L M N F m n, 
    L =mul= (M ++ N)  ->
    m|-cc B ; F :: M ->
              n|-cc B ; F° :: N -> S (max n m)|-cc B ; L
| sig2hcc_ccut : forall B L M N F m n, 
    L =mul= (M ++ N) ->
    m|-cc B ; (! F) :: M ->
              n|-cc F° :: B ; N -> S (max n m)|-cc B ; L 
| sig2hcc_tensor : forall B L M N F G n m, 
    L =mul= (F ** G) :: (M ++ N)  ->
    m |-cc B ; F :: M ->
               n |-cc B ; G :: N -> S (max n m) |-cc B ; L
| sig2hcc_plus1: forall B L M F G n, L =mul= (F ⊕ G) :: M -> n |-cc B ; F :: M -> S n |-cc B ; L 
| sig2hcc_plus2: forall B L M F G n, L =mul= (F ⊕ G) :: M -> n |-cc B ; G :: M -> S n |-cc B ; L 
| sig2hcc_with: forall B L M F G n m, 
    L =mul= (F & G) :: M ->
    m |-cc B ; F :: M ->
               n |-cc B ; G :: M -> S (max n m) |-cc B ; L
                                                           
| sig2hcc_copy: forall B D L M F n, 
    D =mul= F :: B -> L =mul= F :: M ->
    n |-cc D ; L -> 
               S n|-cc D ; M 

| sig2hcc_quest : forall B L M F n, L =mul= (? F) :: M  ->
                                    n |-cc F :: B ; M -> 
                                                    S n |-cc B ; L
                                                                   
| sig2hcc_bang : forall B F L n, L =mul= [! F] ->
                                 n |-cc  B ; [F] ->
                                             S n |-cc  B ; L
where "n |-cc B ; L" := (sig2hcc n B L).

Lemma sig2hcc_der_compat : forall n (B1 B2 L1 L2 : list lexp), B1 =mul= B2 -> L1 =mul= L2 -> n |-cc B1 ; L1 -> n |-cc B2 ; L2.
Proof.
  intros n B1 B2 L1 L2 PB PL H.
  revert L1 L2 PL B1 B2 PB H;
    induction n using strongind; intros.
  - inversion H; subst. 
    +
      refine (sig2hcc_init _ (transitivity (symmetry PL) H0)). 
    +
      refine (sig2hcc_one _ (transitivity (symmetry PL) H0)).
    +
      refine (sig2hcc_top _ (transitivity (symmetry PL) H0)).
  - inversion H0; subst; try rewrite PL in H3; try rewrite PL in H2;
      try rewrite PB in H3; try rewrite PB in H2.
    +
      refine (sig2hcc_bot H2 _); auto.
      apply H with (L1:= M) (B1:=B1); auto.
    +
      refine (sig2hcc_par H2 _); auto.
      apply H with (L1:= F :: G :: M) (B1:=B1); auto.
    +
      refine (sig2hcc_cut H2 _ _).
      eapply H with (L1:= F :: M) (B1:=B1); auto.
      eapply H with (L1:= F° :: N) (B1:=B1); auto.
    +
      refine (sig2hcc_ccut H2 _ _).
      eapply H with (L1:= (! F) :: M) (B1:=B1); auto.
      eapply H with (L1:=N) (B1:= F° :: B1); auto.
    + 
      refine (sig2hcc_tensor H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: N) (B1:=B1); auto.
    +
      refine (sig2hcc_plus1 H2 _).
      apply H with (L1:= F :: M) (B1:=B1); auto. 
    +
      refine (sig2hcc_plus2 H2 _).
      apply H with (L1:= G :: M) (B1:=B1); auto. 
    +
      refine (sig2hcc_with H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: M) (B1:=B1); auto.
    + 
      refine (sig2hcc_copy H2 H3 _).   
      apply H with (L1:= L) (B1:=B1); auto. 
    +
      refine (sig2hcc_quest H2 _).
      apply H with (L1:= M) (B1:= F :: B1); auto. 
    +
      refine (sig2hcc_bang H2 _).
      apply H with (L1:= [F]) (B1:=B1); auto. 
Qed. 

Generalizable All Variables.
Instance sig2hcc_der_morphism :
  Proper (meq ==> meq ==> iff) (sig2hcc n).
Proof.
  unfold Proper; unfold respectful. 
  intros n B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (sig2hcc_der_compat PB PL H).
  refine (sig2hcc_der_compat (symmetry PB) (symmetry PL) H).
Qed.

Reserved Notation " n '|~>' m ';' B ';' L" (at level 80).

Inductive sig3: nat -> nat -> list lexp -> list lexp -> Prop := 
| sig3_init : forall (B L: list lexp) A, L =mul= (A ⁺) :: [A ⁻] -> 0 |~> 0 ; B ; L
| sig3_one : forall (B L: list lexp), L =mul= [1] -> 0 |~> 0 ; B ; L
| sig3_top : forall (B L M: list lexp), L =mul= Top :: M -> 0 |~> 0 ; B ; L
| sig3_bot : forall (B L M: list lexp) n c, L =mul= Bot :: M -> n |~> c ; B ; M -> S n |~> c ; B ; L
| sig3_par : forall (B L M: list lexp) F G n c, L =mul= (F $ G) :: M -> n |~> c ; B ; F :: G :: M -> S n |~> c ;B ; L
| sig3_tensor : forall (B L M N: list lexp) F G n m c1 c2, L =mul= (F ** G) :: (M ++ N) -> m |~> c1 ; B ; F :: M -> n |~> c2 ; B ; G :: N -> S (max n m)  |~> c1+c2 ;B ; L
| sig3_plus1: forall (B L M: list lexp) F G n c, L =mul= (F ⊕ G) :: M -> n |~> c ; B ; F :: M -> S n |~> c ; B ; L
| sig3_plus2: forall (B L M: list lexp) F G n c, L =mul= (F ⊕ G) :: M -> n |~> c ; B ; G :: M -> S n |~> c ; B ; L
| sig3_with: forall (B L M: list lexp) F G n m c1 c2, L =mul= (F & G) :: M -> m |~> c1 ; B ; F :: M ->
                                                                                             n |~> c2 ; B ; G :: M -> S (max n m) |~> c1 + c2; B ; L
| sig3_copy: forall (B L M D: list lexp) F n c, D =mul= F :: B -> L =mul= F :: M -> n |~> c; D ; L -> S n |~> c ; D ; M
| sig3_quest : forall (B L M: list lexp) F n c, L =mul= (? F) :: M  -> n |~> c; F :: B ; M -> S n |~> c; B ; L
| sig3_bang : forall (B L: list lexp) F n c, L =mul= [! F] -> n |~>  c; B ; [F] -> S n |~> c ; B ; L 
| sig3_CUT : forall (B L: list lexp) n c w h, sig3_cut_general w h n c B L -> S n |~> S c ; B ; L 

with
sig3_cut_general : nat -> nat -> nat -> nat -> list lexp -> list lexp -> Prop :=
| sig3_cut : forall (B L M N: list lexp) F m n c1 c2 w h, 
    w = lexp_weight F ->
    h = m + n ->
    L =mul= (M ++ N) -> 
    m |~> c1 ; B ; F :: M -> 
                   n |~> c2 ; B ; F° :: N -> 
                                  sig3_cut_general w h (max n m) (c1 + c2) B L
| sig3_ccut : forall (B L M N: list lexp) F m n c1 c2 w h, 
    w = lexp_weight (! F) ->
    h = m + n ->
    L =mul= (M ++ N) -> 
    m |~> c1 ; B ; (! F) :: M -> 
                   n |~> c2 ; F° :: B ; N -> 
                                        sig3_cut_general w h (max n m) (c1 + c2) B L
where "n |~> m ; B ; L" := (sig3 n m B L).

Notation " n '~>' m ';' w ';' h ';' B ';' L"
  := (sig3_cut_general w h n m B L) (at level 80).

Arguments sig3_plus1 [B L M F G n c].

Lemma sig3_der_compat : forall n c (B1 B2 L1 L2: list lexp), 
    B1 =mul= B2 -> L1 =mul= L2 -> n |~> c ; B1 ; L1 -> n |~> c ; B2 ; L2.
Proof.
  intros n c B1 B2 L1 L2 PB PL H.
  revert dependent L1;
    revert dependent L2;
    revert dependent B1;
    revert dependent B2;
    revert dependent c; 
    induction n using strongind; intros.
  - inversion H; subst.
    refine (sig3_init _ (transitivity (symmetry PL) H0)). 
    refine (sig3_one _ (transitivity (symmetry PL) H0)).
    refine (sig3_top _ (transitivity (symmetry PL) H0)).

  - inversion H0; subst; try rewrite PL in H3; try rewrite PL in H2;
      try rewrite PB in H3; try rewrite PB in H2.
    +  
      refine (sig3_bot H2 _); auto.
      apply H with (L1:= M) (B1:=B1); auto.
    +
      refine (sig3_par H2 _); auto.
      apply H with (L1:= F :: G :: M) (B1:=B1); auto.
    +
      refine (sig3_tensor H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: N) (B1:=B1); auto.
    +
      refine (sig3_plus1 H2 _). 
      apply H with (L1:= F :: M) (B1:=B1); auto.
    +
      refine (sig3_plus2 H2 _).
      apply H with (L1:= G :: M) (B1:=B1); auto.
    +
      refine (sig3_with H2 _ _).
      apply H with (L1:= F :: M) (B1:=B1); auto.
      apply H with (L1:= G :: M) (B1:=B1); auto.
    + 
      refine (sig3_copy H2 H3 _).
      apply H with (L1:= L) (B1:=B1); auto.    
    +
      refine (sig3_quest H2 _).
      apply H with (L1:= M) (B1:= F :: B1); auto. 
    +
      refine (sig3_bang H2 _).
      apply H with (L1:= [F]) (B1:=B1); auto. 
    + 
      inversion H2; subst.
      ++
        eapply sig3_CUT.
        eapply sig3_cut with (F:=F); [ auto | auto | | |].
        rewrite <- PL. exact H4.
        apply H with (L1:= F :: M) (B1:=B1); auto.
        apply H with (L1:= F° :: N) (B1:=B1); auto.
      ++
        eapply sig3_CUT.
        eapply sig3_ccut with (F:=F) (M:=M) (N:=N) ; [ auto | auto | | | ].
        rewrite <- PL. exact H4.
        eapply H with (L1:= (! F) :: M) (B1:=B1); auto.
        apply H with (L1:= N) (B1:= F° :: B1); auto.
Qed.

Generalizable All Variables.
Instance sig3_der_morphism :
  Proper (meq ==> meq ==> iff) (sig3 n c).
Proof.
  unfold Proper; unfold respectful. 
  intros n c B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (sig3_der_compat PB PL H).
  refine (sig3_der_compat (symmetry PB) (symmetry PL) H).
Qed.

Hint Constructors sig2h sig2hc sig2hcc sig3 : core.

Theorem sig2_iff_sig2h :  forall B L, |-- B ; L <-> exists m, m |-- B ; L .
Proof.
  split; intros.
  *
    induction H; try destruct IHsig2; try destruct IHsig2_1; try destruct IHsig2_2;
      eexists;
      [eapply sig2h_init; eassumption |
       eapply sig2h_one; eassumption |
       eapply sig2h_top; eassumption |
       eapply sig2h_bot; eassumption |
       eapply sig2h_par; eassumption |   
       eapply sig2h_tensor; eassumption |
       eapply sig2h_plus1; eassumption |
       eapply sig2h_plus2; eassumption |
       eapply sig2h_with; eassumption |
       eapply sig2h_copy; eassumption |
       eapply sig2h_quest; eassumption |
       eapply sig2h_bang; eassumption].
  *
    destruct H.
    revert B L H.
    induction x using strongind; intros B L Hsig2h.
    inversion Hsig2h; subst;
      [eapply sig2_init; eassumption |  
       eapply sig2_one; eassumption |
       eapply sig2_top; eassumption ].
    inversion Hsig2h; subst.
    assert (|-- B; M) by solve [eapply H; auto].
    eapply sig2_bot; eassumption.
    assert (|-- B; F :: G :: M) by solve [eapply H; auto].   
    eapply sig2_par; eassumption.
    assert (|-- B; F :: M) by solve [eapply H with (m0:=m); auto].  
    assert (|-- B; G :: N) by solve [eapply H with (m0:=n); auto].    
    eapply sig2_tensor; eassumption.
    assert (|--  B; F :: M) by solve [eapply H; auto].   
    eapply sig2_plus1; eassumption.
    assert (|--  B; G :: M) by solve [eapply H; auto].   
    eapply sig2_plus2; eassumption.
    assert (|-- B; F :: M) by solve [eapply H with (m0:=m); auto].  
    assert (|-- B; G :: M) by solve [eapply H with (m0:=n); auto].  
    eapply sig2_with; eassumption. 
    assert (|--  B; L0) by solve [eapply H; auto].
    eapply sig2_copy ; eassumption.
    assert (|-- F :: B; M) by solve [eapply H; auto].    
    eapply sig2_quest; eassumption. 
    assert (|-- B; [F]) by solve [eapply H; auto].    
    eapply sig2_bang; eassumption. 
Qed.                          

Theorem sig2hc_then_sig2hcc: forall n B L, sig2hc n B L -> sig2hcc n B L.
Proof.
  intros.
  induction H.
  eapply sig2hcc_init; eassumption.
  eapply sig2hcc_one; eassumption.
  eapply sig2hcc_top; eassumption.
  eapply sig2hcc_bot; eassumption.
  eapply sig2hcc_par; eassumption.
  eapply sig2hcc_cut; eassumption.
  eapply sig2hcc_tensor; eassumption.
  eapply sig2hcc_plus1; eassumption.
  eapply sig2hcc_plus2; eassumption.
  eapply sig2hcc_with; eassumption.
  eapply sig2hcc_copy; eassumption.
  eapply sig2hcc_quest; eassumption.
  eapply sig2hcc_bang; eassumption.  
Qed.

Theorem sig2hcc_then_sig2hc: forall n B L, sig2hcc n B L -> exists m, sig2hc m B L.
Proof.
  intros.
  induction H; try destruct IHsig2hcc; try destruct IHsig2hcc1; try destruct IHsig2hcc2;
    eexists.
  eapply sig2hc_init; eassumption.
  eapply sig2hc_one; eassumption.
  eapply sig2hc_top; eassumption.
  eapply sig2hc_bot; eassumption.
  eapply sig2hc_par; eassumption.
  eapply sig2hc_cut; eassumption.
  eapply sig2hc_cut with (F:=!F) (M:=M) (N:=N) (m:=x); auto.
  eapply sig2hc_quest with (F:=F°); eauto.
  eapply sig2hc_tensor; eassumption.
  eapply sig2hc_plus1; eassumption.
  eapply sig2hc_plus2; eassumption.
  eapply sig2hc_with; eassumption.
  eapply sig2hc_copy; eassumption.
  eapply sig2hc_quest; eassumption.
  eapply sig2hc_bang; eassumption.  
Qed.

Theorem sig2hc_iff_sig2hcc: forall B L, (exists n, sig2hc n B L) <-> exists m, sig2hcc m B L.
Proof.
  split; intros.
  *
    destruct H.
    eexists.
    apply sig2hc_then_sig2hcc; eauto.
  *
    destruct H.
    eapply sig2hcc_then_sig2hc; eauto.
Qed.

Theorem sig2hcc_then_sig3 :  forall B L n, 
    n |-cc B ; L -> exists c, n |~> c ; B ; L.
Proof.
  intros.
  revert dependent B;
    revert dependent L.
  induction n using strongind; intros L B Hyp.
  **
    inversion Hyp; subst; eexists.
    eapply sig3_init; eassumption.
    eapply sig3_one; eassumption.
    eapply sig3_top; eassumption.
  **
    inversion Hyp; subst.
    ***
      assert (exists c : nat, n |~> c ; B; M) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      refine (sig3_bot H1 H0).
    ***
      assert (exists c : nat, n |~> c ; B; F :: G :: M) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      refine (sig3_par H1 H0).
    ***
      assert (exists c : nat, m |~> c ; B; F :: M) as Hn1 by solve [eapply H; auto].
      assert (exists c : nat, n0 |~> c ; B; F° :: N) as Hn2 by solve [eapply H; auto].      
      destruct Hn1, Hn2.
      eexists.
      eapply sig3_CUT.
      refine (sig3_cut _ _ _ H0 H4); auto.
    ***
      assert (exists c : nat, m |~> c ; B; (! F) :: M) as Hn1 by solve [eapply H; auto].
      assert (exists c : nat, n0 |~> c ; F° :: B; N) as Hn2 by solve [eapply H; auto].     
      destruct Hn1, Hn2.
      eexists.
      eapply sig3_CUT.
      refine (sig3_ccut _ _ _ H0 H4); auto.
    ***
      assert (exists c : nat, m |~> c ; B; F :: M) as Hn1 by solve [eapply H; auto].
      assert (exists c : nat, n0 |~> c ; B; G :: N) as Hn2 by solve [eapply H; auto].     
      destruct Hn1, Hn2.
      eexists.
      refine (sig3_tensor H1 H0 H4).
    ***                  
      assert (exists c : nat, n |~> c ; B; F :: M) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      refine (sig3_plus1 H1 H0).
    ***                  
      assert (exists c : nat, n |~> c ; B; G :: M) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      refine (sig3_plus2 H1 H0).                        
    ***
      assert (exists c : nat, m |~> c ; B; F :: M) as Hn1 by solve [eapply H; auto].
      assert (exists c : nat, n0 |~> c ; B; G :: M) as Hn2 by solve [eapply H; auto].      
      destruct Hn1, Hn2.
      eexists.
      refine (sig3_with H1 H0 H4).
    ***
      assert (exists c : nat, n |~> c ; B; L0) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      rewrite H2 in H0.
      refine (sig3_copy H1 _ H0); auto.
    ***
      assert (exists c : nat, n |~> c ; F :: B; M) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      refine (sig3_quest H1 H0).               
    ***
      assert (exists c : nat, n |~> c ; B; [F]) as Hn by solve [eapply H; auto].
      destruct Hn.
      eexists.
      refine (sig3_bang H1 H0).
Qed.        


Theorem sig3_then_sig2hcc :  forall B L n c, 
    n |~> c ; B ; L  -> n |-cc B ; L.
Proof.
  intros.
  revert dependent B;
    revert dependent L;
    revert dependent c.
  induction n using strongind; intros c L B Hyp.
  **
    inversion Hyp; subst.
    eapply sig2hcc_init; eassumption.
    eapply sig2hcc_one; eassumption.
    eapply sig2hcc_top; eassumption.
  **
    inversion Hyp; subst. 
    ***
      assert (n |-cc B; M) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_bot H1 _); auto.
    ***
      assert (n |-cc B; F :: G :: M) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_par H1 _); auto.
    ***
      assert (m |-cc B; F :: M) as Hc1 by
            solve [eapply H; auto; eassumption].
      assert (n0 |-cc B; G :: N) as Hc2 by
            solve [eapply H; auto; eassumption].        
      refine (sig2hcc_tensor H1 Hc1 Hc2).
    ***                  
      assert (n |-cc B; F :: M) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_plus1 H1 Hc).
    ***                  
      assert (n |-cc B; G :: M) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_plus2 H1 Hc).                        
    ***
      assert (m |-cc B; F :: M) as Hc1 by
            solve [eapply H; auto; eassumption].
      assert (n0 |-cc B; G :: M) as Hc2 by
            solve [eapply H; auto; eassumption].       
      refine (sig2hcc_with H1 Hc1 Hc2).
    ***
      assert (n |-cc B; L0) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_copy H1 H2 Hc).
    ***
      assert (n |-cc F :: B; M) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_quest H1 Hc).               
    ***
      assert (n |-cc B; [F]) as Hc by
            solve [eapply H; auto; eassumption].
      refine (sig2hcc_bang H1 Hc).
    ***
      inversion H1; subst. 
      assert (m |-cc B; F :: M) as Hc1 by
            solve [eapply H; auto; eassumption].
      assert (n0 |-cc B; F° :: N) as Hc2 by
            solve [eapply H; auto; eassumption]. 
      refine (sig2hcc_cut H3 Hc1 Hc2).

      assert (m |-cc B; (! F) :: M) as Hc1 by
            solve [eapply H; auto; eassumption].
      assert (n0 |-cc F° :: B; N) as Hc2 by
            solve [eapply H; auto; eassumption].        
      refine (sig2hcc_ccut _ Hc1 Hc2); auto.
Qed.        

Theorem sig3_iff_sig2hcc :  forall B L, 
    (exists n c, n |~> c ; B ; L) <-> exists m, m |-cc B ; L.
Proof.
  split; intros.
  *
    do 2 destruct H.
    eexists.
    eapply sig3_then_sig2hcc; eauto.
  *
    destruct H.
    eexists.
    eapply sig2hcc_then_sig3; eauto.
Qed.    
