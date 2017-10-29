(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

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

  - [TriSystem] (notation [ |-F- B ; L ; UP L ] for the negative phase and
    [ |-F- B ; L ; DW F ] for the positive phase). This system implements
    the focused system for linear logic as described by 
    #<a href="https://www.cs.cmu.edu/~fp/courses/15816-s12/misc/andreoli92jlc.pdf"> Andreoli </a>#.

 *)


(*Add LoadPath "./". *)
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export LL.StrongInduction.
Require Export LL.Syntax.
Require Import LL.Eqset.

Set Implicit Arguments.

Module SqSystems (DT : Eqset_dec_pol).
  
  Module Export SxLL := FormulasLL DT.
  Export DT.

  Hint Resolve Max.le_max_r. 
  Hint Resolve Max.le_max_l.
  Hint Constructors IsNegativeAtom.
  Hint Constructors IsPositiveAtom.

  
  (****** ARROWS ******)
  Inductive Arrow  :=
  | UP (l : list Lexp)
  | DW (F : Lexp).
  
  Definition Arrow2LL (A: Arrow) : list Lexp :=
    match A  with
    | UP l => l
    | DW F => [F]
    end.
  
  Lemma Arrow_eq_dec : forall F1 F2: Arrow , {F1 =F2} + {F1 <> F2}.
    intros.
    destruct F1;destruct F2.
    generalize(list_eq_dec FEqDec l l0);intro.
    destruct H;subst;auto. right; intuition. apply n;intuition. inversion H;auto.
    right;intro. inversion H.
    right;intro. inversion H.
    generalize(FEqDec F F0);intro.
    destruct H;subst;auto. right;intuition. apply n;inversion H;auto.
  Qed.
  

  (******************************************************)
  (** Triadic system *)
  (******************************************************)
  Reserved Notation " '|-F-' B ';' L ';' X " (at level 80).
  
  Inductive TriSystem:  list Lexp -> list Lexp -> Arrow -> Prop :=
  | tri_init1 : forall B A, IsNegativeAtom A ->  |-F- B ; [(Dual_LExp A)] ; DW (A)
  | tri_init2 : forall B B' A, IsNegativeAtom A -> B =mul= (Dual_LExp A) :: B' -> |-F- B ; [] ; DW (A)
  | tri_one : forall B, |-F- B ; [] ; DW 1
  | tri_tensor : forall B M N MN F G,
      MN =mul= M ++ N -> |-F- B ; N ; DW F -> |-F- B ; M ; DW G -> |-F- B ; MN ; DW (F ** G)
  | tri_plus1 : forall B M F G, |-F- B ; M ; DW F -> |-F- B ; M ; DW (F ⊕ G)
  | tri_plus2 : forall B M F G, |-F- B ; M ; DW G -> |-F- B ; M ; DW (F ⊕ G)
  | tri_bang : forall B F, |-F- B ; [] ; UP [F] -> |-F- B ; [] ; DW (! F)
  | tri_rel : forall B F L, Release F -> |-F- B ; L ; UP [F] ->  |-F- B ; L ; DW F
                                                                                 
  | tri_top : forall B L M, |-F- B ; L ; UP (Top :: M)
  | tri_bot : forall B L M, |-F- B ; L ; UP M -> |-F- B ; L ; UP (Bot :: M)
  | tri_par : forall B L M F G, |-F- B ; L ; UP (F::G::M) -> |-F- B ; L ; UP(F $ G :: M)
  | tri_with : forall B L M F G,
      |-F- B ; L ; UP (F :: M) -> |-F- B ; L ; UP (G :: M) -> |-F- B ; L ; UP (F & G :: M)
  | tri_quest : forall B L M F, |-F- B ++ [F] ; L ; UP M -> |-F- B ; L ; UP (? F :: M)
  | tri_store : forall B L M F, ~ Asynchronous  F-> |-F- B ; L ++ [F] ; UP M -> |-F- B ; L ; UP (F::M)
  | tri_dec1 : forall B L L' F, ~IsPositiveAtom F -> L =mul= F :: L' -> |-F- B ; L' ; DW F ->|-F- B ; L ; UP []
  | tri_dec2 : forall B B' L  F, ~IsPositiveAtom F -> B =mul= F :: B' -> |-F- B ; L ; DW F -> |-F- B ; L ; UP []
  | tri_ex  : forall B FX M t, |-F- B; M ; DW (Subst FX t) -> |-F- B; M ; DW (E{FX})
  | tri_fx  : forall B L FX M,    (forall x, |-F- B ; L ; UP( (Subst FX x) ::  M)) -> |-F- B ; L ; UP (F{FX} :: M)
  where " '|-F-' B ';' L ';' X " := (TriSystem B L X).
  Hint Constructors TriSystem.
  
  (******************************************************)
  (** Triadic system with meassures *)
  (******************************************************)
  Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).
  Inductive TriSystemh: nat -> list Lexp -> list Lexp -> Arrow -> Prop :=
  | trih_init1 : forall B A,  IsNegativeAtom A ->  0 |-F- B ; [(Dual_LExp A)] ; DW (A)
  | trih_init2 : forall B B' A,  IsNegativeAtom A -> B =mul= (Dual_LExp A) :: B' -> 0 |-F- B ; [] ; DW (A)
  | trih_one : forall B, 0 |-F- B ; [] ; DW 1
  | trih_tensor : forall B M N MN F G n m,
      MN =mul= M ++ N -> n |-F- B ; N ; DW F -> m |-F- B ; M ; DW G -> S (max n m) |-F- B ; MN ; DW (F ** G)
  | trih_plus1 : forall B M F G n, n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (F ⊕ G)
  | trih_plus2 : forall B M F G n, n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (F ⊕ G)
  | trih_bang : forall B F n, n |-F- B ; [] ; UP [F] -> S n |-F- B ; [] ; DW (! F)
  | trih_rel : forall B F L n, Release F -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
                                                                                          
  | trih_top : forall B L M, 0 |-F- B ; L ; UP (Top :: M)
  | trih_bot : forall B L M n, n |-F- B ; L ; UP M -> S n |-F- B ; L ; UP (Bot :: M)
  | trih_par : forall B L M F G n, n |-F- B ; L ; UP (F::G::M) -> S n |-F- B ; L ; UP(F $ G :: M)
  | trih_with : forall B L M F G n m,
      n |-F- B ; L ; UP (F :: M) -> m |-F- B ; L ; UP (G :: M) -> S (max n m) |-F- B ; L ; UP (F & G :: M)
  | trih_quest : forall B L M F n, n |-F- B ++ [F] ; L ; UP M -> S n |-F- B ; L ; UP (? F :: M)
  | trih_store : forall B L M F n, ~ Asynchronous F-> n |-F- B ; L ++ [F] ; UP M -> S n |-F- B ; L ; UP (F::M)
  | trih_dec1 : forall B L L' F n, ~IsPositiveAtom F -> L =mul= F :: L' -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
  | trih_dec2 : forall B B' L  F n, ~IsPositiveAtom F -> B =mul= F :: B' -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | trih_ex  : forall B  n FX M t, 
      n |-F- B; M ; DW (Subst FX t) -> S n |-F- B; M ; DW (E{FX})
  | trih_fx  : 
      forall B L n FX M,
        (forall x : Term, n |-F- B ; L ; UP( (Subst FX x) ::  M)) -> S n |-F- B ; L ; UP (F{FX} :: M)
  where " n '|-F-' B ';' L ';' X " := (TriSystemh n B L X).
  Hint Constructors TriSystemh.
  
  (** Dyadic System *)
  Reserved Notation " '|--' B ';' L" (at level 80).
  Inductive sig2: list Lexp -> list Lexp -> Prop :=

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
  | sig2_ex  : forall B L FX M t,
      L =mul= E{FX} ::  M ->  |-- B ; (Subst FX t) :: M ->  |--  B ; L
  | sig2_fx  : forall B L FX M,  L =mul= (F{FX}) :: M -> (forall x, |-- B ; [Subst FX x] ++  M) ->  |-- B ; L
                                                                                                              
  where "|-- B ; L" := (sig2 B L).

  (** Dyadic system plus height of the derivation *)
  Reserved Notation " n '|--' B ';' L" (at level 80).
  Inductive sig2h: nat -> list Lexp -> list Lexp -> Prop :=
    
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
      n |-- D ; L ->  S n|-- D ; M 
                                   
  | sig2h_quest : forall B L M F n, L =mul= (? F) :: M  ->
                                    n |-- F :: B ; M ->   S n |-- B ; L
                                                                        
  | sig2h_bang : forall B F L n, L =mul= [! F] ->
                                 n |--  B ; [F] ->  S n |--  B ; L
                                                                   
  | sig2h_ex  : forall B L n FX M t,
      L =mul= E{FX} ::  M -> n |-- B ; (Subst FX t) :: M -> S n |--  B ; L
  | sig2h_fx  : forall B L n FX M,  L =mul= (F{FX}) :: M -> (forall x, n |-- B ; [Subst FX x] ++  M) -> S n |-- B ; L
                                                                                                                      
  where "n |-- B ; L" := (sig2h n B L).
  Hint Constructors sig2h.

  (* Dyadic system with inductive measures *)
  Reserved Notation "n '|-c' B ';' L" (at level 80).
  Inductive sig2hc: nat -> list Lexp -> list Lexp -> Prop :=

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
                                                            
  | sig2hc_ex  : forall B L n FX M t,
      L =mul= E{FX} ::  M -> n |-c B ; (Subst FX t) :: M -> S n |-c  B ; L
  | sig2hc_fx  : forall B L n FX M,  L =mul= (F{FX}) :: M -> (forall x, n |-c B ; [Subst FX x] ++  M) -> S n |-c B ; L
                                                                                                                       
  where "n |-c B ; L" := (sig2hc n B L).

  (** System with rules Cut and Cut! *)
  Reserved Notation " n '|-cc' B ';' L" (at level 80).
  Inductive sig2hcc: nat -> list Lexp -> list Lexp -> Prop :=

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
                                                               
  | sig2hcc_ex  : forall B L n FX M t,
      L =mul= E{FX} ::  M -> n |-cc B ; (Subst FX t) :: M -> S n |-cc  B ; L
  | sig2hcc_fx  : forall B L n FX M,  L =mul= (F{FX}) :: M -> (forall x, n |-cc B ; [Subst FX x] ++  M) -> S n |-cc B ; L
                                                                                                                          
  where "n |-cc B ; L" := (sig2hcc n B L).

  (** System with all the inductive measures needed for the proof of cut-elimination *)
  Reserved Notation " n '|~>' m ';' B ';' L" (at level 80).

  Inductive sig3: nat -> nat -> list Lexp -> list Lexp -> Prop := 
  | sig3_init : forall (B L: list Lexp) A, L =mul= (A ⁺) :: [A ⁻] -> 0 |~> 0 ; B ; L
  | sig3_one : forall (B L: list Lexp), L =mul= [1] -> 0 |~> 0 ; B ; L
  | sig3_top : forall (B L M: list Lexp), L =mul= Top :: M -> 0 |~> 0 ; B ; L
  | sig3_bot : forall (B L M: list Lexp) n c, L =mul= Bot :: M -> n |~> c ; B ; M -> S n |~> c ; B ; L
  | sig3_par : forall (B L M: list Lexp) F G n c, L =mul= (F $ G) :: M -> n |~> c ; B ; F :: G :: M -> S n |~> c ;B ; L
  | sig3_tensor : forall (B L M N: list Lexp) F G n m c1 c2, L =mul= (F ** G) :: (M ++ N) -> m |~> c1 ; B ; F :: M -> n |~> c2 ; B ; G :: N -> S (max n m)  |~> c1+c2 ;B ; L
  | sig3_plus1: forall (B L M: list Lexp) F G n c, L =mul= (F ⊕ G) :: M -> n |~> c ; B ; F :: M -> S n |~> c ; B ; L
  | sig3_plus2: forall (B L M: list Lexp) F G n c, L =mul= (F ⊕ G) :: M -> n |~> c ; B ; G :: M -> S n |~> c ; B ; L
  | sig3_with: forall (B L M: list Lexp) F G n m c1 c2, L =mul= (F & G) :: M -> m |~> c1 ; B ; F :: M ->
                                                                                               n |~> c2 ; B ; G :: M -> S (max n m) |~> c1 + c2; B ; L
  | sig3_copy: forall (B L M D: list Lexp) F n c, D =mul= F :: B -> L =mul= F :: M -> n |~> c; D ; L -> S n |~> c ; D ; M
  | sig3_quest : forall (B L M: list Lexp) F n c, L =mul= (? F) :: M  -> n |~> c; F :: B ; M -> S n |~> c; B ; L
  | sig3_bang : forall (B L: list Lexp) F n c, L =mul= [! F] -> n |~>  c; B ; [F] -> S n |~> c ; B ; L 
                                                                                                       
  | sig3_ex  : forall (B L: list Lexp) n c FX M t,
      L =mul= E{FX} ::  M -> n |~> c; B ; (Subst FX t) :: M -> S n |~> c; B ; L
  | sig3_fx  : forall (B L: list Lexp) n c FX M,  L =mul= (F{FX}) :: M -> (forall x, n |~> c; B ; (Subst FX x) ::  M) -> S n |~> c; B ; L
                                                                                                                                          

  | sig3_CUT : forall (B L: list Lexp) n c w h, sig3_cut_general w h n c B L -> S n |~> S c ; B ; L 

  with
  sig3_cut_general : nat -> nat -> nat -> nat -> list Lexp -> list Lexp -> Prop :=
  | sig3_cut : forall (B L M N: list Lexp) F m n c1 c2 w h, 
      w = Lexp_weight F ->
      h = m + n ->
      L =mul= (M ++ N) -> 
      m |~> c1 ; B ; F :: M -> 
                     n |~> c2 ; B ; F° :: N -> 
                                    sig3_cut_general w h (max n m) (c1 + c2) B L
  | sig3_ccut : forall (B L M N: list Lexp) F m n c1 c2 w h, 
      w = Lexp_weight (! F) ->
      h = m + n ->
      L =mul= (M ++ N) -> 
      m |~> c1 ; B ; (! F) :: M -> 
                     n |~> c2 ; F° :: B ; N -> 
                                          sig3_cut_general w h (max n m) (c1 + c2) B L
  where "n |~> m ; B ; L" := (sig3 n m B L).

  Notation " n '~>' m ';' w ';' h ';' B ';' L"
    := (sig3_cut_general w h n m B L) (at level 80).

  Hint Constructors sig2h.
  Hint Constructors sig2hc.
  Hint Constructors sig2hcc.
  Hint Constructors sig3.

End SqSystems.
