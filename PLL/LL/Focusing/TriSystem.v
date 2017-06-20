(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Triadic System
This file specifies Andreoli's triadic system. Sequents are of the shape
<<
|-F- B ; M ; X
>>

where
 - [B] is the classical context
 - [M] contains only positive formulas
 - [X] is an "arrow" that can be:
  - [UP L], where L is a list of formulas (negative phase )
  - [DW F], where F is a formula (positive phase)


 *)


Require Export StrongInduction.
Require Export BDefinitions.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.


(** Triadic System for LL *)

Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).

Inductive TriSystem: nat -> list lexp -> list lexp -> Arrow -> Prop :=
| tri_init1 : forall B A,  0 |-F- B ; [A ⁻] ; DW (A ⁺)
| tri_init2 : forall B B' A,  B =mul= (A ⁻) :: B' -> 0 |-F- B ; [] ; DW (A ⁺)
| tri_one : forall B, 0 |-F- B ; [] ; DW 1
| tri_tensor : forall B M N MN F G n m,
    MN =mul= M ++ N -> n |-F- B ; N ; DW F -> m |-F- B ; M ; DW G -> S (max n m) |-F- B ; MN ; DW (F ** G)
| tri_plus1 : forall B M F G n, n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (F ⊕ G)
| tri_plus2 : forall B M F G n, n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (F ⊕ G)
| tri_bang : forall B F n, n |-F- B ; [] ; UP [F] -> S n |-F- B ; [] ; DW (! F)
| tri_rel : forall B F L n, ReleaseF F = true -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
(*where " n '|-F-' B ';' L ';' X " := (SyncPhase n B L X)
with AsyncPhase : nat -> Multiset -> Multiset -> Arrow -> Prop := *)
| tri_top : forall B L M, 0 |-F- B ; L ; UP (Top :: M)
| tri_bot : forall B L M n, n |-F- B ; L ; UP M -> S n |-F- B ; L ; UP (Bot :: M)
| tri_par : forall B L M F G n, n |-F- B ; L ; UP (F::G::M) -> S n |-F- B ; L ; UP(F $ G :: M)
| tri_with : forall B L M F G n m,
    n |-F- B ; L ; UP (F :: M) -> m |-F- B ; L ; UP (G :: M) -> S (max n m) |-F- B ; L ; UP (F & G :: M)
| tri_quest : forall B L M F n, n |-F- B ++ [F] ; L ; UP M -> S n |-F- B ; L ; UP (? F :: M)
| tri_store : forall B L M F n, AsynchronousF F = false -> n |-F- B ; L ++ [F] ; UP M -> S n |-F- B ; L ; UP (F::M)
| tri_dec1 : forall B L L' F n,
    IsNegativeAtomF F = false ->
    L =mul= F :: L' -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
| tri_dec2 : forall B B' L  F n,
    IsNegativeAtomF F = false ->
    B =mul= F :: B' -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP [] 
where " n '|-F-' B ';' L ';' X " := (TriSystem n B L X).


(* The [B] and [M] contexts can be substituted by equivalent multisets *)
Theorem TriExchange : forall B B' M M' X n, n |-F-  B ; M ; X -> B =mul= B' -> M =mul= M' -> n |-F- B' ; M' ; X.
Proof.
  intros.
  generalize dependent B.
  generalize dependent M.
  generalize dependent B'.
  generalize dependent M'.
  generalize dependent X.
  induction n using strongind;intros.
  + inversion H;subst.
    ++ apply MulSingleton in H1;subst.
       eapply tri_init1.
    ++
      apply meq_sym in H1.
      apply  multiset_meq_empty in H1;subst.
      eapply tri_init2.
      rewrite <- H0.
      apply H2.
    ++
      apply meq_sym in H1.
      apply  multiset_meq_empty in H1;subst.
      eapply tri_one.
    ++
      eapply tri_top.
  + inversion H0;subst.
    ++ (* tensor *)
      apply H  with (M':=N) (B':= B') in H5;auto.
      apply H  with (M':=M0) (B':= B') in H6;auto.
      apply tri_tensor with (F:=F)(G:=G) (N:=N)(M:=M0);auto.
      rewrite <- H1.
      assumption.
    ++ (* Oplus *) 
      eapply H  with (M':=M') (B':=B')in H4;auto.
      eapply tri_plus1;auto.
    ++ (* Oplus 2*)
      eapply H  with (M':=M') (B':=B')in H4;auto.
      eapply tri_plus2;auto.
    ++ (* Bang *)
      apply meq_sym in H1.
      apply  multiset_meq_empty in H1;subst.
      eapply H  with (B':=B')in H4;auto.
      eapply tri_bang;auto.
    ++ (* Release *)
      eapply H  with (M':=M') (B':=B')in H5;auto.
      eapply tri_rel;auto.
    ++ (* Bottom *)
      eapply H  with (M':=M') (B':=B')in H4;auto.
      eapply tri_bot;auto.
    ++ (* Par *)
      eapply H  with (M':=M') (B':=B')in H4;auto.
      eapply tri_par;auto.
    ++ (* with *)
      eapply H  with (M':=M') (B':=B')in H4;auto.
      eapply H  with (M':=M') (B':=B')in H5;auto.
      eapply tri_with;auto.
    ++ (* ? *)
      eapply H  with (M':=M')(B':=B' ++ [F])in H4;auto.
      eapply tri_quest;auto.
    ++  (* store *)
      eapply H  with (M':=M' ++ [F]) (B':=B')in H5;auto.
      eapply tri_store;auto.
    ++  (* decide 1*)
      eapply H  with (M':= L' ) (B':=B')in H6;auto.
      eapply tri_dec1 with (F:=F);auto.
      rewrite <- H1.
      apply H5.
      assumption.
    ++ (* decide 2 *)
      eapply H  with (M':= M' ) (B':=B')in H6;auto.
      eapply tri_dec2 with (F:=F);auto.
      rewrite <- H2.
      apply H5.
Qed.


Generalizable All Variables.
Instance Tri_morph : Proper (meq ==> meq ==> eq ==> iff) (TriSystem n).
Proof. 
  intros n A B Hab C D Hcd X Y Hxy; subst.
  split;intro.
  + apply TriExchange with (B:=A) (M:=C);auto.
  + apply TriExchange with (B:=B) (M:=D);auto.
Qed.
Instance Tri_morph' : Proper (meq ==> meq ==> @eq Arrow ==> iff) (TriSystem n).
Proof. 
  intros n A B Hab C D Hcd X Y Hxy; subst.
  split;intro.
  + apply TriExchange with (B:=A) (M:=C);auto.
  + apply TriExchange with (B:=B) (M:=D);auto.
Qed.

Example myExample l' L1' L2' B M :
  (exists m : nat, m |-F- B; M; UP ((l' :: L1') ++ [⊤] ++ L2')) ->
  exists m : nat, m |-F- B; M; UP (l' :: L1' ++ [⊤] ++ L2').
Proof.
  intros.
  assert (l' :: L1' ++ [⊤] ++ L2' = (l' :: L1') ++ [⊤] ++ L2') by auto. 
  rewrite H0.
Abort.
