(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Structural Rules (Focused System)
This files proves some permutation lemmas for the negative connectives. 
*)


(* Add LoadPath "../../". *)
Require Import Arith.
Require Import Lia.
Require Import TriSystem.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Ltac EquivPosCase H IH m L Hinv :=
  match goal with
    [_ : AsynchronousF _ = false |- _] =>
    inversion H; subst;
    apply IH with(m:=L_weight L) in Hinv;
      auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n));
    destruct Hinv;
    eexists;
    simpl; eapply tri_store;auto;
    eassumption
  end.

Theorem EquivAuxBot : forall B  L L' M  n,  n |-F- B ; M ; UP (L ++ L') -> exists m, m |-F- B ; M ;  UP (L ++ [Bot] ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent n .
  generalize dependent w .

  induction w as [| w' IH] using strongind ; intros n M B L' L H Hw  ;  destruct L as [|l].
  + simpl. simpl in H.
    eexists.
    eapply tri_bot;auto.
    apply H.
  + simpl in Hw. (* Heqw is inconsisten *)
    destruct l; simpl in Hw; inversion Hw.
  + simpl in Hw. inversion Hw.
  + destruct l;inversion Hw as [Hw'];inversion H; subst;auto;try (EquivPosCase H IH m L H6).
    ++ (* TOP *)
      simpl.
      eexists.
      eapply tri_top.
    ++ (* BOT *)
      apply IH  with(m:=L_weight L) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_bot ;auto.
      eassumption.
    ++ (* PAR *)
      apply IH  with (L:= l1 :: l2 :: L) (m:= plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L)) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_par;auto.
      eassumption.
      simpl.
      symmetry; apply Nat.add_assoc.
    ++ (* WITH *)
      apply IH with (L:= l1 :: L) (m:= plus (exp_weight l1) (L_weight L)) in H5;auto.
      apply IH with (L:= l2 :: L) (m:= plus (exp_weight l2) (L_weight L)) in H7;auto.
      destruct H5. destruct H7.
      eexists.
      simpl.
      apply tri_with;eassumption.
      lia.
      lia.
    ++  (* QUEST *)
      apply IH  with(m:=L_weight L) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_quest ;auto.
      eassumption.
      lia.
Qed.

Ltac EquivAuxWithPosCases IH H H' L n1 n0 H6 H13 :=
  inversion H;
  inversion H'; subst;
  generalize(IH (L_weight L) (le_n (L_weight L)) n1 n0 _ _ _ _ H6 H13 (eq_refl (L_weight L))) as Hp;intros;auto;
  destruct Hp;
  eexists;
  eapply tri_store;eauto.

Theorem EquivAuxWith : forall B  L L' M  n n' F G ,  n |-F- B ; M ; UP (L ++ [F] ++ L') ->
                                                                    n' |-F- B ; M ; UP (L ++ [G] ++ L') ->

                                                                                    exists m, m |-F- B ; M ;  UP (L ++ [F & G] ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent n .
  generalize dependent n' .
  generalize dependent w .

  induction w as [| w' IH] using strongind  ; intros n' n M B L' L H H' Hw  ;  destruct L as [|l].
  + simpl. simpl in H.
    eexists.
    eapply tri_with;auto;eassumption.
  + simpl in Hw. (* Heqw is inconsisten *)
    destruct l; simpl in Hw; inversion Hw.
  + simpl in Hw. inversion Hw.
  + destruct l; inversion Hw as [Hw']; try(EquivAuxWithPosCases IH H H' L n1 n0 H6 H13).

    ++ (* TOP *)
      simpl.
      eexists.
      eapply tri_top.
    ++ (* BOT *)
      inversion H.
      inversion H'.
      subst.
      assert(exists m0 : nat, m0 |-F- B; M ; UP (L ++ [F & G] ++ L')) as Hp.
      eapply IH with (m:= L_weight L) ;eauto.
      destruct Hp.
      eexists.
      simpl.
      eapply tri_bot;auto; eassumption.
      subst.
      inversion H10.
      subst.
      inversion H5.
    ++  (* tensor *)
      inversion H; inversion H';subst.
      assert(exists m0 : nat, m0 |-F- B; M ++ [l1 ** l2]; UP (L ++ [F & G] ++ L')) as Hp.
      eapply IH with  (m:= L_weight L);eauto.
      lia.
      destruct Hp.
      eexists.
      simpl. eapply tri_store;auto; eassumption.
    ++ (* PAR *)
      inversion H.
      inversion H'.
      subst.
      assert(exists m0 : nat, m0 |-F- B; M ; UP ((l1 :: l2 :: L) ++ [F & G] ++ L')) as Hp.
      eapply IH with (m:= plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L) ) ;eauto.
      simpl. lia.

      destruct Hp.
      eexists.
      simpl.
      eapply tri_par;auto; eassumption.

      subst.
      inversion H12.
      subst.
      inversion H5.

    ++ (* OPLUS  the same *)
      inversion H; inversion H';subst.
      assert(exists m0 : nat, m0 |-F- B; M ++ [l1 ⊕ l2]; UP (L ++ [F & G] ++ L')) as Hp.
      eapply IH with  (m:= L_weight L);eauto.
      lia.
      destruct Hp.
      eexists.
      simpl. eapply tri_store;auto; eassumption.
    ++  (* WITH *)
      inversion H.
      inversion H'.
      subst.

      assert(exists m0 : nat, m0 |-F- B; M ; UP ((l1 :: L) ++ [F & G] ++ L')) as Hp1.
      eapply IH with (m:= plus (exp_weight l1) (L_weight L) ) ;eauto.
      simpl. lia.
      assert(exists m0 : nat, m0 |-F- B; M ; UP ((l2 :: L) ++ [F & G] ++ L')) as Hp2.
      eapply IH with (m:= plus (exp_weight l2) (L_weight L) ) ;eauto.
      simpl. lia.

      destruct Hp1.
      destruct Hp2.

      eexists.
      simpl.
      eapply tri_with;auto; eassumption.

      subst.
      inversion H13.
      subst.
      inversion H5.
    ++ (* Bang the same *)
      inversion H; inversion H';subst.
      assert(exists m0 : nat, m0 |-F- B; M ++ [! l]; UP (L ++ [F & G] ++ L')) as Hp.
      eapply IH with  (m:= L_weight L);eauto.
      lia.
      destruct Hp.
      eexists.
      simpl. eapply tri_store;auto; eassumption.

    ++  (* quest *)
      inversion H.
      inversion H'.
      subst.
      assert(exists m0 : nat, m0 |-F- B ++ [l]; M ; UP (L ++ [F & G] ++ L')) as Hp.
      eapply IH with (m:= L_weight L) ;eauto.
      lia.

      destruct Hp.
      eexists.
      simpl.
      eapply tri_quest;auto; eassumption.
      subst.
      inversion H11.
      subst.
      inversion H5.
Qed.



(* This proof is exactly the same as the one of bottom *)
Theorem EquivAuxPar : forall B  L L' M F G  n,  n |-F- B ; M ; UP (L ++ [F ; G] ++ L') -> exists m, m |-F- B ; M ;  UP (L ++ [F $ G] ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent n .
  generalize dependent w .
  
  induction w as [| w' IH] using strongind ; intros n M B L' L H Hw  ;  destruct L as [|l].
  + simpl. simpl in H.
    eexists.
    eapply tri_par;auto.
    apply H.
  + simpl in Hw. (* Heqw is inconsisten *)
    destruct l; simpl in Hw; inversion Hw.
  + simpl in Hw. inversion Hw.
  + destruct l;inversion Hw as [Hw'];inversion H; subst;auto;try (EquivPosCase H IH m L H6).
    ++ (* TOP *)
      simpl.
      eexists.
      eapply tri_top.
    ++ (* BOT *)
      apply IH  with(m:=L_weight L) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_bot ;auto.
      eassumption.
    ++ (* PAR *)
      apply IH  with (L:= l1 :: l2 :: L) (m:= plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L)) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_par;auto.
      eassumption.
      simpl.
      symmetry; apply Nat.add_assoc.
    ++ (* WITH *)
      apply IH with (L:= l1 :: L) (m:= plus (exp_weight l1) (L_weight L)) in H5;auto.
      apply IH with (L:= l2 :: L) (m:= plus (exp_weight l2) (L_weight L)) in H7;auto.
      destruct H5. destruct H7.
      eexists.
      simpl.
      apply tri_with;eassumption.
      lia.
      lia.
    ++  (* QUEST *)
      apply IH  with(m:=L_weight L) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_quest ;auto.
      eassumption.
      lia.
Qed.





Ltac EquivAuxSyncPosCases IH F H8 :=
  match goal with
    [ H1 : _ |-F- _ ; ?M ++ [?F] ; UP ((?G :: ?L) ++ _) |- _ ] =>
    inversion H1;subst;
    assert ( (M ++ [F]) ++ [G] =mul=  (M ++ [G]) ++ [F]) by solve_permutation;
    eapply TriExchange with (M':= (M ++ [G]) ++ [F]) in H8;
      auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)), Nat.le_add_r;
    apply IH  with  (m:=L_weight L) in H8 ;auto;
    destruct H8;
    eexists; simpl; eapply tri_store;auto; eassumption
  end.

Theorem EquivAuxSync : forall B  L L' M  n F ,  AsynchronousF F = false -> n |-F- B ; M ++ [F] ; UP (L ++ L') -> exists m, m |-F- B ; M ;  UP (L ++ [F] ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent n .
  generalize dependent w .
  
  induction w as [| w' IH] using strongind; intros n  M   B  L'  L  H1 Hw; destruct L as [|l].
  + simpl. simpl in H1.
    eexists.
    eapply tri_store;auto.
    apply H1.
  + simpl in Hw. (* Hw is inconsisten *)
    destruct l; simpl in Hw; inversion Hw.
  + simpl in Hw. inversion Hw.
  + destruct l;
      inversion Hw as [Hw'];
      inversion H; subst; auto; try (EquivAuxSyncPosCases IH F H8).
    ++ (* TOP *)
      simpl.
      eexists.
      eapply tri_top.
    ++ (* BOT *)
      inversion H1;subst.
      apply IH  with(m:=L_weight L) in H6;auto.
      destruct H6.
      eexists.
      simpl. eapply tri_bot ;auto;eassumption.
      inversion H7.
    ++ (* Tensor *) 
      inversion H1;subst.
      assert ( (M ++ [F]) ++ [l1 ** l2] =mul=  (M ++ [l1 ** l2]) ++ [F]) by solve_permutation.
      eapply TriExchange with (M':= (M ++ [l1 ** l2]) ++ [F]) in H8;
        auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)).
      apply IH  with (m:=L_weight L) in H8;
        auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)).
      destruct H8.
      eexists; simpl; eapply tri_store;auto; eassumption.

    ++ (* PAR *)
      inversion H1;subst.
      apply IH  with (L:= l1 :: l2 :: L) (m:= plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L)) in H6;auto.
      destruct H6.
      eexists.
      simpl. eapply tri_par;auto;eassumption.
      simpl.
      symmetry; apply Nat.add_assoc.
      inversion H7.
    ++ (* OPLUS *) (* Tactic should solve this one *)
      inversion H1;subst.
      assert ( (M ++ [F]) ++ [l1 ⊕ l2] =mul=  (M ++[l1 ⊕ l2]) ++ [F]) by solve_permutation.
      eapply TriExchange with (M':= (M ++ [l1 ⊕ l2]) ++ [F]) in H8;
        auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)).
      apply IH with (m:=L_weight L) in H8;
        auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)).
      destruct H8.
      eexists; simpl; eapply tri_store;auto;eassumption.
    ++ (* WITH *)
      inversion H1;subst.
      apply IH with (L:= l1 :: L) (m:= plus (exp_weight l1) (L_weight L)) in H7;auto.
      apply IH with (L:= l2 :: L) (m:= plus (exp_weight l2) (L_weight L)) in H9;auto.
      destruct H7. destruct H9.
      eexists.
      simpl.
      apply tri_with;eassumption.
      lia.
      lia.
      inversion H7.
    ++ (* BANG *) (* Tactic should solve this one *)
      inversion H1;subst.
      assert ( (M ++ [F]) ++ [! l] =mul=  (M ++ [! l]) ++ [F]) by solve_permutation.
      eapply TriExchange with (M':= (M ++ [! l]) ++ [F]) in H8;
        auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)).
      apply IH with (m:=L_weight L) in H8;
        auto using (fun n m => eq_ind _ _ (Nat.le_add_r m n) _ (Nat.add_comm m n)).
      destruct H8.
      eexists; simpl; eapply tri_store;auto;eassumption.

    ++  (* QUEST *)
      inversion H1;subst.
      apply IH  with(m:=L_weight L) in H6;auto.
      destruct H6.
      eexists.
      simpl. eapply tri_quest ;auto;eassumption.
      lia.
      inversion H7.
Qed.



Theorem EquivAuxQuest : forall B  L L' M  n F,  n |-F- B ++ [F] ; M ; UP (L ++ L') -> exists m, m |-F- B ; M ;  UP (L ++ [? F] ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent n .
  generalize dependent w .
  
  induction w as [| w' IH] using strongind ; intros n M B L' L H Hw  ;  destruct L as [|l].
  + simpl. simpl in H.
    eexists.
    eapply tri_quest;auto.
    apply H.
  + simpl in Hw. (* Heqw is inconsisten *)
    destruct l; simpl in Hw; inversion Hw.
  + simpl in Hw. inversion Hw.
  + destruct l;inversion Hw as [Hw'];inversion H; subst;auto;try (EquivPosCase H IH m L H6).
    ++ (* TOP *)
      simpl.
      eexists.
      eapply tri_top.
    ++ (* BOT *)
      apply IH  with(m:=L_weight L) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_bot ;auto.
      eassumption.
    ++ (* PAR *)
      apply IH  with (L:= l1 :: l2 :: L) (m:= plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L)) in H4;auto.
      destruct H4.
      eexists.
      simpl. eapply tri_par;auto.
      eassumption.
      simpl.
      symmetry; apply Nat.add_assoc.
    ++ (* WITH *)
      apply IH with (L:= l1 :: L) (m:= plus (exp_weight l1) (L_weight L)) in H5;auto.
      apply IH with (L:= l2 :: L) (m:= plus (exp_weight l2) (L_weight L)) in H7;auto.
      destruct H5. destruct H7.
      eexists.
      simpl.
      apply tri_with;eassumption.
      lia.
      lia.
    ++  (* QUEST *)
      assert ((B ++ [F]) ++ [l] =mul= (B ++ [l]) ++ [F]) by solve_permutation.
      assert ( n0 |-F- (B ++ [l]) ++ [F] ; M ; UP (L ++ L')).
      eapply TriExchange.
      apply H4.
      auto.
      auto.
      apply IH with (m:= L_weight L) in H1 ;auto.
      destruct H1.
      eexists.
      simpl. eapply tri_quest ;auto.
      eassumption.
      rewrite Nat.add_comm; apply Nat.le_add_r.
Qed.


Theorem EquivAuxTop : forall B  L L' M ,   exists m, m |-F- B ; M ;  UP (L ++ [Top] ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent w .

  induction w as [| w' IH] using strongind;  intros M B L' L Hw ;  destruct L as [|l].
  + simpl.
    eexists.
    eapply tri_top;auto.
  + simpl in Hw. (* Heqw is inconsisten *)
    destruct l; simpl in Hw; inversion Hw.
  + simpl in Hw. inversion Hw.
  + destruct l;inversion Hw as [Hw'];auto.
    ++  (* ATOM *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [v ⁺] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* ATOM *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [v ⁻] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* TOP *)
      eexists. simpl. eapply tri_top.
    ++ (* bottom *)
      assert( exists m0 : nat, m0 |-F- B; M ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      destruct H.
      eexists. simpl. eapply tri_bot. eassumption.
    ++ (* Zero *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [0] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* One *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [1] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* tensor *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [l1 ** l2] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);auto.
      lia.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* Par *)
      assert( exists m0 : nat, m0 |-F- B; M ; UP ((l1 :: l2  :: L) ++ [⊤] ++ L')).
      apply IH with (m := plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L));subst;auto.
      simpl. lia.
      destruct H.
      eexists. simpl. eapply tri_par;auto. eassumption.
    ++ (* Oplus *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [l1 ⊕ l2] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      lia.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* with *)
      assert( exists m0 : nat, m0 |-F- B; M ; UP ((l1 ::L) ++ [⊤] ++ L')).
      apply IH with (m := plus (exp_weight l1) (L_weight L));auto.
      lia.
      assert( exists m0 : nat, m0 |-F- B; M ; UP ((l2 ::L) ++ [⊤] ++ L')).
      apply IH with (m := plus (exp_weight l2) (L_weight L));auto.
      lia.
      destruct H. destruct H0.
      eexists. simpl. eapply tri_with;auto;eassumption.
    ++ (* Bang *)
      assert( exists m0 : nat, m0 |-F- B; M ++ [! l] ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      lia.
      destruct H.
      eexists; simpl;eapply tri_store;auto;eassumption.
    ++ (* Quest *)
      assert( exists m0 : nat, m0 |-F- B ++ [l]; M ; UP (L ++ [⊤] ++ L')).
      apply IH with (m := L_weight L);subst;auto.
      lia.
      destruct H.
      eexists. simpl. eapply tri_quest;auto. eassumption.
Qed.

Ltac EquivAuxPosCases Heqw H IH H6 F L L' :=
  inversion Heqw; subst;
  simpl in H;
  inversion H;subst;
  apply IH with (m:= L_weight L)in H6 ;auto;
  destruct H6 as [m H6];
  assert( H1:  F::L ++ L' = [F] ++ (L ++ L'));auto;
  rewrite H1 in H6;
  eapply EquivAuxSync in H6;auto.


Theorem EquivAux : forall B L L' F M n, n |-F- B ; M ; UP (L ++ [F] ++ L')  -> exists m, m |-F- B ; M ;  UP(F :: L ++ L').
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent n .
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent w .

  induction w as [| w' IH] using strongind;  intros ;  destruct L as [|l].
  + simpl in H.
    simpl.
    eexists;eassumption.
  + inversion Heqw.
    generalize(exp_weight0 l);intros.
    lia.
  + simpl in H.
    simpl.
    eexists;eassumption.
  + destruct l; try(EquivAuxPosCases Heqw H IH H6 F L L').

    ++ (* Top *)
      assert (F :: (⊤ :: L) ++ L' = [F] ++ [⊤] ++ ( L ++ L')) by reflexivity.
      rewrite H0.
      apply EquivAuxTop.

    ++ (* bot *)

      inversion Heqw. subst.
      simpl in H.
      inversion H; try discriminate; subst.
      apply IH with (m:= L_weight L)in H4 ;auto.
      destruct H4.

      assert( F::L ++ L' = [F] ++ (L ++ L'));auto.
      rewrite H1 in H0.
      eapply EquivAuxBot in H0;auto.

    ++ (* tensor *)
      inversion Heqw. subst.
      simpl in H.
      inversion H;subst.
      apply IH with (m:= L_weight L)in H6 ;auto.
      destruct H6.

      assert( F::L ++ L' = [F] ++ (L ++ L'));auto.
      rewrite H1 in H0.
      eapply EquivAuxSync in H0;auto.
      lia.
    ++ (* par *)
      inversion Heqw. subst.
      simpl in H.
      inversion H; try discriminate; subst.
      apply IH with (L:= l1 :: l2 :: L) (m:= plus (plus (exp_weight l1)  (exp_weight l2)) ( L_weight L))in H4 ; auto.
      destruct H4.

      assert( F :: (l1 :: l2 :: L) ++ L' = [F] ++ [l1 ; l2] ++ (L ++ L'));auto.
      rewrite H1 in H0.
      eapply EquivAuxPar in H0;auto.
      simpl.
      lia.
    ++ (* OPLUS *)
      inversion Heqw. subst.
      simpl in H.
      inversion H;subst.
      apply IH with (m:= L_weight L)in H6 ;auto.
      destruct H6.

      assert( F::L ++ L' = [F] ++ (L ++ L'));auto.
      rewrite H1 in H0.
      eapply EquivAuxSync in H0;auto.
      lia.
    ++ (* with *)
      inversion Heqw. subst.
      simpl in H.
      inversion H; try discriminate; subst.
      apply IH with (L:= l1 :: L) (m:= plus (exp_weight l1) (L_weight L))in H5 ;auto.
      apply IH with (L:= l2 :: L) (m:= plus (exp_weight l2) (L_weight L))in H7 ;auto.

      destruct H5.
      destruct H7.
      assert( F :: (l1 :: L) ++ L' = [F] ++ [l1 ] ++ (L ++ L'));auto.
      assert( F :: (l2 :: L) ++ L' = [F] ++ [l2 ] ++ (L ++ L'));auto.
      rewrite H2 in H0.
      rewrite H3 in H1.


      eapply EquivAuxWith with (F:=l1) (G:=l2) in H0;eauto.
      lia.
      lia.
    ++ (* bang *)
      inversion Heqw. subst.
      simpl in H.
      inversion H;subst.
      apply IH with (m:= L_weight L)in H6 ;auto.
      destruct H6.

      assert( F::L ++ L' = [F] ++ (L ++ L'));auto.
      rewrite H1 in H0.
      eapply EquivAuxSync in H0;auto.
      lia.
    ++ (* quest *)
      inversion Heqw. subst.
      simpl in H.
      inversion H; try discriminate; subst.
      apply IH with (m:= L_weight L)in H4 ;auto.
      destruct H4.

      assert( F::L ++ L' = [F] ++ (L ++ L'));auto.
      rewrite H1 in H0.
      eapply EquivAuxQuest in H0;auto.
      lia.
Qed.





Theorem EquivUpArrow : forall B L L' M n, n |-F- B ; M ; UP L -> L =mul= L' -> exists m, m |-F- B ; M ;  UP L'.
Proof.
  intros.
  remember (L_weight L) as w.
  generalize dependent n .
  generalize dependent L .
  generalize dependent L' .
  generalize dependent B .
  generalize dependent M .
  generalize dependent w .

  induction w as [| w' IH] using strongind;  intros ;  destruct L as [|l].
  +assert (L'= []) by( apply emp_mult;auto).
   subst.
   eexists.
   eassumption.
  + inversion Heqw.
    generalize(exp_weight0 l);intros.
    lia.
  + assert (L'= []) by( apply emp_mult;auto).
    subst.
    eexists.
    eassumption.
  + destruct L' as [| l'].
    (* H0 is inconsisten *)
    apply DestructMulFalse in H0. contradiction.


    apply DestructMSet2 in H0 as Heq.

    destruct Heq as [Heq | Heq].
    ++ destruct Heq;subst.
       inversion H;subst.
       +++  (* top *)
         eexists. eapply tri_top.
       +++ (* bottom *)
         eapply IH with (L' :=L') in H6;auto.
         destruct H6.
         eexists. eapply tri_bot;eauto.
       +++ (* par *)
         eapply IH with (L' := F::G::L') in H6;auto.
         destruct H6.
         eexists. eapply tri_par;eauto.
         simpl in Heqw. inversion Heqw. simpl. lia.
       +++ (* with *)
         eapply IH with (m:= L_weight (F::L)) (L:= F ::L) (L' := F :: L') in H7;auto.
         eapply IH with (m:= L_weight (G::L)) (L := G :: L) (L' := G :: L') in H8;auto.
         destruct H7. destruct H8.
         eexists. eapply tri_with;eauto.

         simpl in Heqw. inversion Heqw. simpl. lia.
         simpl in Heqw. inversion Heqw. simpl. lia.
       +++  (* quest *)
         eapply IH with (m:= L_weight L) (L' :=L') in H6;auto.
         destruct H6.
         eexists. eapply tri_quest;eauto.
         simpl in Heqw. inversion Heqw. simpl. lia.
       +++  (* store *)
         eapply IH with (m:= L_weight L) (L' :=L') in H8;auto.
         destruct H8.
         eexists. eapply tri_store;eauto.
         simpl in Heqw. inversion Heqw.
         generalize(exp_weight0 l');intro.
         lia.
    ++
      destruct Heq as [L1 [L2 [L1' [L2' Heq]]]].

      destruct Heq as [Heq [Heq1 Heq2]];subst.

      inversion H;subst.
      +++ (* top *)

        eapply EquivAuxTop with (L:= l' :: L1').
      +++ (* bottom *)
        eapply IH with (m:= L_weight(L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H5 .
        destruct H5.
        simpl in H1.
        eapply EquivAuxBot with (L:= l' :: L1');eauto.

        simpl in Heqw. inversion Heqw. auto.
        rewrite <-Heq2.
        perm_simplify.
        reflexivity.
      +++ (* par *)
        eapply IH with (m:= L_weight(F :: G :: L1 ++ l' :: L2))
                         (L:=F :: G :: L1 ++ l' :: L2)
                         (L' := [l'] ++ L1' ++ [F ; G] ++ L2') in H5 .
        destruct H5.


        eapply EquivAuxPar with (L:= l' :: L1');eauto.
        simpl in Heqw. inversion Heqw. auto.  
        simpl. lia.   
        assert( L1' ++ [F; G] ++ L2' =mul= [F; G] ++ L1' ++ L2') by auto.  
        rewrite H1. rewrite <- Heq2.
        solv_P.
        apply union_right.
        change ([F; G]) with ([F] ++ [G]).
        solve_permutation.
        reflexivity.

      +++ (* with *)
        eapply IH with (m:= L_weight(F :: L1 ++ l' :: L2))
                         (L:=F :: L1 ++ l' :: L2)
                         (L' := [l'] ++ L1' ++ [F ] ++ L2') in H6 .
        eapply IH with (m:= L_weight(G :: L1 ++ l' :: L2))
                         (L:=G :: L1 ++ l' :: L2)
                         (L' := [l'] ++ L1' ++ [G ] ++ L2') in H7 .

        destruct H6. destruct H7.
        eapply EquivAuxWith with (L := l' :: L1'); eauto.
        simpl in Heqw. inversion Heqw. auto.
        simpl. lia.
        assert(HC : [l'] ++ L1' ++ [G] ++ L2' =mul= [l'] ++ [G] ++ L1' ++ L2') by solve_permutation.  
        rewrite HC. clear HC.
        solv_P.
        solve_permutation.
        reflexivity. 
        simpl in Heqw. inversion Heqw. simpl. lia.
        assert(HC : L1' ++ [F] ++ L2' =mul=  [F] ++ L1' ++ L2') by solve_permutation.  
        rewrite HC. clear HC.
        solv_P. 
        solve_permutation.
        reflexivity.

      +++ (* quest *)
        eapply IH with (m:= L_weight(L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H5 .
        destruct H5.
        eapply EquivAuxQuest with (L := l' :: L1');eauto.

        simpl in Heqw. inversion Heqw. auto.
        simpl. lia. 
        rewrite <- Heq2. solve_permutation.
        reflexivity.

      +++ (* copy *)
        eapply IH with (m:= L_weight(L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H7 .
        destruct H7.
        eapply EquivAuxSync with (L:=l' :: L1');eauto.

        simpl in Heqw. rewrite L_weightApp in Heqw. simpl in Heqw.
        rewrite L_weightApp.

        generalize(exp_weight0 l);intro.
        apply GtZero in H1.
        destruct H1.
        rewrite H1 in Heqw. simpl in Heqw.

        inversion Heqw.
        simpl. lia.
        rewrite <- Heq2.
        solve_permutation.

        reflexivity.
Qed.


(* Weakening *)
Theorem TriWeakening : forall B L F X n, n |-F- B ; L ; X -> n |-F- B ++ [F] ; L ; X.
  intros.
  generalize dependent L .
  generalize dependent B .
  generalize dependent F .
  generalize dependent X .
  generalize dependent n .
  induction n using strongind;intros.
  + (* Base *)
    inversion H;subst.
    ++ eapply tri_init1.
    ++ apply tri_init2 with (B' := B' ++ [F]);auto.
       rewrite H0.  solve_permutation.
    ++ eapply tri_one.
    ++ eapply tri_top.
  + (* Inductive *)
    inversion H0;subst.
    ++ eapply H in H3;auto; try lia.
       eapply H in H4;auto; try lia.
       eapply tri_tensor;eauto.
    ++ eapply H in H2;auto.
       eapply tri_plus1;eauto.
    ++ eapply H in H2;auto.
       eapply tri_plus2;eauto.
    ++ eapply H in H2;auto.
       eapply tri_bang;eauto.
    ++ eapply H in H3;auto.
       eapply tri_rel;eauto.
    ++ eapply H in H2;auto.
       eapply tri_bot;eauto.
    ++ eapply H in H2;auto.
       eapply tri_par;eauto.
    ++ eapply H in H2;auto; try lia.
       eapply H in H3;auto; try lia.
       eapply tri_with;eauto.
    ++  eapply H with (B := B ++ [F0]) (F:=F) in H2;auto.
        eapply tri_quest;auto.
        assert((B ++ [F]) ++ [F0] =mul= (B ++ [F0]) ++ [F]) by solve_permutation.
        rewrite H1. auto.
    ++  eapply H  with (L:= L ++ [F0]) (F:=F) in H3;auto.
        eapply tri_store;auto.
    ++ eapply H in H4;auto.
       eapply tri_dec1 with (F:=F0);eauto.
    ++ eapply H with (F:=F) in H4;auto.
       eapply TriExchange with (B := [F0] ++ B' ++ [F]);eauto.
       eapply tri_dec2 with (F:=F0);eauto.
       eapply TriExchange with (B' := [F0] ++ B' ++ [F]);eauto.
Qed.

(* Up and Down relation *)
Lemma UpExtension: forall B M L F n, lexpPos (M ++ [F]) -> n |-F- B; M ++ [F] ; UP L ->
                                                                                exists m, m<= S n /\ m |-F- B; M ; UP (L ++ [F]).
  intros.
  remember (L_weight L) as w.
  generalize dependent L .
  generalize dependent B .
  generalize dependent M .
  generalize dependent n .
  generalize dependent w .

  induction w as [| w' IH] using strongind .  intros n  M HPos  B L HD Hw.
  + (* w = 0 *)
    destruct L. (* L must be empty. The second case is trivial *)
    exists ((S n)).
    split;auto.
    simpl.
    eapply tri_store;auto.

    generalize(LPos3 M [F] (meq_refl (M ++ [F])) HPos);intro.
    inversion H;auto.

    simpl in Hw.
    apply exp_weight0LF in Hw;contradiction.

  + intros.
    destruct L. (* L cannot be empty *)
    inversion Heqw.
    inversion H0;auto;subst;inversion Heqw;subst.
    ++ (* top *)
      exists 0%nat;split;auto.
      eapply tri_top.
    ++ (* bot *)
      apply IH with (m:= L_weight L) in H5;auto.
      destruct H5 as [n'  [IHn IHd]].
      exists (S n');split;auto. lia. simpl. eapply tri_bot;auto.
    ++  (* PAR *)
      apply IH with (m:= plus (plus (exp_weight F0) (exp_weight G)) (L_weight L)) in H5;auto.
      destruct H5 as [n'  [IHn IHd]].
      exists (S n');split;auto. lia. simpl. eapply tri_par;auto.
      simpl. lia.
    ++ (* with *)
      apply IH with (m:= plus (exp_weight F0) (L_weight L)) in H6;auto.
      apply IH with (m:= plus (exp_weight G) (L_weight L)) in H7;auto.
      destruct H6 as [n'  [IHn IHd]].
      destruct H7 as [m'  [IHn' IHd']].
      simpl.

      exists (S (Nat.max n' m'));split;auto. simpl.
      apply le_n_S.
      rewrite Nat.succ_max_distr.
      apply Nat.max_le_compat;auto.

      eapply tri_with;auto.
      lia.
      lia.
    ++  (* quest *)
      apply IH with (m:= L_weight L) in H5;auto.
      destruct H5 as [n'  [IHn IHd]].
      exists (S n');split;auto. lia. simpl. eapply tri_quest;auto.
      lia.
    ++ (* Store *)
      assert(exists m0 : nat, m0 <= S n0 /\ m0 |-F- B; M ++ [l]; UP (L ++ [F])).
      apply IH with (m:= L_weight L);eauto using WeightLeq.
      apply LPos1 with (L:= [l] ++ (M ++ [F]));auto.
      rewrite <- app_assoc.
      solve_permutation.

      apply lexpPosUnion;auto.
      apply AsynchronousFlexpPos;auto.
      assert((M ++ [l]) ++ [F] =mul= (M ++ [F]) ++ [l]) by solve_permutation.
      rewrite H1;auto.

      destruct H1 as [n'  [IHn IHd]].
      exists (S n');split;auto. lia. simpl. eapply tri_store;auto.
Qed.


Lemma StoreInversion : forall n B M F,  n |-F- B; M; UP [F] -> PosOrPosAtom F -> n -1 |-F- B ; M ++ [F] ; UP [].
  intros.
  inversion H;subst;try(inversion H0);subst;simpl;try(rewrite Nat.sub_0_r);auto.
Qed.
Lemma StoreInversionL : forall n B M N L,  n |-F- B; M; UP (N ++ L) -> lexpPos N -> exists m, m |-F- B ; M ++ N ; UP L.
  intros.
  generalize dependent M.
  generalize dependent n.
  induction N;intros.
  + simpl in *.
    eexists.
    rewrite app_nil_r.
    eauto.
  + inversion H; subst; inversion H0; try discriminate.
    apply (IHN H2) in H7.
    destruct H7.
    eexists.
    assert( M ++ a :: N =mul=  (M ++ [a]) ++ N) as -> by solve_permutation.
    eassumption.
Qed.
