(* Add LoadPath "../../".  *)
Require Export Multisets.
Require Export TriSystem.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Eqset.
Set Implicit Arguments.


(* Lemma MulSingleton : forall (F : lexp) M, [F] =mul= M -> M = [F].
  intros.
  
  induction M; intros.
  * apply emp_mult in H; auto.
  * symmetry in H. apply resolvers2 in H.
    destruct H.
    subst.
    auto.
Qed.

Lemma DestructMulFalse l L : l :: L =mul= [] -> False.
 Proof.
   intro H. 
   assert (l :: L =mul= []) by auto.
   symmetry in H. 
   eapply rem_to_union in H. simpl in H. 
   rewrite H in H0.
   eapply singleton_notempty; eauto.
 Qed.


Lemma Permutation_meq :
  forall (M N : list lexp), Permutation M N <-> M =mul= N.
Proof.

  split; intros H.
  -
    induction H; intros; auto.
    apply meq_trans with (N:=l'); auto.
  -
    revert N H.
    induction M; intros.
    symmetry in H.
    rewrite  emp_mult in H; auto.
    subst. auto.
    
    assert (H1: [a] ++ M =mul= N) by apply H.
    apply meq_cons_In in H1.
    apply In_to_in in H1.
    destruct (In_split _ _ H1) as (h2,(t2,H2)).
    subst N.
    apply Permutation_cons_app.
    apply IHM.
    admit.
    (*eapply permut_remove_hd with a. ; auto.
    exact eq_linear. *)
Admitted.

 

Lemma ListMSetEq1: forall A M L, A :: M ++ L =mul= M ++ (A :: L).
  intros.
  assert(A :: M ++ L = [A] ++ M ++ L) as H1 by reflexivity.
  assert(M ++ (A :: L) = M ++ ( [A] ++ L)) as H2 by reflexivity.
  rewrite H1. rewrite H2.
  solve_permutation.
Qed.

Lemma ListMSetEq2: forall F M L, (M ++ L) ++ [F] =mul= F :: L ++ M.
  intros.
  solve_permutation.
Qed.



Lemma  ListMSetEq3: forall F M L, (F :: M) ++ L =mul= [F] ++ M ++ L.
  intros. simpl. auto.
Qed.


Lemma DestructMSet: forall   F G M1 M2,
  [F] ++ M1 =mul= [G] ++ M2 ->
  (( F = G /\ M1 =mul= M2 )  \/
  exists M2', M2 =mul= [F] ++ M2' /\ M1 =mul= [G] ++ M2').
Proof.
  intros.
  destruct (eqA_dec F G).
  - left.
    (*
    rewrite e in H.
    simpl_cases4.
    split; auto.
  - right.
    simpl_cases2.
    eexists ; eauto.
Qed.*)
Admitted.



 Lemma member_list : forall a L,
    a € L -> exists P1 P2, L = P1 ++ [a] ++ P2.
 Proof.
   intros.
   eapply in_split.
   apply In_to_in.
   auto.
 Qed. 
 
 Lemma DestructMSet2_aux a L M: L =mul= [a] ++ M -> 
          exists T1 T2, L = T1 ++ [a] ++ T2.
Proof.
  intros.
  induction M.
  - rewrite app_nil_r in H. 
    symmetry in H.
    apply MulSingleton in H.  
    do 2 eexists [].
    simpl; auto.
  - assert (member a L) as Hm.
    rewrite H.
    apply In_union_or.
    right. apply member_unit.
    auto.
    apply member_list in Hm.
    auto.
Qed.

Lemma DestructMSet2' l L l' L' x:  L =mul= [l'] ++ x -> L' =mul= [l] ++ x ->
          (exists L1 L2 L1' L2', L= L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2').
  intros.
  apply DestructMSet2_aux in H.
  apply DestructMSet2_aux in H0.
  do 2 destruct H.
  do 2 destruct H0.
  exists x0, x1, x2, x3.
  auto.
Qed.

Lemma DestructMSet2 : forall l L l' L', l :: L =mul= l' :: L' ->
                                        (l = l' /\ L =mul= L') \/
                                        (exists L1 L2 L1' L2', L= L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2' /\ L1 ++ L2 =mul= L1' ++ L2' ) .
 intros.
  change (l :: L =mul= l' :: L') with ([l] ++ L =mul= [l'] ++ L') in H.
  destruct (eqA_dec l l'); [left | right].
  (*
  * rewrite e in H.
    simpl_cases4.
    split; auto. 
  *
  simpl_cases2.
  assert (L' =mul= {{l}} ++ x) by auto.
  assert (L =mul= {{l'}} ++ x) by auto.
  
  apply DestructMSet2_aux in H.
  apply DestructMSet2_aux in H0.
   do 2 destruct H.
  do 2 destruct H0.
  exists x2, x3, x0, x1.
  split; auto.
  split; auto.
  change (x0 ++ [l] ++ x1) with (x0 ++ ({{l}} ++ x1)) in H.
  change (x2 ++ [l'] ++ x3) with (x2 ++ ({{l'}} ++ x3)) in H0.
  rewrite H0 in H2.
  rewrite H in H1.
  rewrite union_perm_left in H2, H1.
  apply right_union in H1.
  apply right_union in H2.
  rewrite H1, H2. auto.
Qed.*)
  Admitted.

Lemma EmptyMS : forall F (M : list lexp), [] = M ++ [F] -> False.
  intros.
  symmetry in H.
  apply app_eq_nil in H.
  inversion H.
  inversion H1.
Qed. *)


Ltac simpl_union_context := 
match goal with
| [ H : [?b] ++ ?M =mul= [?a] ++ ?L |- _ ] =>  
  apply DestructMSet in H; destruct H as [Hten1 | Hten2 ];
  [ destruct Hten1 as [HeqE HeqM] | destruct Hten2 as [L1 Hten2]; destruct Hten2]
| [ H : [?b] ++ ?M =mul= ?a :: ?L |- _ ] =>  
  apply DestructMSet in H; destruct H as [Hten1 | Hten2 ];
  [ destruct Hten1 as [HeqE HeqM] | destruct Hten2 as [L1 Hten2]; destruct Hten2]
| [ H : ?M ++ ?N =mul= [?a] ++ ?x |- _ ] =>
  assert ((exists L1, M =mul= [a] ++ L1) \/ (exists L2, N =mul= [a] ++ L2)) as Hten by refine (solsls _ _ H);
  destruct Hten as [Hten1 | Hten2];
  [ destruct Hten1 as [L1 HL1]; assert (x =mul= N ++ L1) by refine (solsls2 _ H HL1) |
    destruct Hten2 as [L2 HL2]; rewrite union_comm_app in H;
    assert (x =mul= M ++ L2) by refine (solsls2 _ H HL2); rewrite union_comm_app in H
  ]

end.
      
Ltac contradiction_multiset := 
repeat
match goal with
  | [ H : [?l] ++ ?L =mul= [] |- _ ] => 
    apply DestructMulFalse in H; contradiction
  | [ H : ?L ++ [?l] =mul= [] |- _ ] => 
    rewrite union_comm_app in H
  | [ H : [] =mul= [?l] ++ ?L |- _ ] => 
    symmetry in H      
  | [ H : [] =mul= ?L ++ [?l] |- _ ] => 
    symmetry in H        
end.
