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
