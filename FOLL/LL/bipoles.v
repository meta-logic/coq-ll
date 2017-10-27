Add LoadPath "../" .
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.


Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.StructuralRules.
Require Export LL.Multisets.


(* ************ *)
Require Import ZArith.
Open Scope Z_scope.
(* ************ *)
Module Bipole (DT : Eqset_dec_pol).
  Module Export Sys :=  SqSystems DT.

  (* Monopoles *)
  Inductive MonopoleI : Lexp -> Prop  :=
  | mi_top : MonopoleI Top
  | mi_bot : MonopoleI Bot
  | mi_par : forall F G, MonopoleI F -> MonopoleI G -> MonopoleI (Par F G)
  | mi_with : forall F G, MonopoleI F -> MonopoleI G -> MonopoleI (With F G)
  | mi_questA : forall A, MonopoleI (Quest (Atom A))
  | mi_questP : forall A, MonopoleI (Quest (Perp A))
  | mi_forall : forall FX, (forall t, MonopoleI (Subst FX t)) -> MonopoleI (Fx FX)
  | mi_atom : forall A, IsPositiveAtom A -> MonopoleI (A).
  
  Hint Constructors MonopoleI .
  Ltac prove_monopole := repeat(compute ; constructor) .

  Example e1: forall A, IsPositiveAtom (Atom A) -> MonopoleI (With (? (Atom A)) (F{ fun _ x => quest (perp (a1 2 (var x)  )) })).
  Proof with prove_monopole.
    intros ... 
  Qed.

  Lemma PositiveNegativeFalse: forall A (P:Prop),  IsNegativeAtom A -> IsPositiveAtom A -> P.
    intros.
    assert (False).
    eapply NegPosAtomContradiction;eauto.
    apply IsNegativePosOrNegAtom in H.
    auto.
    contradiction.
  Qed.
    
  
  Theorem MonopoleRelease :  forall B M F, MonopoleI F ->
                                           |-F- B ; M ; DW (F) -> |-F- B ; M ; UP [F] .
  Proof with InvTac.
    intros.
    inversion H;subst;(inversion H0;InvTac);subst;
      try(
          match goal with
          | [H: IsPositiveAtom ?F, H' : IsNegativeAtom ?F |- _] => eapply PositiveNegativeFalse;eauto
          end);
      try(
          match goal with
          | [H: IsPositiveAtom ?F |- _] => inversion H;InvTac
          end).
  Qed.

  (* Assuming that exists are in the outermost position *)
  Inductive BipoleI : Lexp -> Prop := 
  | bi_ex : forall FX,  (forall t, BipoleB (Subst FX t)) -> BipoleI (Ex FX)
  | bi_ten : forall F G, BipoleB F -> BipoleB G -> BipoleI (Tensor F G)
  | bi_plus : forall F G, BipoleB F -> BipoleB G -> BipoleI (Plus F G)
  | bi_bang : forall F, MonopoleI F -> BipoleI (Bang F)
  with
  BipoleB : Lexp -> Prop :=
  | bi_mon : forall F, MonopoleI F -> BipoleB F
  | bi_neg : forall A, IsNegativeAtom A -> BipoleB A
  | bi_bi : forall F, BipoleI F -> BipoleB F.
                                              
  
  Hint Constructors BipoleI BipoleB .
  Ltac prove_biP := constructor;InvTac;try(intro;autounfold;simpl); try eapply bi_bi.
                                                
  Example bleft : forall C n, isPositive n = true ->  BipoleI (fun T:Type => tensor (perp (a1 n (cte C))) top).
  Proof with InvTac.
    intros.
    constructor ...
    eapply bi_neg ...
  Qed.

  Example init : forall n m n' m', isPositive n = true -> isPositive m = true ->
                          BipoleI( Ex (fun _ x =>
                                 tensor
                                   (tensor  (perp (a1 n (fc1 n' (var x)))) (perp (a1 m (fc1 m' (var x))))
                                   ) top)).
  Proof with InvTac.
    intros.
    prove_biP.
    prove_biP.
    constructor.
    eapply bi_neg ...
    eapply bi_neg ...
  Qed.  
 
  Example cleft : forall n n' ,  isPositive n = true ->
    BipoleI(
        fun T:Type => ex(fun x :T => ex( fun y:T =>
                                           tensor
                                             (perp (a1 n (fc2 n' (var x) (var y))))
                                             ( par (atom (a1 n (var x))) (atom (a1 n (var y))) ) ))).
  Proof with InvTac.
    intros.
    prove_biP.
    prove_biP.
    constructor ...
    eapply bi_neg ...
    eapply bi_mon ...
    prove_monopole ...
  Qed.
    
  
  Example cright : forall n m,  isPositive n = true ->
                              BipoleI(
                                  Ex (fun _ x => ex( fun y =>
                                                       tensor
                                                         (perp (a1 n (fc2 m (var x) (var y))))
                                                         ( witH
                                                             (atom (a1 n (var x)))
                                                             (atom (a1 n (var y)))
                                ) ))).
  Proof with InvTac.
    intros.
    prove_biP.
    prove_biP.
    constructor ...
    eapply bi_neg ...
    eapply bi_mon ...
    prove_monopole ...
  Qed.   

  Lemma BipoleAtom : forall F, BipoleI F -> ~ IsPositiveAtom F.
  Proof with InvTac.
    intros F H Hneg.
    inversion H; subst;InvTac;(try inversion Hneg;InvTac).
  Qed.

  (* A more restricted biPole --used in rules -- *)
  Inductive BipoleRM : Lexp -> Prop := 
  | brm_ex : forall FX,  (forall t, BipoleRM (Subst FX t)) -> BipoleRM (Ex FX)
  | brm_head : forall A G,  IsNegativeAtom A -> MonopoleI G ->  BipoleRM (Tensor A G).
  Hint Constructors BipoleRM .

  Lemma BipoleRM_Bipole : forall F, BipoleRM F -> BipoleI F .
  Proof with InvTac.
    intros .
    induction H.
    prove_biP.
    prove_biP.
  Qed.
 
  Definition ListBipoles L := Forall (fun F => (BipoleI F)) L.
  
  Definition ListPosAtoms L := Forall (fun F => (IsPositiveAtom F)) L.
  Hint Unfold ListBipoles ListPosAtoms .
  
  Definition CLEFT := fun T:Type => ex(fun x :T => ex( fun y:T =>
                                                        tensor
                                                          (perp (a1 1 (fc2 3 (var x) (var y))))
                                                             ( par (atom (a1 1 (var x))) (atom (a1 1 (var y))) ) )).
  Hint Unfold CLEFT . 

  Lemma EqFx : forall FX FX',
      E{ FX} = (fun T : Type => ex (FX' T)) -> FX = FX'.
    intros.
    extensionality T.
    assert( (E{ FX}) T = (fun T : Type => ex (FX' T)) T).
    rewrite H;auto.
    inversion H0.
    auto.
  Qed.

  Ltac clearEx H :=
    apply EqFx in H;subst.

  Lemma EqTensor : forall F1 F2,
      (fun T : Type => tensor (F1 T) (F2 T)) = Tensor F1 F2.
    intros.
    reflexivity.
  Qed.

  Lemma EqPar : forall F1 F2,
      (fun T : Type => par (F1 T) (F2 T)) = Par F1 F2.
    intros.
    reflexivity.
  Qed.
   
  
  Lemma EqPerp : forall t n,
      (fun T : Type => perp (a1 n (t T))) = Perp (A1 n t) .
    intros.
    reflexivity .
  Qed.

  Lemma EqAtom : forall t n,
      (fun T : Type => atom (a1 n (t T))) = Atom (A1 n t) .
    intros.
    reflexivity .
  Qed.

 
  Lemma EqFC2 : forall n t t',
      
      (fun T : Type => fc2 n (t T) (t' T)) = FC2 n t t'.
    intros;reflexivity.
  Qed.


  Lemma TermFlatten: forall (t:Term) (T:Type) ,   flattenT (t (term T)) =  (t T).
  intros.
  assert(ClosedT t) by apply ax_closedT.
  induction H; try(reflexivity).
  simpl. rewrite IHClosedT. auto.
  simpl. rewrite IHClosedT1. rewrite IHClosedT2. auto.
  Qed. 


  Lemma TermFlattenF : forall t : Term ,
      (fun T : Type => flattenT (t (term T))) = t.
    intros.
    extensionality T.
    apply TermFlatten.
  Qed.
 
     
  Ltac cleanTerm H := repeat (rewrite EqTensor in H + rewrite EqPerp in H +  rewrite EqFC2 in H + rewrite EqPar in H + rewrite TermFlattenF in H + rewrite EqAtom in H).
   
  Lemma ApplyingBipoleRM : forall Theory M F,
      ListBipoles Theory -> ListPosAtoms M -> BipoleRM F ->
      |-F- Theory ; M ; DW CLEFT ->
                        False .
  Proof with InvTac.
    intros.
    autounfold in *.
    inversion H2;subst ...
    clearEx H3.
    compute in H6.
    inversion H6;subst ... 
    clearEx H3.
    unfold Subst in H7.
    simpl in H7.
    cleanTerm H7.
    inversion H7 ...
    inversion H10;subst ...
    inversion H12...
    inversion H13;subst ...
    inversion H16;subst ...
  Admitted.
    

End Bipole.