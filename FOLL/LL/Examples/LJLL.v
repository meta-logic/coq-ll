(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** LJ into LL 
We specify the system LJ for intuitionistic propositional logic. We encode that system as a Linear Logic theory and we prove the adequacy of that encoding. For that, we use the techniques described here #<a href="http://www.sciencedirect.com/science/article/pii/S0304397512010894">[Miller and Pimentel 13]# and the formalization of the focused system for Linear Logic. 
 *)

Add LoadPath "../../" . 
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
Require Export LL.SequentCalculiBasicTheory.
Require Export LL.Multisets.
Require Export LL.StrongInduction.
Require Export LL.FLLMetaTheory.

Hint Resolve Max.le_max_r.
Hint Resolve Max.le_max_l.


Module PL.
  Inductive LForm :Set :=
  | bot (* false *)
  | atom : nat -> LForm (* atomic propositions are named with a natural number *)
  | conj : LForm -> LForm -> LForm (* conjunction *)
  | disj : LForm -> LForm -> LForm (* disjunction *)
  | impl : LForm -> LForm -> LForm (* intuitionistic implication *)
  .
  
  Theorem LForm_dec_eq : forall F G : LForm, {F = G} + {F <> G}.
    induction F;destruct G;try(right;discriminate);
      try(
          generalize(IHF1 G1);intro;
          generalize(IHF2 G2);intro;
          destruct H;destruct H0;subst;try(right;intro;inversion H;contradiction);auto).
    left;auto.
    generalize(eq_nat_decide n n0);intro Hn.
    destruct Hn.
    apply eq_nat_is_eq in e;subst;auto.
    right; intro;rewrite eq_nat_is_eq in n1.
    inversion H.
    contradiction.
  Qed.


  Module F_dec <: Eqset_dec_pol.
    Definition A := LForm.
    Definition eqA_dec := LForm_dec_eq.
    Fixpoint isPositive (n:nat) :=
      match n with
      | 0%nat => false
      | 1%nat => true
      | S (S n) => isPositive n
      end.
  End F_dec.

  Declare Module MSFormulas : MultisetList F_dec.
  Export MSFormulas. 
  
  
  Reserved Notation " L ';' n '|-P-' F" (at level 80).
  Inductive sq : list LForm -> nat -> LForm -> Prop :=
  | init : forall (L L' :list LForm) a, L =mul= atom a :: L' -> L ; 0 |-P- atom a
  | botL : forall (L L' :list LForm) G , L =mul= bot :: L' -> L ; 0 |-P- G
  | cR : forall L F G n m , L ; n |-P- F -> L ; m |-P- G -> L ; S (max n m) |-P- conj F G
  | cL : forall L G G' F L' n, L =mul= (conj G G') :: L' -> G :: G' :: L' ; n |-P- F -> L ; S n |-P- F
  | dR1 : forall L F G n, L ;  n |-P- F -> L ; S n |-P- disj F G
  | dR2 : forall L F G n, L ;  n |-P- G -> L ; S n |-P- disj F G
  | dL : forall L L' F G H n m, L =mul= disj F G :: L' ->  F :: L' ;  n |-P- H -> G :: L' ;  m |-P- H  -> L ;  S (max n m) |-P- H 
  | impR : forall L F G n , F :: L ; n |-P- G ->  L ; S n |-P- impl F G
  | impL : forall L L' F G H n m,  L =mul= impl F G :: L' -> L ; n |-P- F -> G :: L' ; m |-P- H -> L ; S (max n m)|-P- H
  where "L ; n |-P- F" := (sq L n F).

  Example Ex1: exists n, [ (atom 3)] ;n|-P- impl (conj (atom 1) (atom 2)) (conj (atom 2) (conj (atom 3) (atom 1))).
  eexists.
  eapply impR;eauto.
  eapply cL;eauto.
  eapply cR;eauto.
  eapply init;eauto.
  eapply cR;eauto.
  eapply init;eauto.
  eapply init;eauto.
  Qed.

  (* Exchange *)
  Theorem Exch : forall L L' F n, L =mul= L' -> L ; n |-P-F -> L' ;n  |-P-F.
    intros.
    generalize dependent L.
    generalize dependent L'.
    generalize dependent F.
    induction n using strongind;intros;subst.
    + (* base *)
      inversion H0;subst.
      rewrite H in H1.
      eapply init;auto.
      
      rewrite H in H1.
      eapply botL;auto.
    + (* inductive *)
      inversion H1;subst.
      
      (* cR *) 
      apply cR.
      eapply H with (L:=L);auto.
      eapply H with (L:=L);auto.
      
      (* cL *)
      rewrite H0 in H3.
      eapply cL;auto.

      (* dR1 *)
      apply H with (L' := L') in H4;auto.
      apply dR1;auto.

      (* dR2 *)
      apply H with (L' := L') in H4;auto.
      apply dR2;auto.

      (* dL *)
      rewrite H0 in H4.
      eapply dL;eauto.
      
      
      (* impl R *)  
      eapply H with (L' := F0 :: L') in H4;auto.
      eapply impR;auto.
      
      (* impl L *)
      eapply H with (L' := L') in H5;auto.
      eapply impL;eauto.
  Qed.

  Definition meqPL := meq.

  (*!! Why should I prove again these lemmas ? *)
  (* B: Just use the dot notation for multisets *)

  Lemma Contradiction_mset : forall a L,  meq []  (a :: L) -> False.
    intros.
    contradiction_multiset.
  Qed.
  Lemma Contradiction_mset' : forall a L,  meq  (a :: L) [] -> False.
    intros.
    symmetry in H.
    contradiction_multiset.
  Qed.
  
End PL.

Export ListNotations.

Notation " L  '|-P-' n ';' F" := (PL.sq L n F) (at level 80).

Module SLL := FLLMetaTheory PL.F_dec.
Export SLL.

(* Numbers for the predicates *)
Definition rg := 1%nat. (* UP PREDICATE *)
Definition lf := 3. (* DOWN predicate *)
(* Numbers for the functional constructors *)
Definition bt := 0%nat. (* bottom *)
Definition pr := 1%nat. (* atoms / propositions *)
Definition cj := 2%nat. (* conjunction *)
Definition dj := 3%nat. (* disjunction *)
Definition im := 4%nat. (* implication *)

(* Bottom Left *)
Definition  BLEFT :Lexp := fun T:Type => tensor (perp (a1 lf (cte PL.bot))) top.
(* Init *)
Definition  INIT :Lexp :=
  Ex (fun _ x =>
        tensor 
          (tensor  (perp (a1 rg (fc1 pr (var x)))) (perp (a1 lf (fc1 pr (var x))))
          ) top).

(* Conjunction Left *)
Definition  CLEFT :Lexp := fun T:Type =>
                             ex(fun x :T => ex( fun y:T =>
                                                  tensor
                                                    (perp (a1 lf (fc2 cj (var x) (var y))))
                                                    ( par
                                                        (atom (a1 lf (var x)))
                                                        (atom (a1 lf (var y))) ) )).
(* conjunction Right *)
Definition  CRIGHT :Lexp :=
  Ex (fun _ x => ex( fun y =>
                       tensor
                         (perp (a1 rg (fc2 cj (var x) (var y))))
                         ( witH
                             (atom (a1 rg (var x)))
                             (atom (a1 rg (var y)))
     ) )).

(* Disjuntion Right1 *)
Definition DRIGHT1  :Lexp :=
  Ex (fun _ x => ex ( fun y => tensor
                                 (perp (a1 rg (fc2 dj (var x) (var y))))
                                 (atom (a1 rg (var x))))).
(* Disjuntion Right2 *)
Definition DRIGHT2  :Lexp :=
  Ex (fun _ x => ex ( fun y => tensor
                                 (perp (a1 rg (fc2 dj (var x) (var y))))
                                 (atom (a1 rg (var y))))).

(* Disjunction Left *)
Definition DLEFT  :Lexp := Ex (fun _ x => ex ( fun y =>
                                                 tensor
                                                   (perp (a1 lf (fc2 dj (var x) (var y))))
                                                   ( witH (atom (a1 lf (var x))) (atom (a1 lf (var y))) ))).

(* Implication Right *)
Definition IRIGHT  :Lexp := Ex (fun _ x => ex ( fun y => tensor
                                                           (perp (a1 rg (fc2 im (var x) (var y))))
                                                           (par
                                                              (atom (a1 lf (var x)))
                                                              (atom (a1 rg (var y)))))).
(* Implication Left *)
Definition ILEFT  :Lexp :=
  Ex (fun _ x =>
        ex( fun y => ex( fun z =>
                           tensor
                             ( tensor
                                 (perp (a1 lf (fc2 im (var x) (var y))))
                                 (perp (a1 rg (var z)))
                             )
                             ( witH
                                 (par
                                    (atom (a1 rg (var x)))
                                    (atom (a1 lf (fc2 im (var x) (var y)))))
                                 (par
                                    (atom (a1 lf (var y)))
                                    (atom (a1 rg (var z)))))))).

Definition Theory := BLEFT :: INIT :: CRIGHT :: CLEFT :: DRIGHT1 :: DRIGHT2 :: DLEFT :: IRIGHT :: ILEFT :: nil.
Hint Unfold Theory .
   

Example translation:  |-F- Theory ; [Atom (A1 rg (FC2 cj (FC1 pr (Cte (PL.atom 1))) (FC1 pr (Cte (PL.atom 2))))) ;
                                       Atom (A1 lf (FC2 cj (FC1 pr (Cte (PL.atom  1)))
                                                        (FC1 pr (Cte (PL.atom 2))) )) ]  ; UP []. 
Proof with unfold Theory in *;solveF.
  eapply tri_dec2 with (F:=CLEFT) (B' :=  [BLEFT; INIT; CRIGHT; DRIGHT1; DRIGHT2; DLEFT; IRIGHT; ILEFT])...
  
  eapply tri_ex with (t:= (FC1 pr (Cte (PL.atom 1)))).
  eapply tri_ex with (t:= (FC1 pr (Cte (PL.atom 2)))).                            
  simpl.                                                                                                          

  eapply tri_tensor with (N:= [(A1 lf (FC2 cj (FC1 pr (Cte (PL.atom 1))) (FC1 pr (Cte (PL.atom 2))))) ⁺])           
                           (M:= [(A1 rg (FC2 cj (FC1 pr (Cte (PL.atom 1))) (FC1 pr (Cte (PL.atom 2))))) ⁺]) ...                              
  apply Init1 ...                                                                                                     
  apply tri_rel ...
  NegPhase.
  eapply tri_dec2 with (F:=CRIGHT) ...

  eapply tri_ex with (t:= FC1 pr (Cte (PL.atom 1))).
  eapply tri_ex with (t:= FC1 pr (Cte (PL.atom 2))).                                                                                
  eapply tri_tensor with
  (N:= [(A1 rg (FC2 cj (FC1 pr (Cte (PL.atom 1))) (FC1 pr (Cte (PL.atom 2))))) ⁺])
    (M:=[Atom (A1 lf (FC1 pr (Cte (PL.atom 1)))) ; Atom (A1 lf (FC1 pr (Cte (PL.atom 2)) ))]);eauto ...
  eapply Init1 ...
  eapply tri_rel ...
  eapply tri_with ; eapply tri_store ...
  
  + (* branch 1 *)
    eapply tri_dec2 with (F:=INIT);eauto ... 
    eapply tri_ex with (t:= (Cte (PL.atom 1))).
    eapply tri_tensor with
    (N:= [(A1 lf (FC1 pr (Cte (PL.atom 1)))) ⁺ ;Atom (A1 rg (FC1 pr (Cte (PL.atom 1))))  ])
      (M:=  [(A1 lf (FC1 pr (Cte (PL.atom 2)))) ⁺]) ...
    
    eapply tri_tensor with (M:= [(A1 lf (FC1 pr (Cte (PL.atom 1)))) ⁺])
                             (N:= [(A1 rg (FC1 pr (Cte (PL.atom 1)))) ⁺]) ...
    apply Init1 ...
    apply Init1 ... 
    
  + (* branch 2 *)          
    eapply tri_dec2 with (F:=INIT) ...
    eapply tri_ex with (t:= (Cte (PL.atom 2))).
    eapply tri_tensor with (N:= [(A1 lf (FC1 pr (Cte (PL.atom 2)))) ⁺ ;
                                 Atom (A1 rg (FC1 pr (Cte (PL.atom 2)) ))])                                          (M:=  [(A1 lf (FC1 pr (Cte (PL.atom 1)))) ⁺]) ...        

    eapply tri_tensor with (N:= [(A1 rg (FC1 pr (Cte (PL.atom 2)))) ⁺])
                             (M:= [(A1 lf (FC1 pr (Cte (PL.atom 2)))) ⁺]) ...
    apply Init1 ...
    apply Init1 ...
Qed.

Fixpoint encodeTerm (F: PL.LForm) :=
  match F with
  | PL.bot => (Cte PL.bot)
  | PL.atom x => FC1 pr (Cte (PL.atom x))
  | PL.conj x y => FC2 cj (encodeTerm x) (encodeTerm y)
  | PL.disj x y => FC2 dj (encodeTerm x) (encodeTerm y)
  | PL.impl x y => FC2 im (encodeTerm x) (encodeTerm y)
  end.


Definition encodeFL (F: PL.LForm) := Atom (A1 lf ( encodeTerm F)). (* left encoding *)
Definition encodeFR (F: PL.LForm) := Atom (A1 rg ( encodeTerm F)). (* right encoding *)
Hint Unfold encodeFL encodeFR.

Definition encodeList := map encodeFL.

Definition encodeSequent (L: list PL.LForm) (F: PL.LForm) :=
  |-F- Theory ; (encodeFR F) :: encodeList L ; UP [].
Hint Unfold encodeSequent.

Inductive IsPositiveAtomL : list Lexp -> Prop :=
| ispL_nil : IsPositiveAtomL nil
| ispL_cons : forall F L, IsPositiveAtom F -> IsPositiveAtomL L -> IsPositiveAtomL (F ::L).

Lemma encodePositive: forall  L F, IsPositiveAtomL ((encodeFR F) :: encodeList L).
  intros.
  constructor.
  + destruct F;constructor;auto.
  + induction L.
    ++ constructor.
    ++ simpl.
       constructor;[ destruct a; constructor;auto | auto].
Qed.

Lemma PositiveIn:  forall L F, IsPositiveAtomL L -> In F L -> IsPositiveAtom F.
  intros.
  induction L.
  inversion H0.
  inversion H0;subst.
  inversion H;auto.
  apply IHL;auto.
  inversion H;auto.
Qed.

(* Inversion of EncTerm *)

Section InversionTerm.
  Ltac InvTermAux :=
    try(match goal with
        |[H : Cte ?t = FC1 ?n ?t' |- _] => assert(Cte t <> FC1 n t') by (eapply Terms_cte_fc1;eauto);contradiction
        |[H : Cte ?t = FC2 ?n ?t' ?t'' |- _] => assert(Cte t <> FC2 n t' t'') by (eapply Terms_cte_fc2;eauto);contradiction
        |[H :  FC1 ?n ?t = FC2 ?n' ?t' ?t'' |- _] => assert(FC1 n t  <> FC2 n' t' t'') by (eapply Terms_fc1_fc2;eauto);contradiction
        |[H :  FC2 ?n' ?t' ?t'' = FC1 ?n ?t |- _] => symmetry in H;assert(FC1 n t  <> FC2 n' t' t'') by (eapply Terms_fc1_fc2;eauto);contradiction
        end).
  
  Lemma InvEncTermAt : forall F t,  encodeTerm F = FC1 pr t -> exists a, F = PL.atom a.
    intros.
    destruct F;simpl in H; InvTermAux.
    apply F1Eqt in H;eauto.
  Qed.
  
  Lemma InvEncTermAtAt : forall F t n,  (A1 n (encodeTerm F)) ⁺ = ((A1 n (FC1 pr t)) ⁻)° -> exists a, F = PL.atom a.

    intros.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    apply InvEncTermAt in H1.
    auto.
  Qed.
  
  Lemma InvEncTermCj : forall F t t', encodeTerm F = FC2 cj t t' -> exists G G', F = PL.conj G G'.
    intros.
    destruct F;simpl in H;InvTermAux.
    eexists;eauto.
    apply F2Eqn in H. unfold dj in H. unfold cj in H. firstorder.
    apply F2Eqn in H. unfold im in H. unfold cj in H. firstorder.
  Qed.
  
  Lemma InvEncTermCjAt : forall F t t0 n,  (A1 n (encodeTerm F)) ⁺ = ((A1 n (FC2 cj t t0)) ⁻)° -> exists G G', F = PL.conj G G'.
    intros.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    eapply InvEncTermCj;eauto.
  Qed.

  Lemma InvFLCj : forall G G' t t', encodeFL (PL.conj G G') = ((A1 lf (FC2 cj t t')) ⁻)° -> encodeFL G = Atom (A1 lf t) /\ encodeFL G' = Atom (A1 lf t').
    intros.
    unfold encodeFL in H.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    simpl in H1.
    apply F2Eqt1 in H1 as Ht.
    apply F2Eqt2 in H1 as Ht'.
    unfold encodeFL.
    rewrite Ht. rewrite Ht'.
    split;auto.
  Qed.

  Lemma InvFLDj : forall G G' t t', encodeFL (PL.disj G G') = ((A1 lf (FC2 dj t t')) ⁻)° -> encodeFL G = Atom (A1 lf t) /\ encodeFL G' = Atom (A1 lf t').
    intros.
    unfold encodeFL in H.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    simpl in H1.
    apply F2Eqt1 in H1 as Ht.
    apply F2Eqt2 in H1 as Ht'.
    unfold encodeFL.
    rewrite Ht. rewrite Ht'.
    split;auto.
  Qed.

  Lemma InvDjTerm : forall F t t', encodeTerm F = FC2 dj t t' ->
                                   exists G G', F = PL.disj G G' /\ encodeFR G = Atom (A1 rg t) /\ encodeFR G' = Atom (A1 rg t').
    intros.
    destruct F;simpl in H ;InvTermAux.
    apply F2Eqn in H. unfold dj in H. unfold cj in H. firstorder.
    apply F2Eqt1 in H as Ht1.
    apply F2Eqt2 in H as Ht2;subst.
    eexists. eexists;eauto.
    apply F2Eqn in H. unfold dj in H. unfold im in H. firstorder.
  Qed.

  Lemma InvEncTermDjAt : forall F t t' n,  (A1 n (encodeTerm F)) ⁺ = ((A1 n (FC2 dj t t')) ⁻)° -> exists G G', F = PL.disj G G' /\ encodeFR G = Atom (A1 rg t) /\ encodeFR G' = Atom (A1 rg t').
    intros.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    
    eapply InvDjTerm;eauto.
  Qed.
  
  Lemma InvDj: forall F t t' ,  encodeFR F = ((A1 rg (FC2 dj t t')) ⁻)° -> exists G G', F = PL.disj G G' /\ encodeFR G = Atom (A1 rg t) /\ encodeFR G' = Atom (A1 rg t').
    intros.
    unfold encodeFR in H. 
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    apply InvDjTerm;auto.

  Qed.

  Lemma InvImTerm : forall F t t', encodeTerm F = FC2 im t t' ->
                                   exists G G', F = PL.impl G G' /\ encodeFR G = Atom (A1 rg t) /\ encodeFR G' = Atom (A1 rg t').
    intros.
    destruct F;simpl in H ;InvTermAux.
    apply F2Eqn in H. unfold cj in H. unfold im in H. firstorder.
    apply F2Eqn in H. unfold dj in H. unfold im in H. firstorder.
    
    apply F2Eqt1 in H as Ht1.
    apply F2Eqt2 in H as Ht2;subst.
    eexists. eexists;eauto.
  Qed.

  Lemma InvEncTermImAt : forall F t t' n,  (A1 n (encodeTerm F)) ⁺ = ((A1 n (FC2 im t t')) ⁻)° -> exists G G', F = PL.impl G G' /\ encodeFR G = Atom (A1 rg t) /\ encodeFR G' = Atom (A1 rg t').
    intros.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    eapply InvImTerm;eauto.
  Qed.
  
  Lemma InvIm: forall F t t' ,  encodeFR F = ((A1 rg (FC2 im t t')) ⁻)° -> exists G G', F = PL.impl G G' /\ encodeFR G = Atom (A1 rg t) /\ encodeFR G' = Atom (A1 rg t').
    intros.
    unfold encodeFR in H.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    apply InvImTerm;auto.

  Qed.

  Lemma InvFLIm : forall G G' t t', encodeFL (PL.impl G G') = ((A1 lf (FC2 im t t')) ⁻)° -> encodeFL G = Atom (A1 lf t) /\ encodeFL G' = Atom (A1 lf t').
    intros.
    unfold encodeFL in H.
    rewrite AtomNeg in H.
    LexpSubst.
    LexpSubst.
    simpl in H1.
    apply F2Eqt1 in H1 as Ht.
    apply F2Eqt2 in H1 as Ht'.
    unfold encodeFL.
    rewrite Ht. rewrite Ht'.
    split;auto.
  Qed.

  
End InversionTerm.

(* Injuctivity of encodeTerm *)
Lemma encodeTEq : forall t1 t2,  encodeTerm t1 = encodeTerm t2 -> t1 = t2.
  induction t1 ;destruct t2;intros;try(reflexivity); simpl in H;
    try(unfold cj in * );try(unfold dj in * );try(unfold im in * );
      try(match goal with
          |[H : Cte ?t = FC1 ?n ?t' |- _] => assert(Cte t <> FC1 n t') by (eapply Terms_cte_fc1;eauto);contradiction
          |[H : Cte ?t = FC2 ?n ?t' ?t'' |- _] => assert(Cte t <> FC2 n t' t'') by (eapply Terms_cte_fc2;eauto);contradiction
          |[H : FC1 ?n ?t' = Cte ?t  |- _] => symmetry in H ; assert(Cte t <> FC1 n t') by (eapply Terms_cte_fc1;eauto);contradiction
          |[H :  FC2 ?n ?t' ?t'' = Cte ?t |- _] => symmetry in H;assert(Cte t <> FC2 n t' t'') by (eapply Terms_cte_fc2;eauto);contradiction
          |[H :  FC1 ?n ?t = FC2 ?n' ?t' ?t'' |- _] => assert(FC1 n t  <> FC2 n' t' t'') by (eapply Terms_fc1_fc2;eauto);contradiction
          |[H :  FC2 ?n' ?t' ?t'' = FC1 ?n ?t |- _] => symmetry in H ;assert(FC1 n t  <> FC2 n' t' t'') by (eapply Terms_fc1_fc2;eauto);contradiction
          |[F : FC2 ?n ?t1 ?t2 = FC2 ?n' ?t1' ?t2' |- _] => assert(Hn : n = n' ) by  (apply F2Eqn in H; auto);firstorder;try(assert(Ht1 : (encodeTerm t1_1) = (encodeTerm t2_1)) by (eapply F2Eqt1;eauto);assert(Ht2 : (encodeTerm t1_2) = (encodeTerm t2_2)) by (eapply F2Eqt2;eauto);subst; apply IHt1_1 in Ht1;apply IHt1_2 in Ht2;subst;auto)
          end
         ).

  apply F1Eqt in H;apply CteEqt in H;auto.
Qed.

(* Injuctivity of encodeFL *)
Lemma encodeFLEq : forall F G,  encodeFL F = encodeFL G -> F = G.
  intros.
  destruct F;unfold encodeFL in *;LexpSubst;  apply A1InvT in H0;apply encodeTEq in H0;subst;auto.
Qed.


(* Encode Right only produces right atoms *)
Inductive RightAtom: Lexp -> Prop :=
| at_r : forall t, RightAtom ((Atom (A1 rg t))).
Hint Constructors RightAtom.

(* Encode Left only produces left atoms *)
Inductive LeftAtom : Lexp -> Prop :=
| at_l : forall t, LeftAtom ((Atom (A1 lf t))).
Hint Constructors LeftAtom.

(* Encode List only produces left atoms *)
Inductive LeftAtomL: list Lexp -> Prop :=
| lf_nil : LeftAtomL  nil
| lf_cons : forall L F, LeftAtom F -> LeftAtomL L -> LeftAtomL (F :: L) .
Hint Constructors LeftAtomL.

Lemma encodeRightRight : forall F, RightAtom (encodeFR F).
Proof with solveF.
  intros.
  destruct F;unfold encodeFR ...
Qed.

Lemma encodeLeftLeft : forall F, LeftAtom (encodeFL F).
Proof with solveF.
  intros.
  destruct F;unfold encodeFL ...
Qed.

Lemma encodeListLeft : forall L, LeftAtomL (encodeList L).
Proof with solveF.
  intros.
  induction L ...
  constructor ...
  apply encodeLeftLeft.
Qed.


Lemma EncodeFRLFContr : forall F t, encodeFR F <> ((A1 lf t) ⁻)°.
  intros F t HF.
  rewrite AtomNeg in HF.
  
  destruct F;compute in HF;
    match goal with [HF : ?F = ?G |- False ] =>
                    apply @equal_f_dep with (x:=unit) in HF;inversion HF
    end.
Qed.


Lemma EncodeFLRGContr : forall LA t, LeftAtom LA -> LA <> ((A1 rg t) ⁻)°.
  intros.
  inversion H.
  intro HF.
  rewrite AtomNeg in HF.
  apply @equal_f_dep with (x:=unit) in HF.
  inversion HF.
Qed.

Lemma EncodeFLRGContr' : forall F t, encodeFL F <> ((A1 rg t) ⁻)°.
  intros F t HF.
  
  generalize(encodeLeftLeft F); intro HLL.
  apply EncodeFLRGContr with (t:=t) in HLL.
  contradiction.
Qed.

Lemma EncodeLeftLLContr : forall t L, LeftAtomL L -> ~ In ((A1 rg t) ⁻)° L.
  intros.
  induction L;simpl;auto.
  inversion H;subst.
  apply IHL in H3.
  intro.
  destruct H0.
  generalize(EncodeFLRGContr  a t). intro.
  apply H1 in H2.
  contradiction.
  contradiction.
Qed.

(***********************)

Lemma EncSidesCorrect : forall F L M t ,
    encodeFR F :: encodeList L =mul= M  ++ [((A1 rg t) ⁻)°] ->
    encodeFR F = ((A1 rg t) ⁻)° /\ encodeList L =mul= M.
  intros.
  generalize(encodeRightRight F);intro HRF.
  generalize(encodeListLeft L);intro HLL.
  inversion HLL.
  (* it cannot be [] *)
  rewrite <- H1 in H.
  symmetry in H.
  rewrite union_comm in H.
  apply resolvers2 in H.
  destruct H.
  subst;split;auto.
  apply EncodeLeftLLContr with (t:=t) in HLL as HLL' .
  rewrite H0.
  apply notInMul; auto.
Qed.

Lemma EncSidesCorrect' : forall F L M t t', 
    encodeFR F :: encodeList L =mul= M ++ [((A1 lf t) ⁻)°] ++ [((A1 rg t') ⁻)°] ->
    encodeFR F = ((A1 rg t') ⁻)° /\ encodeList L =mul= M ++ [((A1 lf t) ⁻)°].
  intros.
  MReplaceIn (M ++ [((A1 lf t) ⁻)°] ++ [((A1 rg t') ⁻)°]) ( (M ++ [((A1 lf t) ⁻)°]) ++ [((A1 rg t') ⁻)°])  H.
  apply EncSidesCorrect in H.
  auto.
Qed.

(*************)


Lemma multisetEncode : forall L L' : list PL.LForm, PL.MSFormulas.meq L L' -> encodeList L =mul= encodeList L'.
Proof.
  intros L L' H.

  apply Permutation_meq.
  apply PL.MSFormulas.Permutation_meq in H.
  apply Permutation_map; auto.
Qed.

Lemma IsPBLEFT : ~ IsPositiveAtom BLEFT.
Proof with solveF.
  auto ...
Qed.

Lemma IsPINIT : ~ IsPositiveAtom INIT.
Proof with solveF.
  auto ...
Qed.

Lemma IsPCLEFT : ~ IsPositiveAtom CLEFT.
Proof with solveF.
  auto ...
Qed.

Lemma IsPCRIGHT : ~ IsPositiveAtom CRIGHT.
Proof with solveF.
  auto ...
Qed.

Lemma IsPDLEFT : ~ IsPositiveAtom DLEFT.
Proof with solveF.
  auto ...
Qed.

Lemma IsPDRIGHT1 : ~ IsPositiveAtom DRIGHT1.
Proof with solveF.
  auto ...
Qed.

Lemma IsPDRIGHT2 : ~ IsPositiveAtom DRIGHT2.
Proof with solveF.
  auto ...
Qed.


Lemma IsPILEFT : ~ IsPositiveAtom ILEFT.
Proof with solveF.
  auto ...
Qed.

Lemma IsPIRIGHT : ~ IsPositiveAtom IRIGHT.
Proof with solveF.
  auto ...
Qed.

Hint Resolve IsPINIT IsPCLEFT IsPCRIGHT IsPBLEFT IsPDLEFT IsPDRIGHT1 IsPDRIGHT2 IsPILEFT IsPIRIGHT.

Lemma TermFlattenG: forall (t:Term) (T:Type) ,   flattenT (t (term T)) =  (t T).
  intros.
  assert(ClosedT t) by apply ax_closedT.
  induction H; try(reflexivity).
  simpl. rewrite IHClosedT. auto.
  simpl. rewrite IHClosedT1. rewrite IHClosedT2. auto.
Qed.

Lemma TermFlatten: forall F (T:Type) ,   flattenT (encodeTerm F (term T)) =  (encodeTerm F T).
  intros.
  induction F;auto;
    simpl;
    rewrite IHF1;
    rewrite IHF2;
    auto.
Qed.

Lemma AtomFlatten : forall F G n m,   (fun T : Type => perp (a1 n (fc2 m (flattenT (encodeTerm F (term T))) (encodeTerm G T))))=
                                      Perp (A1 n (FC2 m (encodeTerm F) (encodeTerm G))).
  intros.
  
  extensionality T.
  
  rewrite TermFlatten.
  reflexivity.
Qed.

Lemma AtomFlatten' : forall F G n m,   (fun T : Type => atom (a1 n (fc2 m (flattenT (encodeTerm F (term T))) (encodeTerm G T))))=
                                       Atom (A1 n (FC2 m (encodeTerm F) (encodeTerm G))).
  intros.
  extensionality T.
  rewrite TermFlatten.
  reflexivity.
Qed.

Lemma AtomFlatten'' : forall F  n,   (fun T : Type => atom (a1 n (flattenT (encodeTerm F (term T)))))=
                                     Atom (A1 n (encodeTerm F)).
  intros.
  extensionality T.
  rewrite TermFlatten.
  reflexivity.
Qed. 

Lemma AtomFlatten2 : forall F n, (A1 n (encodeTerm F)) ⁺ = fun T : Type => atom (a1 n (flattenT (encodeTerm F (term T)))).
  intros.
  extensionality T.
  rewrite TermFlatten;auto.
Qed.

Lemma AtomFlatten3 : forall F n, (A1 n (encodeTerm F)) ⁺ = fun T : Type => atom (a1 n  (encodeTerm F T)).
  intros.
  extensionality T.
  reflexivity.
Qed.

Lemma FlattenEncTerm:  forall F G n m,  ( (A1 n (FC2 m (encodeTerm F) (encodeTerm G))) ⁺) =
                                        Dual_LExp (fun T : Type => perp (a1 n (fc2 m (flattenT (encodeTerm F (term T))) (encodeTerm G T)))).
  intros.
  rewrite AtomFlatten.
  reflexivity.
Qed.

Lemma Equiv1 : forall F, (A1 lf (encodeTerm F)) ⁺ = encodeFL F.
  intro;reflexivity.
Qed.
Lemma Equiv2 : forall F, (A1 rg (encodeTerm F)) ⁺ =  encodeFR F.
  intro;reflexivity.
Qed.

Ltac conv := 
  simpl;
  try (rewrite AtomFlatten);
  try (rewrite AtomFlatten');
  try (rewrite <- AtomFlatten3);
  try (rewrite AtomFlatten'');
  try(rewrite <- AtomFlatten2);
  try(rewrite Equiv1);
  try(rewrite Equiv2).

Theorem Soundness: forall L F n, L  |-P- n ; F -> ( encodeSequent L F ).
Proof with solveF.
  intros L F n HD.
  dependent induction n generalizing L F using strongind.
  
  + (* base case *)
    inversion HD;subst;unfold encodeSequent;simpl;autounfold;simpl.
    (* case init *)
    apply multisetEncode in H. simpl in H.  
    rewrite H. autounfold. simpl.
    eapply tri_dec2 with (F:= INIT);eauto.
    eapply tri_ex with (t:= (Cte (PL.atom a))).
    eapply tri_tensor with (N:= [A1 rg (FC1 pr (Cte (PL.atom a))) ⁺ ; (A1 lf (FC1 pr (Cte (PL.atom a)))) ⁺])
                             (M:= encodeList L');eauto.
    eapply tri_tensor with (N:=[(A1 rg (FC1 pr (Cte (PL.atom a)))) ⁺])
                             (M:= [(A1 lf (FC1 pr (Cte (PL.atom a)))) ⁺]) ...
    apply Init1 ...
    apply Init1 ...
    apply tri_rel...
    (* case bottom *)
    apply multisetEncode in H. simpl in H.
    rewrite H. autounfold. simpl.
    eapply tri_dec2 with (F:= BLEFT);eauto.
    eapply tri_tensor with (N:= [(A1 lf (Cte PL.bot)) ⁺] ) (M:=  (A1 rg (encodeTerm F)) ⁺ :: encodeList L') ...
     
    apply Init1 ...
  + (* Inductive Cases *)
    inversion HD;subst;autounfold in *;simpl;autounfold;simpl.
    ++ (* Conj R *)
      eapply tri_dec2 with (F:= CRIGHT);eauto.
      eapply tri_ex with (t:= encodeTerm F0).
      eapply tri_ex with (t:= encodeTerm G).
      eapply tri_tensor with (N:= [(A1 rg (FC2 cj (encodeTerm F0)  (encodeTerm G))) ⁺])
                               (M:= encodeList L);eauto;conv ... 
      apply tri_rel ...
      apply tri_with; apply tri_store ...
      (* Branch F *)
      rewrite union_comm.
      apply H in H1;conv ...
      (* Branch G *)
      rewrite union_comm.
      apply H in H3;conv ...
      
    ++ (* case Conj L *)
      apply H in H3 ...
      Check  multisetEncode.
      simpl in H1 .
      specialize H1 with (PL.conj G G') .  compute in H1
      generalize(
      apply multeq_meq in H1.
      eapply multisetEncode in H1.
      
      (*apply multisetEncode in H1.
      rewrite H1.  *)
      eapply tri_dec2 with 
          (B':= [BLEFT; INIT; CRIGHT; DRIGHT1; DRIGHT2; DLEFT; IRIGHT; ILEFT]) (F:= CLEFT)...
      eapply tri_ex with (t:= encodeTerm G). 
      eapply tri_ex with (t:= encodeTerm G') ...
      eapply tri_tensor with (N:= [encodeFL (PL.conj G G')])
                               (M:=  (A1 rg (encodeTerm F)) ⁺ :: encodeList (L'));conv ...

      apply Init1 ...
      apply tri_rel ...
      apply tri_par ...
      apply tri_store ... 
      apply tri_store;conv ... 
      MReplace (encodeFR F :: (encodeList L' ++ [encodeFL G]) ++ [encodeFL G']) (encodeFR F :: encodeFL G :: encodeFL G' :: encodeList L') ...
    ++  (* disjunction R1 *)
      apply H in H2 ...
      eapply tri_dec2 with 
      (B':=[BLEFT; INIT; CRIGHT; CLEFT; DRIGHT2; DLEFT; IRIGHT; ILEFT]) (F:= DRIGHT1)...
      try solve_permutation.
      eapply tri_ex with (t:= encodeTerm F0). 
      eapply tri_ex with (t:= encodeTerm G) ...
      eapply tri_tensor with (N:= [encodeFR (PL.disj F0 G)])
                               (M:=  encodeList L);eauto ...
      
      unfold encodeFR;simpl;conv ...
      apply tri_rel ...
      apply tri_store ...
      rewrite union_comm;conv ...
    ++ (* disjunction R2 *)
      apply H in H2 ...
      eapply tri_dec2 with 
      (B':=[BLEFT; INIT; CRIGHT; CLEFT; DRIGHT1; DLEFT; IRIGHT; ILEFT]) (F:= DRIGHT2)...
      eapply tri_ex with (t:= encodeTerm F0). 
      eapply tri_ex with (t:= encodeTerm G) ...
      eapply tri_tensor with (N:= [encodeFR (PL.disj F0 G)])
                               (M:=  encodeList L);eauto;conv ...

      unfold encodeFR;simpl ...

      apply tri_rel ...
      apply tri_store ...
      rewrite union_comm ...
    ++  (* disjunction LEFT *)
      apply multisetEncode in H2.
      rewrite H2. 
      apply H in H3 ...
      apply H in H5 ...
      eapply tri_dec2 with 
      (B':=[BLEFT; INIT; CRIGHT; CLEFT; DRIGHT1; DRIGHT2; IRIGHT; ILEFT]) (F:= DLEFT)...
      eapply tri_ex with (t:= encodeTerm F0).   
      eapply tri_ex with (t:= encodeTerm G) ...
      eapply tri_tensor with (N:= [encodeFL (PL.disj F0 G)])
                               (M:=  encodeFR F :: encodeList L');eauto;conv...
      unfold encodeFL ...

      apply tri_rel ...
      apply tri_with;apply tri_store;unfold encodeSequent in *;simpl in *;conv ...
      (* Branch F0 *)
      MReplace ( encodeFR F :: encodeList L' ++ [encodeFL F0]) (encodeFR F :: encodeFL F0 :: encodeList L') ...
      (* Branch G *)
      MReplace ( encodeFR F :: encodeList L' ++ [encodeFL G]) (encodeFR F :: encodeFL G :: encodeList L') ...

    ++ (* Implication Right *)
      apply H in H2 ...
      eapply tri_dec2 with 
      (B':=[BLEFT; INIT; CRIGHT; CLEFT; DRIGHT1; DRIGHT2; DLEFT; ILEFT]) (F:= IRIGHT)...
      try solve_permutation.
      eapply tri_ex with (t:= encodeTerm F0). 
      eapply tri_ex with (t:= encodeTerm G) ...
      eapply tri_tensor with (N:= [encodeFR (PL.impl F0 G)])
                               (M:=  encodeList L);eauto;conv ...

      unfold encodeFR;simpl ...

      apply tri_rel ...
      apply tri_par ...
      apply tri_store ...
      apply tri_store;conv ...
      
      MReplace ((encodeList L ++ [encodeFL F0]) ++ [encodeFR G]) (encodeFR G :: encodeFL F0 :: encodeList L) ...
    ++ (* Implication Left *)
      assert(HLL' : PL.meqPL L (PL.impl F0 G :: L')) by 
          solve [apply PL.MSFormulas.multeq_meq; auto].
      assert(H3' : PL.impl F0 G :: L' |-P- n0; F0) by
          solve [eapply PL.Exch;eauto]. clear H3.
      apply multisetEncode in HLL'.

      apply H in H3' ...
      apply H in H5 ...
      eapply tri_dec2 with 
      (B':=[BLEFT; INIT; CRIGHT; CLEFT; DRIGHT1; DRIGHT2; DLEFT; IRIGHT]) (F:= ILEFT)...
      eapply tri_ex with (t:= encodeTerm F0). 
      eapply tri_ex with (t:= encodeTerm G) ... 
      eapply tri_ex with (t:= encodeTerm F) ...
      rewrite HLL'. conv.
      eapply tri_tensor with (N:= [encodeFL (PL.impl F0 G) ; encodeFR F])
                               (M:=  encodeList L') ...

      (* First Tensor *)
      assert(HS:  (fun T : Type =>
                     tensor
                       (perp
                          (a1 lf
                              (fc2 im
                                   (flattenT (flattenT (encodeTerm F0 (term (term T)))))
                                   (flattenT (encodeTerm G (term T))))))
                       (perp (a1 rg (encodeTerm F T)))) =
                  Tensor (Perp (A1 lf (FC2 im (encodeTerm F0) (encodeTerm G))))
                         (Perp (A1 rg (encodeTerm F)))).
      extensionality T.
      do 3 rewrite TermFlatten.
      reflexivity.
      rewrite HS. clear HS.
      eapply tri_tensor with (N:= [encodeFL (PL.impl F0 G)])
                               (M:=  [encodeFR F]) ...
      unfold encodeFL ...
      unfold encodeFR ...
      (* With *)
      eapply tri_rel ...
      eapply tri_with ...
      (* first branch with *)
      eapply tri_par ...
      assert(HS: (fun T : Type =>
                    atom (a1 rg (flattenT (flattenT (encodeTerm F0 (term (term T)))))))=
                 Atom (A1 rg (encodeTerm F0))).
      extensionality T.
      do 2 rewrite TermFlatten;auto.
      rewrite HS;clear HS.
      eapply tri_store ...
      assert(HS: (fun T : Type =>
                    atom
                      (a1 lf
                          (fc2 im (flattenT (flattenT (encodeTerm F0 (term (term T)))))
                               (flattenT (encodeTerm G (term T)))))) =
                 Atom (A1 lf (FC2 im (encodeTerm F0) (encodeTerm G)))).
      extensionality T.
      do 3 rewrite TermFlatten;auto.
      rewrite HS;clear HS.
      eapply tri_store ...
      unfold encodeFR in H3'. simpl in H3'.
      assert(HS: (encodeList L' ++ [(A1 rg (encodeTerm F0)) ⁺]) ++
                                                                [(A1 lf (FC2 im (encodeTerm F0) (encodeTerm G))) ⁺] =mul= (A1 rg (encodeTerm F0)) ⁺
                                                                                                                                                  :: encodeFL (PL.impl F0 G) :: encodeList L').
      solve_permutation.
      rewrite HS;clear HS ...
      (* Second branch with *)
      eapply tri_par ...
      eapply tri_store...
      eapply tri_store...
      assert(HS: (fun T : Type => atom (a1 lf (flattenT (encodeTerm G (term T))))) =
                 Atom (A1 lf (encodeTerm G))).
      extensionality T.
      rewrite TermFlatten;auto.
      rewrite HS;clear HS.
      change (fun T : Type => atom (a1 rg (encodeTerm F T))) with (Atom (A1 rg (encodeTerm F))).
      simpl in H5.
      unfold encodeFL in H5.
      unfold encodeFR in H5.
      MReplace ( (encodeList L' ++ [(A1 lf (encodeTerm G)) ⁺]) ++
                                                               [(A1 rg (encodeTerm F)) ⁺]) (  (A1 rg (encodeTerm F)) ⁺
                                                                                                                     :: (A1 lf (encodeTerm G)) ⁺ :: encodeList L').
      assumption.
Qed.

(***********************)

(************************)



Lemma AtomsTheoryFalse : forall A B, Theory =mul= Atom A :: B -> False.
Proof with InvTac. 
  intros.
  unfold Theory in H.
  multisetContr... 
Qed.

Lemma AtomsTheoryFalse' : forall A B, Theory =mul= Perp A :: B -> False.
Proof with InvTac. 
  intros.
  unfold Theory in H.
  multisetContr... 
Qed.

Lemma InvI1 : forall n t M,  true = isPositive n -> |-F- Theory; M; DW ((A1 n t) ⁻) ->
                                                                    M = [Dual_LExp ( (A1 n t) ⁻)].
Proof with InvTac.
  intros n t M HPos HD1.
  inversion HD1;subst ...
  (* cannot be in B *)
  apply AtomsTheoryFalse in H3.
  contradiction.
  inversion H0;subst ...  
  (* cannot be a release .. then H2 is inconsistent*)
Qed.

Lemma LeftRightAtom :  forall F t, encodeFR F = (A1 rg t) ⁺ -> encodeFL F = (A1 lf t) ⁺.
  intros.
  destruct F; unfold encodeFR in H; LexpSubst;unfold encodeFL;
    apply A1InvT in H0;rewrite H0;reflexivity.
Qed.

Lemma RightLeftAtom :  forall F t, encodeFL F = (A1 lf t) ⁺ -> encodeFR F = (A1 rg t) ⁺.
  intros.
  destruct F; unfold encodeFL in H ; LexpSubst;unfold encodeFR;
    apply A1InvT in H0;rewrite H0;reflexivity.
Qed.

Lemma encodeListIN : forall L F M, encodeList L =mul= [encodeFL F] ++ M -> In F L.
Proof with InvTac.
  induction L; simpl in *;intros ...
  apply DestructMSet in H.
  destruct H.
  (* case 1 *)
  destruct H.
  apply encodeFLEq in H;auto.
  (* case 2 *)
  destruct H as [M' HM].
  destruct HM.
  right.
  apply IHL with (M:= M');auto.
Qed.

Lemma NotEqFRFL : forall F G, encodeFR G <> encodeFL F.
  intros F G Hn.
  rewrite <- Equiv2 in Hn.
  rewrite <- Equiv1 in Hn.
  LexpSubst.
  apply A1InvN in H.
  unfold rg in H.
  unfold lf in H.
  firstorder.
Qed.

Lemma EncodeListMembers: forall F L,  In (encodeFL F) (encodeList L) -> In F L.
  induction L;intro.
  (* case [] *)
  inversion H.
  (* case Ind *)
  inversion H.
  apply encodeFLEq in H0;subst;auto.
  apply IHL in H0.
  simpl.
  right;auto.
Qed.

Lemma EncodeListMembers' : forall L L' t,  encodeList L =mul= ((A1 lf t) ⁻)° :: L' -> exists F, encodeFL F = ((A1 lf t) ⁻)° /\ In F L.
  induction L;intros.
  simpl in H.
  contradiction_multiset. (*!! H is inconsistent *)
  simpl in H.
  apply DestructMSet in H. (*!! Multiset reasoning  on H*)
  do 2 destruct H.
  exists a.
  split; auto.
  destruct H as [L'' H0].
  apply IHL in H0.
  destruct H0 as[F [H0 H0']].
  eexists.
  split;eauto.
Qed.

Lemma encodeListFRIN : forall F G L M, encodeFR G :: encodeList L =mul= M ++ [encodeFL F] -> In F L.
  intros.
  generalize( NotEqFRFL F G); intro HFG.
  rewrite union_comm in H; simpl in H.
  apply multFalse in H.
  inversion H; [contradiction|]. (*!! from HFG and H *)
  apply EncodeListMembers;auto.
Qed.

(********************)
Lemma encodeFL_aux L G L1:
  encodeList L =mul= G :: L1 -> exists a, G = encodeFL a.
Proof.
  intro H.  
  assert (Hin: In G (encodeList L)) by
      solve [apply In_to_in; rewrite H; auto].
  change (encodeList L) with (map encodeFL L) in Hin.
  eapply in_map_iff in Hin.
  destruct Hin as [x  Hx].
  eexists x. firstorder.
Qed.

Lemma encodeFL_aux' a L G L1:
  encodeList L =mul= G :: L1 -> G = encodeFL a -> exists L', PL.meqPL L (a :: L').
Proof.
  intros Hm Hg.  
  rewrite Hg in Hm.
  assert (Hin: In a L) by
      solve [eapply encodeListIN with (M:=L1); auto].
  apply PL.MSFormulas.In_to_in in Hin.
  apply PL.MSFormulas.member_then_meq in Hin.
  eauto.
Qed.

(*!! UP *)
Lemma DestructMSet4 F G M L:
  encodeFR F :: encodeList L =mul= G :: M -> 
  encodeFR F <> G -> exists  L' a, PL.meqPL L (a::L') /\ encodeFL a = G
                                   /\ M =mul= (encodeFR F) :: encodeList L'.
Proof.
  change (encodeFR F :: encodeList L =mul= G :: M) with ([encodeFR F] ++ encodeList L =mul= [G] ++ M).
  intros Hm Hd.
  simpl_union_context; [contradiction|].
  assert (exists a, G = encodeFL a) by
      solve [eapply encodeFL_aux; eauto].
  destruct H1.
  assert (exists L', PL.meqPL L (x :: L')) by
      solve [eapply encodeFL_aux'; eauto].
  destruct H2.
  eexists x0. 
  eexists x.
  split; [auto | split;auto].
  rewrite H.
  apply meq_skip.
  apply multisetEncode in H2.
  rewrite H0 in H2.
  simpl in H2.
  rewrite <- H1 in H2.
  apply insert_meq in H2; auto.
Qed.
(********************)

Lemma encodeInvConj : forall F L M t t', encodeFR F :: encodeList L =mul= M ++ [((A1 lf (FC2 cj t t')) ⁻)°] -> exists L' G G', PL.meqPL L ((PL.conj G G') :: L') /\  (M =mul= (encodeFR F) :: encodeList L') /\ encodeFL (PL.conj G G') = ((A1 lf (FC2 cj t t')) ⁻)°.
  intros.
  generalize(EncodeFRLFContr F (FC2 cj t t'));intro H'.
  rewrite union_comm in H.
  simpl in H.
  assert(exists  L' a, PL.meqPL L (a::L') /\ encodeFL a =((A1 lf (FC2 cj t t')) ⁻)°
                       /\ M =mul= (encodeFR F) :: encodeList L').
  apply DestructMSet4; auto.                     
  (*!! Multsets: from H' and H *)
  destruct H0 as [L' H0].
  destruct H0 as [a HM].
  destruct HM as [HM [HM' HM'']].
  rewrite HM'' in H.
  unfold encodeFL in HM'.
  apply InvEncTermCjAt in HM' as HS.
  destruct HS as [G HS]. 
  destruct HS as [G' HS];subst.
  do 3 eexists;split.
  eassumption.
  rewrite HM''.
  split;auto.
Qed.

Lemma encodeInvDisj : forall F L M t t', encodeFR F :: encodeList L =mul= M ++ [((A1 lf (FC2 dj t t')) ⁻)°] -> exists L' G G', PL.meqPL L ((PL.disj G G') :: L') /\  (M =mul= (encodeFR F) :: encodeList L') /\ encodeFL (PL.disj G G') = ((A1 lf (FC2 dj t t')) ⁻)°.
  intros.
  generalize(EncodeFRLFContr F (FC2 dj t t'));intro H'.
  rewrite union_comm in H.
  simpl in H.
  assert(exists  L' a, PL.meqPL L (a::L') /\ encodeFL a =((A1 lf (FC2 dj t t')) ⁻)°
                       /\ M =mul= (encodeFR F) :: encodeList L').
  
  apply DestructMSet4; auto.
  (*!! Multsets: from H' and H *)
  destruct H0 as [L' H0].
  destruct H0 as [a HM].
  destruct HM as [HM [HM' HM'']].
  rewrite HM'' in H.
  unfold encodeFL in HM'.
  apply  InvEncTermDjAt in HM' as HS.
  destruct HS as [G HS]. 
  destruct HS as [G' HS];subst.
  destruct HS as [HS HS'].
  destruct HS';subst.
  do 3 eexists;split.
  eassumption.
  rewrite HM''.
  split;auto.
Qed.


Lemma encodeInvImpl : forall F L M t1 t2 t3, encodeFR F :: encodeList L =mul= M ++ [((A1 rg t1) ⁻)°] ++ [((A1 lf (FC2 im t2 t3)) ⁻)°] -> exists L' G G', PL.meqPL L ((PL.impl G G') :: L') /\  (M ++ [((A1 rg t1) ⁻)°] =mul= (encodeFR F) :: encodeList L') /\ encodeFR F = ((A1 rg t1) ⁻)° /\ encodeFL (PL.impl G G') = ((A1 lf (FC2 im t2 t3)) ⁻)°.
  intros.
  generalize(EncodeFRLFContr F (FC2 im t2 t3));intro H'.

  assert(exists  L' a, PL.meqPL L (a::L') /\ encodeFL a =((A1 lf (FC2 im t2 t3)) ⁻)°
                       /\ M ++ [((A1 rg t1) ⁻)°] =mul= (encodeFR F) :: encodeList L').
  (*!! Multsets: from H' and H *)
  apply DestructMSet4; auto. rewrite H. solve_permutation.
  destruct H0 as [L' H0].
  destruct H0 as [a HM].
  destruct HM as [HM [HM' HM'']].
  
  symmetry in HM''.
  apply EncSidesCorrect in HM'' as HM'''.
  destruct HM''';subst.
  rewrite <- H1 in H.
  unfold encodeFL in HM'.
  apply  InvEncTermImAt in HM' as HS.
  destruct HS as [G HS]. 
  destruct HS as [G' HS];subst.
  destruct HS as [HS HS'].
  destruct HS';subst.
  do 3 eexists;split.
  eassumption.
  split;auto.
Qed.



Lemma InvINIT : forall L F, |-F- Theory ;(encodeFR F) :: encodeList L ; DW(INIT) -> exists L' a, PL.meqPL L (F:: L') /\ F = PL.atom a.
Proof with InvTac.
  intros.
  inversion H;subst ... 
  (* first the exists *)
  (*unfold INIT in H0. *)
  (*LexpSubst.*) (*clear H0.*)
  unfold Subst in H3; simpl in H3.
  (* now the tensor *)
  inversion H3;subst ...
  change (fun T : Type => tensor (tensor (perp (a1 rg (fc1 pr (t T)))) (perp (a1 lf (fc1 pr (t T))))) top)
  with (Tensor (Tensor (Perp (A1 rg (FC1 pr t))) (Perp (A1 lf (FC1 pr t)))) Top) in H0.
  LexpSubst.
  (* Now the tensor in H2 *)
  inversion H2;subst ...
  (* H5 and H9 must finish *)
  apply InvI1 in H5 ...
  apply InvI1 in H9 ...
  subst.
  rewrite H4 in H1.
  apply EncSidesCorrect' in H1.
  destruct H1 as [HF HL].
  rewrite AtomNeg in *.
  generalize (LeftRightAtom F (FC1 pr t) );intro HLRA.
  apply HLRA in HF.
  rewrite <- HF in HL.
  rewrite union_comm in HL.
  apply encodeListIN in HL.
  rewrite <- AtomNeg in HF.
  apply InvEncTermAtAt in HF.
  destruct HF as [a HF];subst.
  apply PL.MSFormulas.In_to_in in HL.
  apply PL.MSFormulas.member_then_meq in HL.
  destruct HL.
  eexists;eexists. split;eauto.
Qed.



(* Inversion of Bottom Left *)
Lemma InvBLEFT :forall F L,  |-F- Theory; encodeFR (F) :: encodeList L; DW BLEFT -> exists L', PL.meqPL L (PL.bot:: L').
Proof with InvTac.
  intros.
  inversion H ...
  unfold BLEFT in H0.
  change ((fun T : Type => tensor (perp (a1 lf (cte PL.bot))) top)) with
  (Tensor (Perp (A1 lf (Cte PL.bot)) ) Top) in H0.
  LexpSubst.
  apply InvI1 in H2;subst ...
  change (((A1 lf (Cte PL.bot)) ⁻)°) with (encodeFL PL.bot) in H1.
  apply encodeListFRIN in H1.
  apply PL.MSFormulas.In_to_in in H1.
  apply PL.MSFormulas.member_then_meq in H1.
  destruct H1.
  eexists; eauto.
Qed.

Lemma InvCRIGHT :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW CRIGHT -> exists G1 G2 n1 n2, n = S ( S (S (S (S (S (max n1 n2))))))  /\ F = PL.conj G1 G2 /\ S ( S (S (S (S (S (max n1 n2)))))) |-F- Theory; encodeFR (PL.conj G1 G2) :: encodeList L; DW CRIGHT /\ n1 |-F- Theory; encodeFR G1 :: encodeList L ; UP [] /\ n2 |-F- Theory; encodeFR G2 :: encodeList L ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold CRIGHT in H0. LexpSubst. clear H0.
  inversion H4;subst ...
  unfold Subst in H0. simpl in H0. 

  change ((fun T : Type => ex (fun x : T => tensor (perp (a1 rg (fc2 cj (t T) (var x)))) (witH (atom (a1 rg (t T))) (atom (a1 rg (var x)))))))
  with (E{ fun T x => tensor (perp (a1 rg (fc2 cj (t T) (var x)))) (witH (atom (a1 rg (t T))) (atom (a1 rg (var x)))) }) in H0.
  LexpSubst. clear H0.
  unfold Subst in H5. simpl in H5.
  inversion H5;subst ...
  
  assert (HS : (fun T : Type =>
                  tensor (perp (a1 rg (fc2 cj (flattenT (t (term T))) (t0 T))))
                         (witH (atom (a1 rg (flattenT (t (term T))))) (atom (a1 rg (t0 T))))) = 
               Tensor (Perp (A1 rg (FC2 cj t t0)))
                      (With (Atom (A1 rg t))  (Atom (A1 rg t0)))).
  extensionality T;simpl.
  rewrite TermFlattenG. auto.
  rewrite HS in H0. clear HS.
  LexpSubst.
  inversion H2;subst ...
  inversion H8;subst ...
  inversion H11;subst ...
  inversion H13;subst ...
  inversion H14;subst ...
  simpl in H.
  apply EncSidesCorrect in H1 as H1'.
  destruct H1' as [HFG HML].
  
  unfold encodeFR in HFG. simpl in HFG.
  apply  InvEncTermCjAt in HFG as HFG'.

  destruct HFG' as [G1 HFG'].
  destruct HFG' as [G2 HFG']. subst.
  rewrite AtomNeg in HFG.
  
  LexpSubst.
  LexpSubst. simpl in H6.
  apply F2Eqt1 in H6 as H6'.
  apply F2Eqt2 in H6 as H6'';subst.

  rewrite <- HML in H16. rewrite union_comm in H16. simpl in H16.
  rewrite <- HML in H18. rewrite union_comm in H18. simpl in H18.
  do 4 eexists.
  split;eauto.
  apply AtomsTheoryFalse in H10.
  contradiction.
  
  (* H3 is inconsisten *)
  inversion H3 ...
  simpl in H6. intuition.
Qed.




Lemma InvCLEFT :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW CLEFT -> exists L' G1 G2 n1, n = S ( S (S (S (S ( S (S n1))))))  /\ PL.meqPL L  ((PL.conj G1 G2) :: L') /\ n1 |-F- Theory; encodeFR F :: encodeFL G1 :: encodeFL G2 :: encodeList L' ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold CLEFT in H0.
  
  change ((fun T : Type => ex
                             (fun x : T => ex (fun y : T => tensor (perp (a1 lf (fc2 cj (var x) (var y))))
                                                                   (par (atom (a1 lf (var x))) (atom (a1 lf (var y))))))))
  with
  (E{ fun _ x => ex (fun y => tensor (perp (a1 lf (fc2 cj (var x) (var y)))) (par (atom (a1 lf (var x))) (atom (a1 lf (var y)))) ) }) in H0.
  LexpSubst. clear H0.
  unfold Subst in H4;simpl in H4.
  inversion H4 ...
  change (fun T : Type =>
            ex
              (fun x : T =>
                 tensor (perp (a1 lf (fc2 cj (t T) (var x))))
                        (par (atom (a1 lf (t T))) (atom (a1 lf (var x))))))
  with
  (E{ fun T x => tensor (perp (a1 lf (fc2 cj (t T) (var x))))
                        (par (atom (a1 lf (t T))) (atom (a1 lf (var x))))}) in H0.
  LexpSubst. clear H0.
  unfold Subst in H5;simpl in H5.
  assert (HS : (fun T : Type =>
                  tensor (perp (a1 lf (fc2 cj (flattenT (t (term T))) (t0 T))))
                         (par (atom (a1 lf (flattenT (t (term T))))) (atom (a1 lf (t0 T)))))
               = Tensor (Perp (A1 lf (FC2 cj t t0))) (Par (Atom (A1 lf t)) (Atom (A1 lf t0)))).
  extensionality T;simpl.
  rewrite TermFlattenG. auto.
  rewrite HS in H5. clear HS.
  inversion H5 ...
  (* H8 *)
  inversion H8;subst ...
  inversion H10...
  inversion H11;subst ...
  inversion H14;subst ...

  (* H2 *)
  clear H4 H5 H10 H11 H13 H15 H3 H14.
  inversion H2;subst ...
  apply encodeInvConj in H1.
  destruct H1 as [L' H1].
  destruct H1 as [G H1].
  destruct H1 as [G' H1].
  destruct H1 as [H1  H1'].
  destruct H1' as [H1'  H1''].
  rewrite H1' in H16.
  apply InvFLCj in H1''.
  destruct H1'' as [HGt HGt'].
  rewrite <- HGt  in H16.
  rewrite <- HGt'  in H16.
  eexists L'. exists G. exists G'. eexists. 
  split;auto.
  split;auto.
  assert(HM: ((encodeFR F :: encodeList L') ++ [encodeFL G]) ++ [encodeFL G'] =mul=
             encodeFR F :: encodeFL G :: encodeFL G' :: encodeList L') ...

  rewrite HM in H16;clear HM.
  assumption.
  
  (* cannot be from B *)
  apply AtomsTheoryFalse in H7. contradiction.
  (* cannot be a release *)
  inversion H3;subst.
  unfold lf in H7. simpl in H7. intuition.
Qed.


Lemma InvILEFT :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW ILEFT -> exists L' G1 G2 n1 n2, n =  S (S (S (S ( S (S ( (S (S (S (max n1 n2))))))))))  /\ PL.meqPL L  ((PL.impl G1 G2) :: L') /\ n1 |-F- Theory; encodeFR G1 :: encodeList L ; UP [] /\ n2 |-F- Theory; encodeFR F :: encodeFL G2 :: encodeList L' ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold ILEFT in H0.
  LexpSubst;clear H0.
  unfold Subst in H4;simpl in H4.
  inversion H4 ...
  change (fun T : Type =>
            ex (fun x : T =>
                  ex
                    (fun x0 : T =>
                       tensor
                         (tensor (perp (a1 lf (fc2 im (t T) (var x)))) (perp (a1 rg (var x0))))
                         (witH
                            (par (atom (a1 rg (t T))) (atom (a1 lf (fc2 im (t T) (var x)))))
                            (par (atom (a1 lf (var x))) (atom (a1 rg (var x0))))))))
  with
  (E{ fun T x => ex
                   (fun x0 : T =>
                      tensor
                        (tensor (perp (a1 lf (fc2 im (t T) (var x)))) (perp (a1 rg (var x0))))
                        (witH
                           (par (atom (a1 rg (t T))) (atom (a1 lf (fc2 im (t T) (var x)))))
                           (par (atom (a1 lf (var x))) (atom (a1 rg (var x0)))))) }) in H0 .
  LexpSubst. clear H4 H0.
  unfold Subst in H5;simpl in H5.
  inversion H5 ...
  change(fun T : Type =>
           ex
             (fun x : T =>
                tensor
                  (tensor
                     (perp (a1 lf (fc2 im (flattenT (t (term T))) (t0 T)))) (perp (a1 rg (var x))))
                  (witH
                     (par (atom (a1 rg (flattenT (t (term T))))) (atom (a1 lf (fc2 im (flattenT (t (term T))) (t0 T)))))
                     (par (atom (a1 lf (t0 T))) (atom (a1 rg (var x)))))))
  with
  (E{ fun T x => tensor
                   (tensor
                      (perp (a1 lf (fc2 im (flattenT (t (term T))) (t0 T)))) (perp (a1 rg (var x))))
                   (witH
                      (par (atom (a1 rg (flattenT (t (term T))))) (atom (a1 lf (fc2 im (flattenT (t (term T))) (t0 T)))))
                      (par (atom (a1 lf (t0 T))) (atom (a1 rg (var x))))) } ) in H0.
  LexpSubst. clear H0.
  unfold Subst in H4;simpl in H4. clear H5.
  inversion H4 ...
  assert(HS :  (fun T : Type =>
                  tensor
                    (tensor
                       (perp
                          (a1 lf
                              (fc2 im (flattenT (flattenT (t (term (term T))))) (flattenT (t0 (term T)))))) 
                       (perp (a1 rg (t1 T))))
                    (witH
                       (par
                          (atom (a1 rg (flattenT (flattenT (t (term (term T)))))))
                          (atom
                             (a1 lf
                                 (fc2 im (flattenT (flattenT (t (term (term T))))) (flattenT (t0 (term T)))))))
                       (par (atom (a1 lf (flattenT (t0 (term T)))))
                            (atom (a1 rg (t1 T)))))) =
               Tensor (Tensor (Perp (A1 lf (FC2 im t t0))) (Perp (A1 rg t1))) (With (Par (Atom (A1 rg t)) (Atom (A1 lf (FC2 im t t0)))) (Par (Atom (A1 lf t0)) (Atom (A1 rg t1)))) ).
  extensionality T.
  do 3 rewrite TermFlattenG.
  reflexivity. rewrite HS in H0;clear HS.
  LexpSubst. clear H4.
  
  (* Inversion of H7 *)
  inversion H7;subst ... clear H7. (* release *)
  inversion H8;subst ... clear H8. (* with *)
  inversion H9;subst ... clear H9.
  inversion H7;subst ... clear H7.
  inversion H11;subst ... clear H3  H8 H9 H11. (* conslusion in H12 *)
  inversion H10;subst ... clear H10. (* with *)
  inversion H6;subst ... clear H6. (* store *)
  inversion H9;subst ... clear H9. (* conslusion in H10 *)
  clear H7 H8.
  (* Inversion of H2 *)
  inversion H2;subst ... (* tensor *)
  (* First Tensor in H4 *)
  inversion H4;subst ...
  (* Second Parte in H8 *)
  inversion H8;subst ...

  (*****************)
  clear H9 H11 H2 H4 H8.
  rewrite H3 in H1. clear H3.
  apply encodeInvImpl in H1.
  destruct H1 as [L' H1].
  destruct H1 as [G H1].
  destruct H1 as [G' H1].
  destruct H1 as [H1  H1'].
  destruct H1' as [H1'  H1''].
  destruct H1'';subst.
  assert(HS :(M ++ [(A1 lf t0) ⁺]) ++ [(A1 rg t1) ⁺]  =mul=
             (((M ++ [(A1 rg t1) ⁺]) ++ [(A1 lf t0) ⁺])  )) ...
  rewrite HS in H10;clear HS.
  rewrite H1' in H10.
  eexists L'. exists G. exists G'. exists n0. exists n1.
  split;auto.
  split;auto.
  split;auto.
  clear H10.
  assert(HS: encodeList L =mul= encodeList (PL.impl G G' :: L'))
    by (apply multisetEncode;auto).
  rewrite HS;clear HS.
  simpl.
  rewrite H2.
  symmetry in H1'.
  apply EncSidesCorrect in H1'.
  destruct H1';subst.
  rewrite <- H4 in H12.
  apply InvFLIm in H2.
  destruct H2;subst.
  apply RightLeftAtom in H2.
  rewrite H2.
  assert(HS:  (A1 rg t) ⁺ :: ((A1 lf (FC2 im t t0)) ⁻)° :: encodeList L'
              =mul= (encodeList L' ++ [(A1 rg t) ⁺]) ++ [(A1 lf (FC2 im t t0)) ⁺]) ...
  rewrite HS;clear HS.
  assumption.
  apply InvFLIm in H2.
  destruct H2;subst.
  rewrite H3.
  MReplace(encodeFR F :: (A1 lf t0) ⁺ :: encodeList L') ((encodeFR F :: encodeList L') ++ [(A1 lf t0) ⁺]).
  assumption.
  (*****************)
  
  (* cannot be from B *)
  apply AtomsTheoryFalse in H13. contradiction.
  (* cannot be a release *)
  inversion H5;subst.
  unfold lf in H6. simpl in H6. intuition.
  
  (* cannot be from B *)
  apply AtomsTheoryFalse in H11. contradiction.
  (* cannot be a release *)
  inversion H5;subst.
  unfold lf in H6. simpl in H6. intuition.
Qed.


Lemma InvDLEFT :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW DLEFT -> exists L' G1 G2 n1 n2, n =  S (S (S (S ( S (S (max n1 n2))))))  /\ PL.meqPL L  ((PL.disj G1 G2) :: L') /\ n1 |-F- Theory; encodeFR F :: encodeFL G1 :: encodeList L' ; UP [] /\ n2 |-F- Theory; encodeFR F :: encodeFL G2 :: encodeList L' ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold DLEFT in H0.
  LexpSubst;clear H0.
  unfold Subst in H4;simpl in H4.
  inversion H4 ...
  change (fun T : Type =>
            ex
              (fun x : T =>
                 tensor (perp (a1 lf (fc2 dj (t T) (var x))))
                        (witH (atom (a1 lf (t T))) (atom (a1 lf (var x))))))
  with
  (E{ fun T x => 
        tensor (perp (a1 lf (fc2 dj (t T) (var x))))
               (witH (atom (a1 lf (t T))) (atom (a1 lf (var x))))}) in H0.
  LexpSubst. clear H0.
  unfold Subst in H5;simpl in H5.
  assert (HS : (fun T : Type =>
                  tensor (perp (a1 lf (fc2 dj (flattenT (t (term T))) (t0 T))))
                         (witH (atom (a1 lf (flattenT (t (term T)))))
                               (atom (a1 lf (t0 T))))) =
               Tensor (Perp (A1 lf (FC2 dj t t0))) (With (Atom (A1 lf t)) (Atom (A1 lf t0))) ).
  extensionality T;simpl.
  rewrite TermFlattenG. auto.
  rewrite HS in H5. clear HS.
  inversion H5 ...
  (* H8 *)
  inversion H8;subst ...
  inversion H10...
  inversion H12;subst ...
  inversion H13;subst ...
  clear H10 H3  H4 H12 H13 H14 H16.
  (* H2 *)
  inversion H2;subst ...
  (* case Init *)
  apply encodeInvDisj in H1.
  destruct H1 as [L' H1].
  destruct H1 as [G H1].
  destruct H1 as [G' H1].
  destruct H1 as [H1  H1'].
  destruct H1' as [H1'  H1''].
  rewrite H1' in H17.
  rewrite H1' in H15.
  apply InvFLDj in H1''.
  destruct H1'' as [HGt HGt'].
  rewrite <- HGt'  in H17.
  rewrite <- HGt  in H15.
  eexists L'. exists G. exists G'. exists n. exists n1.
  split;auto.
  split;auto.
  split;auto.
  assert(HM:encodeFR F :: encodeFL G :: encodeList L' =mul=  
            (encodeFR F :: encodeList L') ++ [encodeFL G] ) ...  
  rewrite HM; assumption.

  assert(HM:encodeFR F :: encodeFL G' :: encodeList L' =mul=  
            (encodeFR F :: encodeList L') ++ [encodeFL G'] ) ...
  rewrite HM; assumption.
  
  
  (* cannot be from B *)
  apply AtomsTheoryFalse in H9. contradiction.
  (* cannot be a release *)
  inversion H3;subst.
  unfold lf in H4. simpl in H4. intuition.
Qed.



Lemma InvDRIGHT1 :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW DRIGHT1 -> exists   G1 G2 n1, n =  (S (S (S ( S (S n1)))))  /\ F = PL.disj G1 G2 /\ n1 |-F- Theory; encodeFR G1 :: encodeList L ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold DRIGHT1 in H0.
  LexpSubst. clear H0.
  unfold Subst in H4;simpl in H4.
  inversion H4;subst ...
  change (fun T : Type =>
            ex
              (fun x : T => tensor (perp (a1 rg (fc2 dj (t T) (var x)))) (atom (a1 rg (t T)))))
  with
  (E{ fun T x => tensor (perp (a1 rg (fc2 dj (t T) (var x)))) (atom (a1 rg (t T)))}) in H0.
  LexpSubst. clear H0.
  unfold Subst in H5;simpl in H5.
  assert(HS : (fun T : Type =>
                 tensor (perp (a1 rg (fc2 dj (flattenT (t (term T))) (t0 T))))
                        (atom (a1 rg (flattenT (t (term T))))))
              = Tensor (Perp (A1 rg (FC2 dj t t0))) (Atom (A1 rg t)) ).
  extensionality T;simpl.
  rewrite TermFlattenG. auto.
  rewrite HS in H5. clear HS.
  inversion H5 ...
  (* H8 *)
  inversion H8;subst ...
  (* cannot be an axiom *)
  inversion H9 ...
  apply A1InvN in H6;subst. unfold rg in H3. simpl in H3. intuition.
  (* cannot be from the theory *)
  apply AtomsTheoryFalse' in H10.
  contradiction.
  (* it is a release *)
  inversion H10;subst ...

  (* H2 *)
  inversion H2;subst ...
  apply EncSidesCorrect in H1.
  destruct H1 as [H1 H1'].
  apply InvDj in H1.
  destruct H1 as [G HG].
  destruct HG as [G' HG].
  destruct HG as [HG [HG' HG'']];subst.
  rewrite <- H1' in H13.
  rewrite <- HG' in H13.
  exists G. exists G'. eexists. 
  split;auto.
  split;auto.
  MReplace (encodeFR G :: encodeList L) ( encodeList L ++ [encodeFR G])...
  
  (* cannot be from the theory *)
  apply AtomsTheoryFalse in H14.
  contradiction.
  (* cannot be a release *)
  inversion H6;subst ...
  unfold rg in H7. simpl in H7. intuition.
Qed.


Lemma InvDRIGHT2 :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW DRIGHT2 -> exists   G1 G2 n1, n =  (S (S (S ( S (S n1)))))  /\ F = PL.disj G1 G2 /\ n1 |-F- Theory; encodeFR G2 :: encodeList L ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold DRIGHT2 in H0.
  LexpSubst. clear H0.
  unfold Subst in H4;simpl in H4.
  inversion H4;subst ...
  change  (fun T : Type =>
             ex
               (fun x : T =>
                  tensor (perp (a1 rg (fc2 dj (t T) (var x)))) (atom (a1 rg (var x)))))
  with
  (E{ fun T x => tensor (perp (a1 rg (fc2 dj (t T) (var x)))) (atom (a1 rg (var x)))} ) in H0.
  LexpSubst. clear H0.
  unfold Subst in H5;simpl in H5.
  assert(HS : (fun T : Type =>
                 tensor (perp (a1 rg (fc2 dj (flattenT (t (term T))) (t0 T))))
                        (atom (a1 rg (t0 T))))
              = Tensor (Perp (A1 rg (FC2 dj t t0))) (Atom (A1 rg t0)) ).
  extensionality T;simpl.
  
  rewrite TermFlattenG. auto.
  rewrite HS in H5. clear HS.
  inversion H5 ...
  (* H8 *)
  inversion H8;subst ...
  (* cannot be an axiom *)
  inversion H9 ...
  apply A1InvN in H6;subst. unfold rg in H3. simpl in H3. intuition.
  (* cannot be from the theory *)
  apply AtomsTheoryFalse' in H10.
  contradiction.
  (* it is a release *)
  inversion H10;subst ...

  (* H2 *)
  inversion H2;subst ...
  apply EncSidesCorrect in H1.
  destruct H1 as [H1 H1'].
  apply InvDj in H1.
  destruct H1 as [G HG].
  destruct HG as [G' HG].
  destruct HG as [HG [HG' HG'']];subst.
  rewrite <- H1' in H13.
  rewrite <- HG'' in H13.
  exists G. exists G'. eexists. 
  split;auto.
  split;auto.
  MReplace (encodeFR G' :: encodeList L) ( encodeList L ++ [encodeFR G']) ...

  (* cannot be from the theory *)
  apply AtomsTheoryFalse in H14.
  contradiction.
  (* cannot be a release *)
  inversion H6;subst ...
  unfold rg in H7. simpl in H7. intuition.
Qed.

Lemma InvIRight :forall F L n,  n |-F- Theory; (encodeFR F) :: encodeList L; DW IRIGHT -> exists   G1 G2 n1, n =  (S (S (S ( S (S (S (S n1)))))))  /\ F = PL.impl G1 G2 /\ n1 |-F- Theory; encodeFR G2 :: encodeFL G1 :: encodeList L ; UP [].
Proof with InvTac.
  intros.
  inversion H;subst ...
  unfold IRIGHT in H0.
  LexpSubst. clear H0.
  unfold Subst in H4;simpl in H4.
  inversion H4;subst ...
  change (fun T : Type =>
            ex
              (fun x : T =>
                 tensor (perp (a1 rg (fc2 im (t T) (var x))))
                        (par (atom (a1 lf (t T))) (atom (a1 rg (var x))))))
  with
  (E{ fun T x => tensor (perp (a1 rg (fc2 im (t T) (var x))))
                        (par (atom (a1 lf (t T))) (atom (a1 rg (var x))))}) in H0.
  
  LexpSubst. clear H0.
  unfold Subst in H5;simpl in H5.
  assert(HS : (fun T : Type =>
                 tensor (perp (a1 rg (fc2 im (flattenT (t (term T))) (t0 T))))
                        (par (atom (a1 lf (flattenT (t (term T)))))
                             (atom (a1 rg (t0 T))))) =
              Tensor (Perp (A1 rg (FC2 im t t0))) (Par (Atom (A1 lf t) ) (Atom (A1 rg t0) )) ) ...
  extensionality T;simpl.
  rewrite TermFlattenG. auto.
  rewrite HS in H5. clear HS.
  inversion H5 ...
  (* H8 *)
  inversion H8;subst ... clear H8.
  inversion H10 ... clear H10.
  inversion H9;subst ... clear H9.
  inversion H12;subst ... clear H3 H11 H10 H12.

  (* H2 *)
  inversion H2;subst ...
  apply EncSidesCorrect in H1.
  destruct H1 as [H1 H1'].
  apply InvIm in H1.
  destruct H1 as [G HG].
  destruct HG as [G' HG].
  destruct HG as [HG [HG' HG'']];subst.
  rewrite <- H1' in H13.

  rewrite <- HG'' in H13.
  apply LeftRightAtom in HG'.
  rewrite <- HG' in H13.
  exists G. exists G'. eexists.  
  split;auto.
  split;auto. 

  assert(HS:  encodeFR G' :: encodeFL G :: encodeList L =mul= 
              (encodeList L ++ [encodeFL G]) ++ [encodeFR G']) ...
  rewrite HS ...

  (* cannot be from the theory *)
  apply AtomsTheoryFalse in H9.
  contradiction.
  (* Cabbot be  release *)
  inversion H3;subst ...
  unfold rg in H6 ... intuition.
Qed.

Theorem Completeness : forall L F, ( encodeSequent L F ) -> exists n, L |-P- n ; F.
Proof with InvTac.
  intros.
  unfold encodeSequent in H.
  apply AdequacyTri2 in H.
  destruct H as [n].
  generalize dependent L.
  generalize dependent F.
  induction n using strongind;intros.
  + (* Base: inconsistent*)
    inversion H.
  + unfold Theory in H.
    inversion H0;subst.
    ++ (* The formula was taken from the context M *)
      (* This is inconsistent by Lemma encodePositive *)
      generalize( encodePositive L F);intro HPos.
      inversion HPos;subst.
      assert(encodeFR F = F0 \/ In F0 (encodeList L)). 
      eapply DestructMSet'; eauto.
      (*!! from H3 *)
      destruct H1;subst.
      contradiction.
      assert(IsPositiveAtom F0) by( eapply PositiveIn;eauto).
      contradiction.
      
    ++ assert(
           F0 = BLEFT \/ F0 = INIT \/ 
           F0 =  CRIGHT \/ F0 =  CLEFT \/ 
           F0 =  DRIGHT1 \/ F0 =  DRIGHT2 \/ 
           F0 =  DLEFT \/ F0 =  IRIGHT \/ F0 =  ILEFT).
       unfold Theory in H3.
       assert (In F0 [BLEFT; INIT; CRIGHT; CLEFT; DRIGHT1; DRIGHT2; DLEFT; IRIGHT; ILEFT]).
       apply In_to_in.
       rewrite H3; auto.
       destruct H1; eauto.
       destruct H1; eauto.
       destruct H1; eauto.
       destruct H1; eauto.
       destruct H1. do 4 right. left. eauto.
       destruct H1. do 5 right. left. eauto.
       destruct H1. do 6 right. left. eauto.
       destruct H1. do 7 right. left. eauto.
       destruct H1. do 8 right. eauto.
       inversion H1. 
       
       destruct H1  as [HF1 | [HF1 | [HF1 | [HF1 | [HF1 | [HF1 | [HF1 | [HF1 |HF1]]]]]]]];subst.
       +++ (* case BLeft *)
         apply AdequacyTri1 in H4.
         apply InvBLEFT in H4.
         destruct H4.
         eexists.
         eapply PL.botL;eauto.
       +++ (* Case Init *)
         apply AdequacyTri1 in H4.
         apply InvINIT in H4.
         destruct H4 as [L' [a [H4 H4']]];subst.
         eexists.
         apply PL.Exch with (L:= PL.atom a :: L');auto.
         eapply PL.init ...
       +++ (* case CRIGHT *)
         apply InvCRIGHT in H4.
         destruct H4 as [G1].
         destruct H1 as [G2].
         destruct H1 as [n1].
         destruct H1 as [n2].
         destruct H1. subst.
         destruct H4. subst.
         destruct H4. subst.
         destruct H4.
         apply H  with (m:=n1) in H4... destruct H4 as [n H4].
         apply H  with (m:=n2) in H5... destruct H5 as [m H5].
         eexists. eapply PL.cR;eauto.
         assert(n2 <= max n1 n2). apply Nat.le_max_r. omega.
         assert(n1 <= max n1 n2). apply Nat.le_max_l. omega.
       +++  (* case CLEFT *)
         apply InvCLEFT in H4.
         destruct H4 as [L' H4].
         destruct H4 as [G1 H4].
         destruct H4 as [G2 H4].
         destruct H4 as [n1 H4].
         destruct H4; subst.
         destruct H4; subst.
         assert(HL : encodeFR F :: encodeFL G1 :: encodeFL G2 :: encodeList L' =
                     encodeFR F :: encodeList (G1 :: G2 :: L')) by reflexivity.
         rewrite HL in H4. clear HL.
         apply H  with (m:=n1) in H4... destruct H4 as [n H4].

         eexists. eapply PL.cL;eauto.
         omega.
       +++ (* DISJ RIGHT 1 *)
         apply InvDRIGHT1 in H4.
         destruct H4 as [G1 H4].
         destruct H4 as [G2 H4].
         destruct H4 as [n1 H4].
         destruct H4; subst.
         destruct H4; subst.
         apply H with (m:=n1) in H4.
         destruct H4 as [n H4].
         eexists.
         apply PL.dR1;eauto.
         omega.
       +++ (* DISJ RIGHT 2 *)
         apply InvDRIGHT2 in H4.
         destruct H4 as [G1 H4].
         destruct H4 as [G2 H4].
         destruct H4 as [n1 H4].
         destruct H4; subst.
         destruct H4; subst.
         apply H with (m:=n1) in H4.
         destruct H4 as [n H4].
         eexists.
         apply PL.dR2;eauto.
         omega.
       +++ (* DISJ LEFT *)
         apply InvDLEFT in H4.
         destruct H4 as [L' H4].
         destruct H4 as [G1 H4].
         destruct H4 as [G2 H4].
         destruct H4 as [n1 H4].
         destruct H4 as [n2 H4].
         destruct H4; subst.
         destruct H4; subst.
         destruct H4.
         assert(HG1 : encodeFR F :: encodeFL G1 :: encodeList L' =
                      encodeFR F :: encodeList (G1 :: L')) by reflexivity.
         assert(HG2 : encodeFR F :: encodeFL G2 :: encodeList L' =
                      encodeFR F :: encodeList (G2 :: L')) by reflexivity.
         
         rewrite HG1 in H4.
         rewrite HG2 in H5.
         apply H  with (m:=n1) in H4... destruct H4 as [m1 H4].
         apply H  with (m:=n2) in H5... destruct H5 as [m2 H5].
         
         eexists. eapply PL.dL;eauto.
         assert(n2 <= max n1 n2). apply Nat.le_max_r. omega.
         assert(n1 <= max n1 n2). apply Nat.le_max_l. omega.
       +++ (* Implication Right *)
         apply InvIRight in H4.
         destruct H4 as [G1 H4].
         destruct H4 as [G2 H4].
         destruct H4 as [n1 H4].
         destruct H4; subst.
         destruct H4; subst.
         assert(HG : encodeFR G2 :: encodeFL G1 :: encodeList L =
                     encodeFR G2 :: encodeList (G1 :: L)) by reflexivity.
         rewrite HG  in H4.
         apply H with (m:=n1) in H4.
         destruct H4 as [n H4].
         eexists.
         apply PL.impR;eauto.
         omega.
       +++ (* IMP Left *)
         apply InvILEFT in H4.
         destruct H4 as [L' H4].
         destruct H4 as [G1 H4].
         destruct H4 as [G2 H4].
         destruct H4 as [n1 H4].
         destruct H4 as [n2 H4].
         destruct H4; subst.
         destruct H4; subst.
         destruct H4; subst.
         apply H with (m:=n1) in H4; 
           [|repeat apply Nat.le_le_succ_r; auto].
         destruct H4 as [n1' H4].
         assert(HS : encodeFR F :: encodeFL G2 :: encodeList L' =
                     encodeFR F :: encodeList (G2 :: L')) by reflexivity.
         rewrite HS  in H5;clear HS.

         apply H with (m:=n2) in H5; 
           [|repeat apply Nat.le_le_succ_r; auto]. 
         
         destruct H5 as [n2' H5].
         
         eexists.
         eapply PL.impL;eauto.
Qed.