Require Export LL.MultisetLL.
Require Export Syntax.
Require Export LL.MetaTheory.StrongInduction.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Omega.
Require Export LL.myTactics.
Require Export List.
Export ListNotations.
Require Import Coq.Program.Equality.


Set Implicit Arguments.

(* Asynchronous formulas *)

Definition AsynchronousF (F :lexp) :=
  match F with
  | Atom _ => false 
  | Perp _ => false 
  | Top => true
  | Bot => true
  | Zero => false
  | One => false
  | Tensor _ _ => false
  | Par _ _ => true
  | Plus _ _ => false
  | With _ _ => true
  | Bang _ => false
  | Quest _ => true
  end.

Inductive Asynchronous : lexp -> Prop :=
| ATop :   Asynchronous Top
| ABot :   Asynchronous Bot
| APar :   forall F G, Asynchronous (Par F G)
| AWith :  forall F G, Asynchronous (With F G)
| AQuest : forall F  , Asynchronous (Quest F).

Hint Constructors Asynchronous.

Theorem AsyncEqR : forall F:lexp, AsynchronousF F = true -> Asynchronous F.
Proof.
  intros.  
  destruct F;auto;try (inversion H).
Qed.

Theorem AsyncEqL : forall F:lexp, Asynchronous F -> AsynchronousF F = true.
Proof.
  intros.
  destruct F;inversion H;reflexivity.
Qed.

(* Negative Atoms *)
Inductive IsNegativeAtom : lexp -> Prop :=
  IsNA : forall v, IsNegativeAtom (Perp v).
  
Hint Constructors IsNegativeAtom.

Definition IsNegativeAtomF (F:lexp) :=
  match F with
  | Perp _ => true
  | _ => false
  end.

(* Complexity for list of formulas *)
Fixpoint exp_weight (P:lexp) : nat :=
  match P with
  | Atom X => 1
  | Perp X => 1
  | One => 1
  | Bot => 1
  | Zero => 1
  | Top => 1
  | Tensor X Y => 1 + (exp_weight X) + (exp_weight Y)
  | Par X Y => 1 + (exp_weight X) + (exp_weight Y)
  | Plus X Y => 1 + (exp_weight X) + (exp_weight Y)
  | With X Y  => 1 + (exp_weight X) + (exp_weight Y)
  | Bang X => 1 + exp_weight X
  | Quest X  => 1 + exp_weight X
  end.

Theorem exp_weight0 : forall  F:lexp, exp_weight F > 0.
Proof.
  intro.
  induction F;simpl;omega.
Qed.

Theorem exp_weight0F : forall  F:lexp, exp_weight F = 0%nat -> False.
Proof.
  intros.
  generalize(exp_weight0 F).
  intro.
  rewrite H in H0.
  inversion H0.
Qed.


(* Complexity of list of formulas  *)
Fixpoint L_weight (L: list lexp) : nat :=
  match L with
  | nil => 0
  | H :: L' => (exp_weight H) + (L_weight L')
  end.

Theorem exp_weight0LF : forall l L, 0%nat = exp_weight l + L_weight L -> False.
Proof.
  intros.
  assert(exp_weight l > 0%nat) by (apply exp_weight0).
  omega.
Qed.

Theorem L_weightApp : forall L M, L_weight (L ++M) = L_weight L + L_weight M.
Proof.
  intros.
  induction L; auto.
  simpl.
  rewrite IHL.
  omega.
Qed.

Lemma GtZero : forall n, n >0 -> exists n', n = S n'.
Proof.
  intros.
  destruct n.
  inversion H.
  exists n;auto.
Qed.


(* Lists of positive formulas *)
Fixpoint lexpPos (l: list lexp) : Prop :=
  match l with
  | nil => True
  | H :: T => (AsynchronousF H = false) /\ lexpPos(T)
  end.

Fixpoint BlexpPos (l: list lexp) : bool :=
  match l with
  | nil => true
  | H :: T => andb (negb (AsynchronousF H)) ( BlexpPos T)
  end.


Theorem PosBool : forall l, BlexpPos l = true <-> lexpPos l.
Proof.
  intros.
  split;induction l;simpl;auto.
  - intro.
    split.
    rewrite andb_true_iff in H.
    destruct H.
    auto.
    rewrite negb_true_iff in H.
    auto.
    rewrite andb_true_iff in H.
    destruct H.
    auto.
  - intro.
    destruct H.
    apply IHl in H0.
    rewrite H.
    simpl.
    auto.
Qed.

Inductive lexpPos' : list lexp -> Prop :=
  | l_nil : lexpPos' []
  | l_sin : forall a, (AsynchronousF a = false) -> lexpPos' [a]
  | l_cos : forall a l, lexpPos' [a] -> lexpPos' l -> lexpPos' (a::l).

Hint Resolve l_nil l_sin l_cos.

(* Properties of lexpPos *)
Lemma lexpPosUnion a L: lexpPos [a] -> lexpPos L -> lexpPos ([a] ++ L).
Proof.
  intros.
  simpl; firstorder.
Qed.  

Lemma lexpPosUnion_inv a L: lexpPos ([a] ++ L) -> lexpPos [a] /\ lexpPos L.
Proof.
  intros.
  simpl in H.
  split; firstorder.
Qed.

Lemma lexpPos_lexpPos' M: lexpPos' M <-> lexpPos M.
Proof.
  split; intros.
  * induction H;
    try solve [simpl; auto].
    apply lexpPosUnion; auto.
  * induction M; intros; auto.
    apply lexpPosUnion_inv in H.
    destruct H.
    apply l_cos; auto.
    apply l_sin; firstorder.
Qed.

Lemma LPos1 L M: L =mul= M -> lexpPos L -> lexpPos M.
Proof.
  intros P H.
  apply lexpPos_lexpPos'.
  apply lexpPos_lexpPos' in H.
  apply Permutation_meq in P.
  induction P; subst.
  * apply l_nil.
  * inversion H; subst.
    apply l_cos; auto.
    apply l_cos; auto.
  * inversion_clear H.
    inversion_clear H1. 
    apply l_cos; auto.
    apply l_cos; auto.
  * apply IHP2.
    apply IHP1;auto.
Qed.

Instance lexpPos_morph : Proper (meq ==> iff) (lexpPos).
Proof.
  intros L M Heq .
  split;intro.
  + eapply LPos1;eauto.
  + apply LPos1 with (L:=M);auto.
    
Qed.





Lemma LPos2 : forall M N L, L =mul= M ++ N -> lexpPos L -> lexpPos M.
Proof. 
  induction M;intros;simpl;auto.  
  assert (L =mul= M ++ (a::N)) by ( rewrite H; eauto).
  apply IHM in H1;auto.
  firstorder.
  apply LPos1 in H;auto.
  inversion H;auto.
Qed.

Lemma LPos3:  forall M N L, L =mul= M ++ N -> lexpPos L -> lexpPos N .
Proof.
  intros.
  rewrite union_comm_app in H.
  eapply LPos2 ;eassumption.
Qed.

Lemma WeightLeq: forall w l L, S w = L_weight (l :: L) -> L_weight L <= w.
Proof.
  intros.
  simpl in H.
  generalize (exp_weight0 l);intro.
  apply GtZero in H0.
  destruct H0.
  rewrite H0 in H.
  omega.
Qed.

Lemma AsynchronousFlexpPos : forall  l, AsynchronousF l = false -> lexpPos [l].
Proof.
  intros.
  constructor;auto.
  constructor.
Qed.


(* Arrows *)

Inductive Arrow : Set :=
| UP : list lexp -> Arrow
| DW : lexp -> Arrow.


Fixpoint eqArrow (exp_1 exp_2 : Arrow) :=
  match exp_1, exp_2 with
  | DW a, DW b =>  a = b
  | UP A, UP B =>  A = B
  | _, _ => False
  end.
  
Lemma eqArrow_refl: forall x, eqArrow x x.
Proof.
  induction x; simpl; auto.
Qed.

Lemma eqArrow_symm: forall x y, eqArrow x y -> eqArrow y x.
Proof. 
   induction x ; induction y; intros; simpl; auto.
Qed.
    
Lemma eqArrow_trans: forall x y z, eqArrow x y -> eqArrow y z -> eqArrow x z.
Proof.  
  induction x ; induction y; induction z; intros; simpl in *; auto; subst; auto.
  contradiction.
  contradiction.
Qed.

Hint Resolve eqArrow_refl eqArrow_symm eqArrow_trans.

Add Parametric Relation : Arrow eqArrow
  reflexivity proved by eqArrow_refl
  symmetry proved by eqArrow_symm
  transitivity proved by eqArrow_trans as eq_arrow.

Declare Instance eqArrow_Equivalence : Equivalence eqArrow. 

Lemma Arrow_eq_dec : forall A B: Arrow, {A = B} + {A <> B}.
Proof.
	intros A B; decide equality.
	apply list_eq_dec. 
	apply LExp_eq_dec.
	apply LExp_eq_dec.
Qed. 
 
Definition Arrow2LL (A: Arrow) : list lexp :=
  match A with
  | UP l => l
  | DW f => [f]
  end.                     


(* We assume a positive bias in the encodings *)
(* Definition of when a formula can be relased (from a positive phase to a negative phase *)
Definition ReleaseF (F:lexp ) :=
 match F with
 | Atom _ => false (* due to the bias *)
 | Perp _ => true 
 | Top => true
 | Bot => true
 | Zero => false
 | One => false
 | Tensor _ _ => false
 | Par _ _ => true
 | Plus _ _ => false
 | With _ _ => true
 | Bang _ => false
 | Quest _ => true
 end.

 Inductive Release : lexp-> Prop :=
 | RelNA : forall v, Release (Perp v)
 | RelTop : Release Top
 | RelBot : Release Bot
  | RelPar : forall F G, Release (Par F G)
| RelWith : forall F G, Release (With F G)
  | RelQuest : forall F, Release (Quest F).

 Hint Constructors Release.
 Theorem ReleaseR : forall F:lexp, ReleaseF F = true -> Release F.
 Proof.
   intros.
   destruct F;auto;try (inversion H).
 Qed.
 Theorem ReleaseL : forall F:lexp, Release F -> ReleaseF F = true.
 Proof.
   intros.
   destruct F;inversion H;reflexivity.
 Qed.

 
 (* Some definitions for the proof of completeness *)
 Inductive NotAsynchronous : lexp -> Prop :=
| NAAtomP :  forall v,  NotAsynchronous (Atom v)
| NAAtomN :  forall v,  NotAsynchronous (Perp v)
| NAZero :  NotAsynchronous Zero
| NAOne :  NotAsynchronous One
| NATensor : forall F G,  NotAsynchronous ( F ** G)
| NAPlus : forall F G,  NotAsynchronous ( Plus F  G)
| NABang : forall F,  NotAsynchronous ( ! F ).

Hint Constructors NotAsynchronous.
                                          
Theorem AsynchronousEquiv : forall F, NotAsynchronous F <-> ~ Asynchronous F.
Proof.
  intros.
  split.
  + destruct F; intros H Hn; try(inversion Hn) ; try (inversion H).
  + intro H.
    destruct F;auto; (try  contradict H; auto).
Qed.

Inductive PosOrPosAtom : lexp -> Prop :=
  | PPAtom :  forall v,  PosOrPosAtom (Atom v)
  | PPZero :  PosOrPosAtom Zero
  | PPOne :  PosOrPosAtom One
  | PPTensor : forall F G,  PosOrPosAtom ( F ** G)
  | PPPlus : forall F G,  PosOrPosAtom ( Plus F  G)
  | PPBang : forall F,  PosOrPosAtom ( ! F ).
  
Hint Constructors PosOrPosAtom.

Inductive NotPosOrPosAtom : lexp -> Prop :=
  | NPPAtom :  forall v,  NotPosOrPosAtom (Perp v)
  | NPPTop : NotPosOrPosAtom Top
  | NPPBot : NotPosOrPosAtom Bot
  | NPPPar : forall F G, NotPosOrPosAtom (Par F G)
  | NPPWith : forall F G, NotPosOrPosAtom (With F G)
  | NPPQuest : forall F , NotPosOrPosAtom (Quest F).
  
Hint Constructors NotPosOrPosAtom.

Lemma DecPosOrPosAtom1 : forall F, PosOrPosAtom F -> ~ NotPosOrPosAtom F.
Proof.
  intros F H Hn .
  destruct F;try (inversion H);try(inversion Hn).
Qed.

Lemma DecPosOrPosAtom : forall F, NotPosOrPosAtom F \/ PosOrPosAtom F.
Proof.
  intros.
  destruct F; [right | left   | left |left|right |right| right|left| right|left|right|left];auto.
Qed.
  
Lemma NotPosOrPosAtomRelease : forall F, NotPosOrPosAtom F -> ReleaseF F = true.
Proof.
  intros.
  destruct H;reflexivity.
Qed.

Lemma PosOrPosAtomAsync : forall F, PosOrPosAtom F ->  AsynchronousF F = false.
Proof.
  intros.
  destruct F;(try inversion H); reflexivity.
Qed.

Lemma plus_le_reg_r: forall n m p : nat, n + p <= m + p -> n <= m.
Proof.
  intros.
  assert (n+p = p + n) by (apply plus_comm).
  assert (m+p = p + m) by (apply plus_comm).
  rewrite H0 in H. rewrite H1 in H.
  eapply plus_le_reg_l in H.
  assumption.
Qed.



                                                            
