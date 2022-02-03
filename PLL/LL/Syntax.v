(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Syntax of Linear Logic 

Formulas in LL are build from the following syntax

<<
F:= A | A ^ | ⊤ | ⊥ | 0 | 1 | F ** F | F $ F | F ⊕ F | F & F | ! F | ? F
>>

where 
 - [A] is an atom (instance of [var]),
 - [A ^] is the negation of the atom [A].
 - [⊤,⊥,0,1] are the units
 - [F ** F] is multiplicative conjunction (tensor)
 - [F $ F] is multiplicative disjunction (par)
 - [F & F] is additive conjunction (oplus)
 - [F ⊕ F] is additive disjunction (oplus)
 - [!, ?] are the exponentials. 

The linear implication [F -o F] is defined as [A° $ B]. 

The usual dualities, moving negation inwards,  can be computed by [dual_LExp]. 

The weight (or complexity) of a formula can be obtained via [lexp_weight]. 

 *)


Require Export Bool.
Require Export Atoms.
Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Set Implicit Arguments.


(** Syntax  and Notation *)
Inductive lexp :=
| Atom    : var -> lexp
| Perp    : var -> lexp
| Top     : lexp
| Bot     : lexp
| Zero    : lexp
| One     : lexp
| Tensor  : lexp -> lexp -> lexp
| Par     : lexp -> lexp -> lexp
| Plus    : lexp -> lexp -> lexp
| With    : lexp -> lexp -> lexp
| Bang    : lexp -> lexp
| Quest   : lexp -> lexp.

Notation "⊥" := Bot.
Notation "⊤" := Top.
Notation "0" := Zero.
Notation "1" := One.
Notation "A ** B" := (Tensor A B) (at level 50) .
Notation "A $ B" := (Par A B) (at level 50) .
Notation "A ⊕ B" := (Plus A B) (at level 50).
Notation "A & B" := (With A B) (at level 50) .
Notation "! A" := (Bang A) (at level 50) .
Notation "? A" := (Quest A) (at level 50) .
Notation "A ⁺" := (Atom A) (at level 10) .
Notation "A ⁻" := (Perp A) (at level 10) .

(** Dualilities   *)
Fixpoint dual_LExp (X: lexp) :=
  match X with
  | Atom X 	 => Perp X 
  | Perp X 	 => Atom X
  | One => Bot
  | Bot => One
  | Zero => Top
  | Top => Zero  
  | Tensor X Y => Par (dual_LExp X) (dual_LExp Y)
  | Par X Y    => Tensor (dual_LExp X) (dual_LExp Y)
  | Plus X Y => With (dual_LExp X) (dual_LExp Y)
  | With X Y    => Plus (dual_LExp X) (dual_LExp Y)
  | Bang X   => Quest (dual_LExp X) 
  | Quest X  => Bang (dual_LExp  X) 
  end.

Notation "P °" := (dual_LExp P) (at level 1, left associativity, format "P °").

(** Linear implication as [A° $ B].  *)
Definition imp (A B: lexp): lexp := A° $ B.
Notation"A -o B"    := (imp A B) (at level 70).


Lemma neg2pos: forall A, Atom A = (Perp A)°.
Proof.
  intro; reflexivity. Qed.

Theorem ng_involutive: forall F: lexp, F = F°°.
Proof.
  intro. simpl. induction F; try reflexivity; simpl;
	          try rewrite <- IHF1; 
	          try rewrite <- IHF2; try reflexivity;
	            rewrite <- IHF; reflexivity. 
Qed.

#[export] Hint Rewrite neg2pos ng_involutive : core.

(** Decidability of equality on formulas *)
Lemma LExp_eq_dec : forall A B: lexp, {A = B} + {A <> B}.
Proof.
  intros A B; decide equality;
    apply Var_eq_dec.
Qed.

Fixpoint LExpEq (exp_1 exp_2: lexp) :=
  match exp_1, exp_2 with
  | Atom a, Atom b => VarEq a b
  | Perp a, Perp b => VarEq a b
  | Bot, Bot => true
  | Top, Top => true
  | One, One => true
  | Zero, Zero => true  
  | Tensor a b, Tensor c d
    => andb (LExpEq a c) (LExpEq b d)
  | Par a b, Par c d
    => andb (LExpEq a c) (LExpEq b d)
  | Plus a b, Plus c d
    => andb (LExpEq a c) (LExpEq b d)
  | With a b, With c d
    => andb (LExpEq a c) (LExpEq b d)
  | Bang a, Bang b
    => LExpEq a b
  | Quest a, Quest b
    => LExpEq a b 
  | _, _ => false
  end.

Fixpoint eqLExp (exp_1 exp_2: lexp) :=
  match exp_1, exp_2 with
  | Atom a, Atom b => eqVar a b
  | Perp a, Perp b => eqVar a b
  | Bot, Bot => True
  | Top, Top => True
  | One, One => True
  | Zero, Zero => True	
  | Tensor a b, Tensor c d
    => (eqLExp a c) /\ (eqLExp b d)
  | Par a b, Par c d
    => (eqLExp a c) /\  (eqLExp b d)
  | Plus a b, Plus c d
    => (eqLExp a c) /\ (eqLExp b d)
  | With a b, With c d
    => (eqLExp a c) /\  (eqLExp b d)
  | Bang a, Bang b
    => eqLExp a b
  | Quest a, Quest b 
    => eqLExp a b
  | _, _ => False
  end.


Theorem eqExpA: forall a b, eqLExp (a ⁺) (b ⁺) <-> a = b .
Proof.
  split; intros.
  simpl in H. auto.
  subst; simpl; auto.
Qed.

Theorem eqExpP: forall a b, eqLExp (a ⁻) (b ⁻) <-> a = b .
Proof.
  split; intros.
  simpl in H. auto.
  subst; simpl; auto.
Qed.

Lemma eqLExp_refl: forall x, eqLExp x x.
Proof.
  auto.
  induction x; simpl; auto;
    unfold eqVar;unfold VarEq; 
      destruct (Var_eq_dec); auto. 
Qed.
#[export] Hint Resolve eqLExp_refl : core.

Lemma eq_then_eqLExp: forall A B, A = B -> eqLExp A B.
Proof. intros; rewrite H; auto. Qed.

Lemma eqLExp_then_eq: forall A B,  eqLExp A B -> A = B.
Proof.
  induction A; induction B; intros; try reflexivity; try auto; try inversion H.
  apply eqExpA in H1; rewrite H1; auto.
  apply eqExpP in H1; rewrite H1; auto.

  rewrite IHA1 with (B:=B1); auto.
  rewrite IHA2 with (B:=B2); auto.
  rewrite IHA1 with (B:=B1); auto.
  rewrite IHA2 with (B:=B2); auto.
  rewrite IHA1 with (B:=B1); auto.
  rewrite IHA2 with (B:=B2); auto.
  rewrite IHA1 with (B:=B1); auto.
  rewrite IHA2 with (B:=B2); auto.

  rewrite IHA with (B:=B); auto.
  rewrite IHA with (B:=B); auto.
Qed.

#[export] Hint Resolve eqLExp_then_eq eq_then_eqLExp : core.


Lemma tns_eq f1 f2 g1 g2 : f1 ** g1 = f2 ** g2 <-> f1=f2/\g1=g2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H.
  destruct H. auto.
  destruct H; subst. auto. 
Qed.
Lemma par_eq f1 f2 g1 g2 : f1 $ g1 = f2 $ g2 <-> f1=f2/\g1=g2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H.
  destruct H. auto.
  destruct H; subst. auto. 
Qed.
Lemma pls_eq f1 f2 g1 g2 : f1 ⊕ g1 = f2 ⊕ g2 <-> f1=f2/\g1=g2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H.
  destruct H. auto.
  destruct H; subst. auto. 
Qed.
Lemma wth_eq f1 f2 g1 g2 : f1 & g1 = f2 & g2 <-> f1=f2/\g1=g2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H.
  destruct H. auto.
  destruct H; subst. auto. 
Qed.
Lemma bng_eq f1 f2 : ! f1 = ! f2 <-> f1=f2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H; auto.
  subst; auto. 
Qed.
Lemma qst_eq f1 f2 : ? f1 = ? f2 <-> f1=f2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H; auto.
  subst; auto. 
Qed.
Lemma atp_eq f1 f2 : f1⁺ = f2⁺ <-> f1=f2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H; auto.
  subst; auto. 
Qed.
Lemma atn_eq f1 f2 : f1⁻ = f2⁻ <-> f1=f2.
Proof.
  split; intros.
  apply eq_then_eqLExp in H.
  simpl in H; auto.
  subst; auto. 
Qed.
#[export] Hint Resolve tns_eq par_eq pls_eq wth_eq bng_eq qst_eq atp_eq atn_eq : core.

Lemma eqLExp_symm: forall x y, eqLExp x y -> eqLExp y x.
Proof. intros. apply eqLExp_then_eq in H; auto. Qed.
#[export] Hint Resolve eqLExp_symm : core.

Lemma eqLExp_trans: forall x y z, eqLExp x y -> eqLExp y z -> eqLExp x z.
Proof. intros;
         apply eqLExp_then_eq in H; 
         apply eqLExp_then_eq in H0; subst; auto. Qed.
#[export] Hint Resolve eqLExp_trans : core.


Add Parametric Relation : lexp eqLExp
    reflexivity proved by eqLExp_refl
    symmetry proved by eqLExp_symm
    transitivity proved by eqLExp_trans as eq_linear.

#[export] Instance eqLExp_Equivalence : Equivalence eqLExp.
Proof.
  exact eq_linear. Qed.

Lemma dif_then_no_eqLExp: forall A B, A <> B <-> ~ eqLExp A B.
Proof. split; intros; intro; apply H; auto. Qed.

Lemma eqLExp_dec : forall (f1 f2 : lexp),
    {eqLExp f1 f2} + {~ eqLExp f1 f2}.
Proof.
  intros.
  destruct (LExp_eq_dec f1 f2); subst.
  * left; auto.
  * right; auto.
Qed.

(** Weight  (complexity) of a formula  *)
Fixpoint lexp_weight (P:lexp) : nat :=
  match P with
  | Atom X => 0
  | Perp X => 0
  | One => 0
  | Bot => 0
  | Zero => 0
  | Top => 0
  | Tensor X Y => 1 + (lexp_weight X) + (lexp_weight Y)
  | Par X Y => 1 + (lexp_weight X) + (lexp_weight Y)
  | Plus X Y => 1 + (lexp_weight X) + (lexp_weight Y)
  | With X Y  => 1 + (lexp_weight X) + (lexp_weight Y)
  | Bang X => 1 + lexp_weight X
  | Quest X  => 1 + lexp_weight X
  end.

Lemma lweight_dual : forall F: lexp, lexp_weight F = lexp_weight F°.
Proof.
  induction F; auto; simpl;
    try rewrite IHF1; try rewrite IHF2; auto.
Qed.

Lemma lweight_dual_plus : forall F G, lexp_weight F + lexp_weight G = lexp_weight F° + lexp_weight G°.
Proof.
  intros.
  rewrite lweight_dual with (F:=F).
  rewrite lweight_dual with (F:=G).
  auto.
Qed.

Lemma not_eqLExp_sym : forall x y: lexp, ~ eqLExp x y -> ~ eqLExp y x.
Proof.
  intros.
  induction x; induction y; auto.
Qed.


Generalizable All Variables.

#[export] Instance tns_morph : Proper (eqLExp ==> eqLExp ==> eqLExp) Tensor.
Proof. intros a b ab c d cd. firstorder. Qed.

#[export] Instance par_morph : Proper (eqLExp ==> eqLExp ==> eqLExp) Par.
Proof. intros a b ab c d cd. firstorder. Qed.

#[export] Instance pls_morph : Proper (eqLExp ==> eqLExp ==> eqLExp) Plus.
Proof. intros a b ab c d cd. firstorder. Qed.

#[export] Instance wth_morph : Proper (eqLExp ==> eqLExp ==> eqLExp) With.
Proof. intros a b ab c d cd. firstorder. Qed.

#[export] Instance bng_morph : Proper (eqLExp ==> eqLExp) Bang.
Proof. intros a b ab. firstorder. Qed.

#[export] Instance qst_morph : Proper (eqLExp ==> eqLExp) Quest.
Proof. intros a b ab. firstorder. Qed.

#[export] Instance atm_morph : Proper (eqVar ==> eqLExp) Atom.
Proof. intros a b ab. firstorder. Qed.

#[export] Instance prp_morph : Proper (eqVar ==> eqLExp) Perp.
Proof. intros a b ab. firstorder. Qed.

#[export] Instance lexp_morph : Proper (eqLExp ==> eqLExp ==> iff)  eqLExp.
Proof. intros a b ab c d cd. firstorder. 
       refine (eqLExp_trans _ _ _ _ cd). 
       refine (eqLExp_trans _ _ _ _ H).
       auto.
       refine (eqLExp_trans _ _ _ ab _). 
       refine (eqLExp_trans _ _ _ H _).
       auto.
Qed.

#[export] Instance dual_morph : Proper (eqLExp ==> eqLExp) dual_LExp.
Proof. intros a b ab. apply eqLExp_then_eq in ab. 
       rewrite ab. auto. Qed.
