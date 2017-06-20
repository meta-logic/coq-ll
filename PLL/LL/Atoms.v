(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Atomic Propositions
    
Atomic propositions in LL are represented by the type [var] 

[Parameter var: Set.]

We assume that equality on such atomic propositions is decidablee 

[Axiom Var_eq_dec : forall x y : var, {x = y} + {x <> y}.]


 *)
Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Bool.Bool.
Set Implicit Arguments.

(** Type for atomic propositions *)
Parameter var: Set.

(** Decidability of equality on atomic propositions *)
Axiom Var_eq_dec : forall x y : var, {x = y} + {x <> y}.   
Hint Resolve Var_eq_dec.

(** Equality on atomic propositions *)
Definition VarEq (x y: var):= 
  match Var_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

Definition eqVar (x y: var):= 
  VarEq x y = true.

(** Reflexivity *)
Lemma eqVar_refl: forall x, eqVar x x.
Proof.
  intros.
  unfold eqVar. 
  unfold VarEq.
  destruct (Var_eq_dec x x); auto. 
Qed.

(** Symmetry *)
Lemma eqVar_symm: forall x y, eqVar x y -> eqVar y x.
Proof.
  intros.
  unfold eqVar in *. 
  unfold VarEq in *.
  destruct (Var_eq_dec y x); auto.
  destruct (Var_eq_dec x y); auto.
Qed.

(** Transitivity *)
Lemma eqVar_trans: forall x y z, eqVar x y -> eqVar y z -> eqVar x z.
Proof.
  intros.
  unfold eqVar in *. 
  unfold VarEq in *.
  destruct (Var_eq_dec x z); auto.
  destruct (Var_eq_dec y z); auto.
  destruct (Var_eq_dec x y); auto.
  rewrite <- e0 in e.
  contradiction.
Qed.

Hint Resolve eqVar_refl eqVar_symm eqVar_trans.

(** [eqVar] is an equivalence relation *)
Add Parametric Relation : var eqVar
    reflexivity proved by eqVar_refl
    symmetry proved by eqVar_symm
    transitivity proved by eqVar_trans as eq_var.

(** Reflexivity *)
Lemma eqVar_refl': forall x, VarEq x x = true.
Proof.
  intros.
  unfold VarEq.
  destruct (Var_eq_dec x x); auto.
Qed.

(** Symmetry *)
Lemma eqVar_symm': forall x y, VarEq x y = true -> VarEq y x = true.
Proof.
  intros.
  unfold VarEq in *.
  destruct (Var_eq_dec y x); auto.
  destruct (Var_eq_dec x y); auto.
Qed.

(** Transitivity *)
Lemma eqVar_trans': forall x y z, VarEq x y  = true -> VarEq y z = true -> VarEq x z = true.
Proof.
  intros.
  unfold VarEq in *.
  destruct (Var_eq_dec x z); auto.
  destruct (Var_eq_dec y z); auto.
  destruct (Var_eq_dec x y); auto.
  rewrite <- e0 in e.
  contradiction.
Qed.

Hint Resolve eqVar_refl' eqVar_symm' eqVar_trans'.

Theorem eqVar_then_eq : forall x y, VarEq x y = true -> x = y.
Proof.
  intros.
  unfold VarEq in H.
  destruct (Var_eq_dec x y); auto.
  inversion H.
Qed.

Hint Resolve eqVar_then_eq.
