(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Syntax of Linear Logic 

Formulas in LL are build from the following syntax

<<
F:= A | A ^ | ⊤ | ⊥ | 0 | 1 | F ** F | F $ F | F ⊕ F | F & F | ! F | ? F 
    | E{ FX} | F{ FX}
>>

where 
 - [A] is an atom. 
 - [A ^] is the negation of the atom [A].
 - [⊤,⊥,0,1] are the units
 - [F ** F] is multiplicative conjunction (tensor)
 - [F $ F] is multiplicative disjunction (par)
 - [F & F] is additive conjunction (oplus)
 - [F ⊕ F] is additive disjunction (oplus)
 - [!, ?] are the exponentials. 
 - [E {FX}] existential quantifier
 - [F {FX}] universal quantifier

The usual dualities, moving negation inwards,  can be computed by [Dual_LExp] (notation [A°]). 

The linear implication [F -o F] is defined as [A° $ B]. 


The weight (or complexity) of a formula can be obtained via [Lexp_weight]. 

This file also defines the polarity of formulas following Andreoli's focused system (https://www.cs.cmu.edu/~fp/courses/15816-s12/misc/andreoli92jlc.pdf). Many lemmas on polarities are proved in Section [Polarities].

 *)

Require Export Bool.
Require Export Arith.
Require Export Nat.
Require Import AuxResults.
Require Export Multisets.
Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import StrongInduction.
Require Export Eqset.
Export ListNotations.
Set Implicit Arguments.

Module Syntax_LL (DT : Eqset_dec_pol).
  Export DT.
  

  (** ** Parametric HOAS
      Take a look on #< a href="http://adam.chlipala.net/cpdt/html/Hoas.html">Library Hoas</a>#. 
   *)
  Section Sec_lExp.
    Variable T : Type. (* Parametric HOAS *)

    Inductive term  :=
    |var (t: T) (* variables *)
    |cte (e:A) (* constants from the domain DT.A *)
    |fc1 (n:nat) (t: term) (* family of functions of 1 argument *)
    |fc2 (n:nat) (t1 t2: term). (* family of functions of 2 argument *)
    
    Inductive aprop := (* atomic propositions *)
    | a0 : nat -> aprop (* 0-ary predicates *)
    | a1 : nat -> term -> aprop (* unary predicates *)
    | a2 : nat -> term -> term -> aprop. (* binary predicates *)
    
    Inductive lexp  :=
    | atom (a :aprop) (* atoms *)
    | perp (a: aprop) (* negated atoms *)
    | top | bot | zero | one  (* constants *)
    | tensor (F G : lexp)
    | par    (F G : lexp)
    | plus   (F G : lexp)
    | witH   (F G : lexp)
    | bang   (F : lexp)
    | quest  (F : lexp) 
    | ex     (f : T ->lexp) (* quantifiers *)
    | fx     (f : T ->lexp) .
  End Sec_lExp.
  
  (***** Avoiding The parameter T ***********)
  Arguments var [T].   Arguments cte [T].
  Arguments fc1 [T].   Arguments fc2 [T].
  Arguments a0 [T]. Arguments a1 [T]. Arguments a2 [T]. 
  Arguments atom [T]. Arguments perp [T].
  Arguments top [T]. Arguments one [T]. Arguments bot [T]. Arguments zero [T].
  Arguments tensor [T]. Arguments par [T]. Arguments plus [T]. Arguments witH [T].
  Arguments bang [T]. Arguments quest [T].
  Arguments ex [T]. Arguments fx [T].
  (*****************************************)

  (**************************************************)
  (* Types for lexp *)
  (* all of them closed terms (forall T:Type ... ) *)
  (**************************************************)
  Definition Term := forall T:Type,  term T. (* type for terms *)
  Definition AProp := forall T:Type, aprop T. (* type for atomic propositions *)
  Definition Lexp := forall T:Type, lexp T. (* Type for formulas *)
  Definition Subs := forall T:Type,  T -> lexp T. (* Type for substitutions *)
  Definition SubsL := list Subs. (* Type for substitutions on lists *)

  (* Useful Constructors (poly version of the connectives) *)
  Definition Cte (t : A) : Term := fun _ => cte t.
  Definition FC1 (n:nat) (t:Term): Term := fun _ => fc1 n (t _).
  Definition FC2 (n:nat) (t t':Term): Term := fun _ => fc2 n (t _) (t' _).
  Definition A0 (n : nat) : AProp := fun _ => a0 n.
  Definition A1 (n : nat) (t:Term) : AProp := fun _ => a1 n (t _).
  Definition A2 (n : nat) (t t':Term) : AProp := fun _ => a2 n (t _) (t' _).
  Definition Atom  (P: AProp) :Lexp :=  fun _ => atom (P _).
  Definition Perp  (P: AProp) :Lexp :=  fun _ => perp(P _). 
  Definition Top   :Lexp := fun _ => top .
  Definition Bot   :Lexp := fun _ => bot.
  Definition One   :Lexp := fun _ => one.
  Definition Zero   :Lexp := fun _ => zero .
  Definition Tensor  (F G: Lexp) :Lexp :=  fun _ => tensor (F _) (G _).
  Definition Par  (F G: Lexp) :Lexp :=  fun _  => par (F _) (G _).
  Definition Plus  (F G: Lexp) :Lexp :=  fun _ => plus (F _) (G _).
  Definition With  (F G: Lexp) :Lexp :=  fun _ => witH (F _) (G _).
  Definition Bang  (F: Lexp) :Lexp :=  fun _ => bang (F _ ).
  Definition Quest  (F: Lexp) :Lexp :=  fun _ => quest (F _ ).
  Definition Ex  (Fx : Subs) : Lexp := fun _ => ex (Fx _).
  Definition Fx  (Fx : Subs) : Lexp := fun _ => fx (Fx _).

  (** Closed Terms *)
  Inductive ClosedT : Term -> Prop :=
  | cl_cte: forall C, ClosedT (Cte C)
  | cl_fc1: forall n t1, ClosedT t1 -> ClosedT (FC1 n t1)
  | cl_fc2: forall n t1 t2, ClosedT t1 -> ClosedT t2 -> ClosedT (FC2 n t1 t2).
  
  (** Closed Atomic Propositions *)
  Inductive ClosedA : AProp -> Prop :=
  | cl_a0 : forall n, ClosedA (A0 n)
  | cl_a1 : forall n t, ClosedT t -> ClosedA (fun _ => a1 n (t _))
  | cl_a2 : forall n t t', ClosedT t -> ClosedT t' -> ClosedA (fun _ => a2 n (t _) (t' _)).

  (** Closed Formulas *)
  Inductive Closed : Lexp -> Prop :=
  | cl_atom : forall A, ClosedA A -> Closed (Atom A )
  | cl_perp : forall A, ClosedA A -> Closed (Perp A )
  | cl_one : Closed One
  | cl_bot : Closed Bot
  | cl_zero : Closed Zero
  | cl_top : Closed Top
  | cl_tensor : forall F G, Closed F -> Closed G -> Closed (Tensor F G)
  | cl_par : forall F G, Closed F -> Closed G -> Closed (Par F G)
  | cl_plus : forall F G, Closed F -> Closed G -> Closed (Plus F G)
  | cl_with : forall F G, Closed F -> Closed G -> Closed (With F G)
  | cl_bang : forall F, Closed F -> Closed (Bang F)
  | cl_quest : forall F, Closed F -> Closed (Quest F)
  | cl_ex : forall FX, Closed (Ex FX)
  | cl_fx : forall FX, Closed (Fx FX).

  (** Axioms of Closedeness *)
  Axiom ax_closedT : forall X:Term, ClosedT X.
  Axiom ax_closedA : forall A: AProp, ClosedA A.
  Axiom ax_closed : forall F:Lexp, Closed F.

  (** We assume equality on formulas to be decidable *)
  Axiom FEqDec : forall (F G: Lexp ),  {F = G} + {F <> G}.
  Lemma not_eqLExp_sym : forall x y: Lexp,  x <> y -> y <> x.
  Proof. intuition.
  Qed.

  (* Case analysis on a formula *)
  Ltac caseLexp F :=
    let Hx := fresh "HF" in
    assert(Hx : Closed F) by (apply ax_closed);
    inversion Hx.
  (* Induction on a formula *)
  Ltac indLexp F :=
    let Hx := fresh "HF" in
    assert(Hx : Closed F) by (apply ax_closed);
    induction Hx.
  (* Dealing with equality on LExp *)
  Ltac lexp_contr H :=
    eapply @equal_f_dep with (x:=unit) in H;
    inversion H.
  Ltac lexp_contr_unit H :=
    eapply @equal_f_dep with (x:=unit) in H;
    inversion H.
  Ltac LexpContr :=
    try(match goal with [H : ?F = ?G |- _] =>
                        assert(False) by lexp_contr_unit H;contradiction
        end).
  
  
  (************************************)
  (* Dualities on formulas *)
  (************************************)
  Section Dualities.
    Variable T: Type.
    (** Dualilities   *)
    Fixpoint dual_LExp (X: lexp T) :=
      match X with
      | atom A 	 => perp A 
      | perp A 	 => atom A
      | one => bot
      | bot => one
      | zero => top
      | top => zero  
      | tensor F G => par (dual_LExp F) (dual_LExp G)
      | par F G    => tensor (dual_LExp F) (dual_LExp G)
      | plus F G => witH (dual_LExp F) (dual_LExp G)
      | witH F G    => plus (dual_LExp F) (dual_LExp G)
      | bang F   => quest (dual_LExp F) 
      | quest F  => bang (dual_LExp  F)
      | ex X => fx (fun x => dual_LExp (X x))
      | fx X => ex (fun x => dual_LExp (X x))
      end.

    Theorem ng_involutive: forall F: lexp T, F = dual_LExp (dual_LExp F).
    Proof.
      intro. 
      induction F; simpl; auto;
        try( try(rewrite <- IHF1); try(rewrite <- IHF2); try(rewrite <- IHF);auto);
        try(assert (f = fun x =>  dual_LExp (dual_LExp (f x))) by
               (extensionality t; apply H); rewrite <- H0; auto).
    Qed.

    (** Linear implication *)
    Definition imp (A B: lexp T): lexp T := par (dual_LExp A) B.
  End Dualities.

  Arguments dual_LExp [T].
  
  Definition Imp (A B : Lexp) : Lexp := fun _ => imp (A _) (B _).
  Definition Dual_LExp (X: Lexp) : Lexp := fun _ => dual_LExp (X _).

  (**************************************)
  (* Notation on Formulas *)
  (**************************************)
  Module LLNotation.
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
    Notation "'F{' FX '}'" := (Fx FX) (at level 10) .
    Notation "'E{' FX '}'" := (Ex FX) (at level 10) .
    Notation "P °" := (Dual_LExp P) (at level 1, left associativity, format "P °").
    Notation"A -o B"    := (Imp A B) (at level 70).
  End LLNotation.

  Export LLNotation.

  Lemma one_bot : 1° = ⊥.
  Proof. auto. Qed.
  Lemma bot_one : ⊥° = 1.
  Proof. auto. Qed.  
  Lemma top_zero : ⊤° = 0.
  Proof. auto. Qed.
  Lemma zero_top : 0° = ⊤.
  Proof. auto. Qed.


  Lemma atom_perp A: (A ⁺)° = A ⁻.
  Proof. auto. Qed.  
  Lemma perp_atom A: (A ⁻)° = A ⁺.
  Proof. auto. Qed. 
  
  Lemma tensor_par A B: (A ** B)° = A° $ B°.
  Proof. extensionality T.  apply @equal_f_dep. auto. Qed.
  Lemma par_tensor A B: (A $ B)° = A° ** B°.
  Proof. extensionality T.  apply @equal_f_dep. auto. Qed.
  Lemma with_plus A B: (A & B)° = A° ⊕ B°.
  Proof. extensionality T.  apply @equal_f_dep. auto. Qed.
  Lemma plus_with A B: (A ⊕ B)° = A° & B°.
  Proof. extensionality T.  apply @equal_f_dep. auto. Qed.
  
  Lemma bang_quest A: (! A)° = ? A°.
  Proof. auto. Qed.  
  Lemma quest_bang A: (? A )° = ! A°.
  Proof. auto. Qed. 
  
  Lemma fx_ex FX: F{FX}° = Ex (fun _ x => dual_LExp(FX _ x)).
  Proof. extensionality T.  apply @equal_f_dep. auto. Qed.
  Lemma ex_fx FX: E{FX}° = Fx (fun _ x => dual_LExp(FX _ x)).
  Proof. extensionality T.  apply @equal_f_dep. auto. Qed.

  Lemma AtomNeg : forall A, (A ⁻)° = A ⁺.
    intro.
    reflexivity.
  Qed.
  Lemma AtomPos : forall A, (A ⁺)° = A ⁻.
    intro.
    reflexivity.
  Qed.
  
  
  
  Lemma Neg2pos: forall A, Atom A = Dual_LExp (Perp A).
  Proof. intro; reflexivity. Qed.
  
  Theorem Ng_involutive: forall F: Lexp, F = Dual_LExp (Dual_LExp F).
  Proof.
    intro.
    unfold Dual_LExp.
    extensionality T.
    rewrite <- ng_involutive with (T:=T).
    reflexivity.
  Qed.
  
  Hint Rewrite Neg2pos Ng_involutive.

  

  (**********************************************)
  (* Substitutions *)
  (**********************************************)
  Section Substitution.
    Variable T : Type.
    Fixpoint flattenT   (t : term ( (term T))) : term T :=
      match t with
      | var x => x
      | cte x => cte x
      | fc1 n x => fc1 n (flattenT x)
      | fc2 n x y => fc2 n (flattenT x) (flattenT y)
      end.
    
    Fixpoint flatten   (e : lexp ( (term T))) : lexp ( T) :=
      match e with
      | atom (a0 n) => atom (a0 n)
      | atom (a1 n t) => atom (a1 n (flattenT t))
      | atom (a2 n t t') => atom (a2 n (flattenT t) (flattenT t'))
      | perp (a0 n) => perp (a0 n)
      | perp (a1 n t) => perp (a1 n (flattenT t))
      | perp (a2 n t t') => perp (a2 n (flattenT t) (flattenT t'))
      | top => top
      | bot => bot
      | zero => zero
      | one => one
      | tensor F G => tensor (flatten F)  (flatten G)
      | par F G => par (flatten F)  (flatten G)
      | plus F G => plus (flatten F)  (flatten G)
      | witH F G => witH (flatten F)  (flatten G)
      | bang F => bang (flatten F)  
      | quest F => quest (flatten F)  
      | ex FX => ex (fun x => flatten (FX  (var x)))
      | fx FX => fx (fun x => flatten (FX  (var x)))
      end.
  End Substitution.

  (* Poly version of substitutions *)
  Definition Subst   (S : Subs ) (X : Term)  : Lexp :=
    fun T:Type  => flatten (S (term T) (X T)).

  Fixpoint SubstL   (S : SubsL ) (X : Term)  : list Lexp := map (fun s => Subst s X) S.
  
  

  
  (************************************************)
  (* Equality On LExp Formulas *)
  (************************************************)

  Section EqualityFormulas. 
    Lemma AtomEq: forall A A', Atom A = Atom A' -> A = A'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma PerpEq: forall A A', Perp A = Perp A' -> A = A'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    (*Lemma A1eq : forall n n' t t', A1 n t = A1 n' t' -> t = t'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma A1eqn : forall n n' t t', A1 n t = A1 n' t' -> n = n'.
      intros.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H. auto.
    Qed.

    
    Lemma A2eq : forall n t1 t2 t1' t2', A2 n t1 t2 = A2 n t1' t2' -> t1 = t1'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma A2eq' : forall n t1 t2 t1' t2', A2 n t1 t2 = A2 n t1' t2' -> t2 = t2'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.*)
    
    Lemma ParEq1 : forall F G F0 G0,  F0 $ G0 = F $ G -> F = F0.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma ParEq2 : forall F G F0 G0,  F0 $ G0 = F $ G -> G = G0.
      intros. extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    Lemma WithEq1 : forall F G F0 G0,  F0 & G0 = F & G -> F = F0.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma WithEq2 : forall F G F0 G0,  F0 & G0 = F & G -> G = G0.
      intros. extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    Lemma TensorEq1 : forall F G F0 G0,  F0 ** G0 = F ** G -> F = F0.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma TensorEq2 : forall F G F0 G0,  F0 ** G0 = F ** G -> G = G0.
      intros. extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    Lemma PlusEq1 : forall F G F0 G0,  F0 ⊕ G0 = F ⊕ G -> F = F0.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    Lemma PlusEq2 : forall F G F0 G0,  F0 ⊕ G0 = F ⊕ G -> G = G0.
      intros. extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    Lemma BangEq : forall F F',  ! F = ! F'-> F = F'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    
    Lemma QuestEq : forall F F',  ? F = ? F'-> F = F'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.
    
    Lemma FxEq : forall F F',  F{ F } = F{ F' }-> F = F'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.

    Lemma ExEq : forall F F',  E{ F } = E{ F' }-> F = F'.
      intros.
      extensionality T. apply @equal_f_dep with (x:=T) in H.
      inversion H. auto.
    Qed.

    Lemma CteEqt : forall t t',  Cte t = Cte t' -> t = t'.
      intros.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H;auto.
    Qed.


    Lemma F1Eqn : forall n n' t t',  FC1 n t = FC1 n' t' -> n = n'.
      intros.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H;auto.
    Qed.

    Lemma F1Eqt : forall n n' t t',  FC1 n t = FC1 n' t' -> t = t'.
      intros.
      extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H;auto.
    Qed.

    Lemma F2Eqn : forall n1 n2 t1 t1' t2 t2',  FC2 n1 t1 t2 = FC2 n2 t1' t2' -> n1 = n2.
      intros.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H;auto.
    Qed.


    Lemma F2Eqt1 : forall n1 n2 t1 t1' t2 t2',  FC2 n1 t1 t2 = FC2 n2 t1' t2' -> t1 = t1'.
      intros.
      extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H;auto.
    Qed.

    Lemma F2Eqt2 : forall n1 n2 t1 t1' t2 t2',  FC2 n1 t1 t2 = FC2 n2 t1' t2' -> t2 = t2'.
      intros.
      extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H;auto.
    Qed.

    Lemma Terms_cte_fc1 : forall t n t', Cte t <> FC1 n t'.
      intros t n t' Hn.
      apply @equal_f_dep with (x:=unit) in Hn.
      inversion Hn.
    Qed.

    Lemma Terms_cte_fc2 : forall t n t' t'', Cte t <> FC2 n t' t''.
      intros t n t' t'' Hn.
      apply @equal_f_dep with (x:=unit) in Hn.
      inversion Hn.
    Qed.

    Lemma Terms_fc1_fc2 : forall t n t' t'' n', FC1 n t <> FC2 n' t' t''.
      intros t n t' t'' n' Hn.
      apply @equal_f_dep with (x:=unit) in Hn.
      inversion Hn.
    Qed.

    Lemma A0Inv : forall n m, A0 n = A0 m -> n = m.
      intros.
      unfold A0 in H.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H;auto.
    Qed.

    Lemma A1InvN : forall n m t t', A1 n t = A1 m t' -> n = m.
      intros.
      unfold A1 in H.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H;auto.
    Qed.

    Lemma A1InvT : forall n m t t', A1 n t = A1 m t' -> t = t'.
      intros.
      unfold A1 in H.
      extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H;auto.
    Qed.

    Lemma A2InvN : forall n m t1 t1' t2 t2', A2 n t1 t2 = A2 m t1' t2' -> n = m.
      intros.
      unfold A2 in H.
      apply @equal_f_dep with (x:=unit) in H.
      inversion H;auto.
    Qed.

    Lemma A2InvT1 : forall n m t1 t1' t2 t2', A2 n t1 t2 = A2 m t1' t2' -> t1 = t1'.
      intros.
      unfold A2 in H.
      extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H;auto.
    Qed.

    Lemma A2InvT2 : forall n m t1 t1' t2 t2', A2 n t1 t2 = A2 m t1' t2' -> t2 = t2'.
      intros.
      unfold A2 in H.
      extensionality T.
      apply @equal_f_dep with (x:=T) in H.
      inversion H;auto.
    Qed.



  End EqualityFormulas. 
  
  (* Inversion on Hypotheses of the shape F:Lexp = G:Lexp *)
  Ltac LexpSubst :=
    match goal with
    | [H : A0 ?n = A0 ?m  |- _] =>
      assert (n = m) by ( apply A0Inv in H;auto);
      subst
    | [H : A1 ?n ?F = A1 ?m ?F' |- _] =>
      assert (F = F') by ( apply A1InvT in H;auto);
      assert (n = m) by ( apply A1InvN in H;auto);
      subst
    | [H : A2 ?n ?F1 ?F2 = A2 ?m ?F1' ?F2' |- _] =>
      assert (F1 = F1') by ( apply A2InvT1 in H;auto);
      assert (F2 = F2') by ( apply A2InvT2 in H;auto);
      assert (n = m) by ( apply A2InvN in H;auto);
      subst
    | [H : Atom ?F = Atom ?F' |- _] =>
      assert (F = F') by ( apply AtomEq in H;auto);
      subst
    | [H : Perp ?F = Perp ?F' |- _] =>
      assert (F = F') by ( apply PerpEq in H;auto);
      subst  
    | [H : ?F ** ?G = ?F' ** ?G' |- _] =>
      assert (F = F') by ( apply TensorEq1 in H;auto);
      assert (G = G') by ( apply TensorEq2 in H;auto);
      subst; clear H
    | [H : ?F ⊕ ?G = ?F' ⊕ ?G' |- _] =>
      assert (F = F') by ( apply PlusEq1 in H;auto);
      assert (G = G') by ( apply PlusEq2 in H;auto);
      subst; clear H
    | [H : ?F $ ?G = ?F' $ ?G' |- _] =>
      assert (F = F') by ( apply ParEq1 in H;auto);
      assert (G = G') by ( apply ParEq2 in H;auto);
      subst; clear H
    | [H : ?F & ?G = ?F' & ?G' |- _] =>
      assert (F = F') by ( apply WithEq1 in H;auto);
      assert (G = G') by ( apply WithEq2 in H;auto);
      subst; clear H
    | [H : F{ ?F }= F{ ?F'} |- _] =>
      assert (F = F') by ( apply FxEq in H;auto);
      subst
    | [H : E{ ?F }= E{ ?F'} |- _] =>
      assert (F = F') by ( apply ExEq in H;auto);
      subst
    | [H :  ! ?F = ! ?F' |- _] =>
      assert (F = F') by ( apply BangEq in H;auto);
      subst
    | [H :  ? ?F = ? ?F' |- _] =>
      assert (F = F') by ( apply QuestEq in H;auto);
      subst
    end.
  
  (************************************************)
  

  (********************************************)
  (* Measures (weight/complexity) on Formulas *)
  (* For the proof of Cut-elimination  *)
  (********************************************)
  Section Measures.

    Fixpoint lexp_weight (P:lexp unit) : nat :=
      match P with
      | atom X | perp X => 0
      | one | bot | zero | top => 0
      | tensor X Y => 1 + (lexp_weight X) + (lexp_weight Y)
      | par X Y => 1 + (lexp_weight X) + (lexp_weight Y)
      | plus X Y => 1 + (lexp_weight X) + (lexp_weight Y)
      | witH X Y  => 1 + (lexp_weight X) + (lexp_weight Y)
      | bang X => 1 + lexp_weight X
      | quest X  => 1 + lexp_weight X
      | ex FX => 1 + lexp_weight (FX tt)
      | fx FX => 1 + lexp_weight (FX tt)
      end.

    Definition Lexp_weight (P : Lexp) :nat := lexp_weight (P _).

    Hint Unfold Lexp_weight Dual_LExp.

    Theorem WeightDestruct0 : forall F:Lexp, 0%nat = Lexp_weight F ->
                                             (exists A, F = Atom A) \/ (exists A, F = Perp A) \/
                                             F = One \/ F = Bot \/ F = Zero \/ F = Top.
      autounfold.
      intros.
      caseLexp F;firstorder; try(rewrite <- H2 in H; inversion H);
        try(rewrite <- H1 in H; inversion H);
        try(rewrite <- H0 in H; inversion H).
      left;eauto.
      right;left;eauto.
      
    Qed.

    Definition eq_wt F G:= Lexp_weight F = Lexp_weight G.
    
    Lemma wt_refl : forall F, eq_wt F F.
    Proof. unfold eq_wt; auto. Qed.
    
    Lemma wt_symm : forall F G, eq_wt F G -> eq_wt G F.
    Proof. unfold eq_wt; auto. Qed. 
    
    Lemma wt_trans: forall F G T, eq_wt F G -> eq_wt G T -> eq_wt F T.
    Proof. unfold eq_wt; intros; rewrite H, H0; auto. Qed. 
    
    Hint Resolve wt_refl wt_symm wt_trans.
    
    Add Parametric Relation : (Lexp) eq_wt 
        reflexivity proved by wt_refl
        symmetry proved by wt_symm
        transitivity proved by wt_trans as wt_linear.

    Lemma wt_eq : forall F G, F = G -> Lexp_weight F = Lexp_weight G.
      intros. rewrite H. auto.
    Qed.


    Lemma lweight_dual_unit : forall FX:Subs, lexp_weight (FX unit tt) = lexp_weight (dual_LExp (FX unit tt)).
    Proof.
      intros.
      induction (FX unit tt);try(reflexivity);
        try(simpl;try(rewrite IHl);try(rewrite IHl1);try(rewrite IHl2);reflexivity);
        (simpl; generalize (H tt);intro HH; rewrite HH; reflexivity).
    Qed.
    
    Lemma lweight_dual : forall F: Lexp , Lexp_weight F = Lexp_weight (Dual_LExp F).
    Proof.
      intro.
      indLexp F;try (reflexivity);autounfold in *;
        try(simpl; try(rewrite IHHF1);try(rewrite IHHF2);auto);
        rewrite lweight_dual_unit;auto.
    Qed.

    
    Lemma lweight_dual_plus : forall F G, Lexp_weight F + Lexp_weight G = Lexp_weight (Dual_LExp F) + Lexp_weight (Dual_LExp G).
    Proof.
      intros.
      rewrite lweight_dual with (F:=F).
      rewrite lweight_dual with (F:=G).
      auto.
    Qed.
  End Measures.
  

  (*************************************************)
  (** Equality UpTo Atoms *)
  (*************************************************)
  Section EqUpTo.
    Variable T T':Type.
    Inductive xVariantT : term T -> term T'-> Prop :=
    | xvt_var : forall x y, xVariantT (var x) (var y)
    | xvt_cte : forall c, xVariantT (cte c) (cte c)
    | xvt_fc1 : forall n t t', xVariantT t t' -> xVariantT (fc1 n t) (fc1 n t')
    | xvt_fc2 : forall n t1 t2 t1' t2', xVariantT t1 t1' -> xVariantT t2 t2' ->  xVariantT (fc2 n t1 t2) (fc2 n t1' t2').
    
    Inductive xVariantA : aprop T -> aprop T'-> Prop :=
    | xva_eq : forall n, xVariantA (a0 n) (a0 n)
    | xva_a1 : forall n t t', xVariantT t t' -> xVariantA (a1 n t) (a1 n t')
    | xva_a2 : forall n t1 t2 t1' t2', xVariantT t1 t1' -> xVariantT t2 t2' -> xVariantA (a2 n t1 t2) (a2 n t1' t2').

    Inductive EqualUptoAtoms : lexp T -> lexp T' -> Prop :=
    | eq_atom : forall A A', xVariantA A A' ->  EqualUptoAtoms (atom A) (atom A')
    | eq_perp : forall A A', xVariantA A A' -> EqualUptoAtoms (perp A) (perp A')
    | eq_top : EqualUptoAtoms top top
    | eq_bot : EqualUptoAtoms bot bot
    | eq_zero : EqualUptoAtoms zero zero
    | eq_one : EqualUptoAtoms one one
    | eq_tensor : forall F G F' G', EqualUptoAtoms F F' -> EqualUptoAtoms G G' -> EqualUptoAtoms (tensor F G) (tensor F' G')
    | eq_par : forall F G F' G', EqualUptoAtoms F F' -> EqualUptoAtoms G G' -> EqualUptoAtoms (par F G) (par F' G')
    | eq_plus : forall F G F' G', EqualUptoAtoms F F' -> EqualUptoAtoms G G' -> EqualUptoAtoms (plus F G) (plus F' G')
    | eq_with : forall F G F' G', EqualUptoAtoms F F' -> EqualUptoAtoms G G' -> EqualUptoAtoms (witH F G) (witH F' G')
    | eq_bang : forall F F', EqualUptoAtoms F F' -> EqualUptoAtoms (bang F) (bang F')
    | eq_quest : forall F F', EqualUptoAtoms F F' -> EqualUptoAtoms (quest F) (quest F')
    | eq_ex : forall FX FX' ,  (forall t t', EqualUptoAtoms (FX t) (FX' t')) -> EqualUptoAtoms (ex (FX )) (ex (FX'))
    | eq_fx : forall FX FX' , (forall t t', EqualUptoAtoms (FX t) (FX' t')) ->  EqualUptoAtoms (fx (FX )) (fx (FX')).

    Inductive EqualUptoAtomsL : list (lexp T) -> list (lexp T') -> Prop :=
    | eq_nil : EqualUptoAtomsL nil nil
    | eq_cons : forall F F' L L', EqualUptoAtoms F F' -> EqualUptoAtomsL L L' -> EqualUptoAtomsL (F :: L) (F' :: L').
  End EqUpTo. 


  (** We assume that substitutions cannot do pattern-matching nor in the type T nor in the term t *)
  Axiom ax_subs_uptoAtoms  : forall (T T':Type) (t:T) (t' :T') (FX:Subs), EqualUptoAtoms (FX T t) (FX T' t').
  Axiom ax_lexp_uptoAtoms  : forall (T T':Type)  (F :Lexp), EqualUptoAtoms (F T) (F T').

  Theorem  subs_uptoAtomsL  : forall (T T':Type) (t:T) (t' :T') (FX:SubsL),
      EqualUptoAtomsL  (map (fun s => (s T t) )  FX)  (map (fun s => (s T' t') )  FX).
    intros.
    induction FX.
    +simpl;constructor.
    +simpl.
     constructor. apply ax_subs_uptoAtoms.
     apply IHFX.
  Qed.

  (**************************************)
  (** Basic Definition for Focusing *)
  (*************************************)
  Section Polarities. 
    (* Asynchronous formulas *)
    Definition asynchronousF (F :lexp unit) :=
      match F with
      | atom _ | perp _ => false 
      | top => true
      | bot => true
      | zero => false
      | one => false
      | tensor _ _ => false
      | par _ _ => true
      | plus _ _ => false
      | witH _ _ => true
      | bang _ => false
      | quest _ => true
      | ex _ => false
      | fx _ => true
      end.
    Definition AsynchronousF (F:Lexp) : bool := asynchronousF (F _).
    Hint Unfold AsynchronousF.
    
    Inductive Asynchronous : Lexp -> Prop :=
    | aTop :   Asynchronous Top
    | aBot :   Asynchronous Bot
    | aPar :   forall F G, Asynchronous (Par F G)
    | aWith :  forall F G, Asynchronous (With F G)
    | aQuest : forall F  , Asynchronous (Quest F)
    | aForall : forall FX  , Asynchronous (Fx FX).
    
    Hint Constructors Asynchronous.

    Theorem AsyncEqL : forall F:Lexp , Asynchronous F -> AsynchronousF F = true.
    Proof.
      intros.
      inversion H;try(reflexivity).
    Qed.
    
    Theorem AsyncEqR : forall F: Lexp, AsynchronousF F = true -> Asynchronous F.
    Proof.
      intros.
      caseLexp F;auto;
        try( rewrite <- H1 in H); 
        try( rewrite <- H0 in H); 
        try( rewrite <- H2 in H); inversion H.
    Qed.

    Theorem AsyncEq : forall F:Lexp , Asynchronous F <-> AsynchronousF F = true.
      split. apply AsyncEqL. apply AsyncEqR.
    Qed.
    

    (* Negative Atoms *)
    Inductive IsNegativeAtom : Lexp -> Prop :=
    | IsNA0 : forall n, true = isPositive n -> IsNegativeAtom (Perp (A0 n ))
    | IsNA0' : forall n, false = isPositive n -> IsNegativeAtom (Atom (A0 n ))
    | IsNA1 : forall n t, true = isPositive n -> IsNegativeAtom (Perp (A1 n t ))
    | IsNA1' : forall n t, false = isPositive n -> IsNegativeAtom (Atom (A1 n t))
    | IsNA2 : forall n t t', true = isPositive n -> IsNegativeAtom (Perp (A2 n t t'))
    | IsNA2'' : forall n t t', false = isPositive n -> IsNegativeAtom (Atom (A2 n t t')).
    
    Hint Constructors IsNegativeAtom.
    
    (* Positive Atoms *)
    Inductive IsPositiveAtom : Lexp -> Prop :=
    | IsPA0 : forall n, false = isPositive n -> IsPositiveAtom (Perp (A0 n ))
    | IsPA0' : forall n, true = isPositive n -> IsPositiveAtom (Atom (A0 n ))
    | IsPA1 : forall n t, false = isPositive n -> IsPositiveAtom (Perp (A1 n t ))
    | IsPA1' : forall n t, true = isPositive n -> IsPositiveAtom (Atom (A1 n t))
    | IsPA2 : forall n t t', false = isPositive n -> IsPositiveAtom (Perp (A2 n t t'))
    | IsPA2'' : forall n t t', true = isPositive n -> IsPositiveAtom (Atom (A2 n t t')).
    
    Hint Constructors IsPositiveAtom.
    
    (* Complexity of formulas for the focused system *)
    Fixpoint exp_weight (P:lexp unit) : nat :=
      match P with
      | atom _ | perp _ | one | bot | zero | top => 1
      | tensor X Y => 1 + (exp_weight X) + (exp_weight Y)
      | par X Y => 1 + (exp_weight X) + (exp_weight Y)
      | plus X Y => 1 + (exp_weight X) + (exp_weight Y)
      | witH X Y  => 1 + (exp_weight X) + (exp_weight Y)
      | bang X => 1 + exp_weight X
      | quest X  => 1 + exp_weight X
      | ex FX  => 1 + exp_weight (FX tt)
      | fx FX  => 1 + exp_weight (FX tt)
      end.

    Definition Exp_weight (F:Lexp) :nat := exp_weight(F _).
    Hint Unfold Exp_weight.

    Theorem exp_weight0 : forall  F:Lexp , Exp_weight F > 0.
      intros.
      unfold Exp_weight.
      induction F;simpl;omega.
    Qed.

    Theorem exp_weight0F : forall  F:Lexp , Exp_weight F = 0%nat -> False.
    Proof.
      intros.
      generalize(exp_weight0 F).
      intro.
      rewrite H in H0.
      inversion H0.
    Qed.

    (* Complexity of list of formulas  *)
    Fixpoint L_weight (L: list Lexp) : nat :=
      match L with
      | nil => 0
      | H :: L' => (Exp_weight H) + (L_weight L')
      end.
    
    Theorem exp_weight0LF : forall l L, 0%nat = Exp_weight l + L_weight L -> False.
    Proof.
      intros.
      assert(Exp_weight l > 0%nat) by (apply exp_weight0).
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
    
    Lemma FlattenAtom : forall T, forall (A : aprop (term T)), exists A' ,  flatten (atom A) = atom A'.
      intros.
      destruct A3;simpl;eauto.
    Qed.
    
    Lemma FlattenPerp : forall T, forall (A : aprop (term T)), exists A' ,  flatten (perp A) = perp A'.
      intros.
      destruct A3;simpl;eauto.
    Qed.

    Lemma subs_weight_weak:  forall (FX:Subs) x, Exp_weight (Subst FX x) = exp_weight (FX unit tt) .
      intros.
      autounfold. unfold Subst.
      assert (ClosedT x) by apply ax_closedT.
      inversion H. 
      + assert(EqualUptoAtoms (FX (term unit) (Cte C unit)) (FX unit tt)) by apply ax_subs_uptoAtoms.
        induction H1;simpl; try(destruct A3);auto.
      + assert(EqualUptoAtoms (FX (term unit) (FC1 n t1 unit)) (FX unit tt)) by apply ax_subs_uptoAtoms.
        induction H2;simpl; try(destruct A3);auto.
      + assert(EqualUptoAtoms (FX (term unit) (FC2 n t1 t2 unit)) (FX unit tt)) by apply ax_subs_uptoAtoms.
        induction H3;simpl; try(destruct A3);auto.
    Qed.
    
    Theorem subs_weight : forall (FX : Subs) x y, Exp_weight(Subst FX x) = Exp_weight(Subst FX y).
      intros.
      rewrite subs_weight_weak.
      rewrite subs_weight_weak.
      auto.
    Qed.

    Lemma subs_weight_weak':  forall (FX:Subs) x, Lexp_weight (Subst FX x) = (lexp_weight (FX unit tt)) .
      intros.
      unfold Lexp_weight.
      unfold Subst.
      
      assert (ClosedT x) by apply ax_closedT.
      inversion H. 
      + assert(EqualUptoAtoms (FX (term unit) (Cte C unit)) (FX unit tt)) by apply ax_subs_uptoAtoms.
        induction H1;simpl ; try(destruct A3); unfold Lexp_weight; auto.
      + assert(EqualUptoAtoms (FX (term unit) (FC1 n t1 unit)) (FX unit tt)) by apply ax_subs_uptoAtoms.
        induction H2;simpl; try(destruct A3);auto.
      + assert(EqualUptoAtoms (FX (term unit) (FC2 n t1 t2 unit)) (FX unit tt)) by apply ax_subs_uptoAtoms.
        induction H3;simpl; try(destruct A3);auto.
    Qed. 
    
    Theorem subs_weight' : forall (FX : Subs) x y, Lexp_weight(Subst FX x) = Lexp_weight(Subst FX y).
      intros.
      rewrite subs_weight_weak'.
      rewrite subs_weight_weak'.
      auto.
    Qed.
    
    Lemma Flatten_dual : forall T (F: lexp (term T)), flatten F = dual_LExp(flatten ( dual_LExp F)).
      intros.
      induction F;simpl;try(destruct a);try(reflexivity);
        try(simpl;rewrite IHF1;rewrite IHF2; intuition);
        try(simpl;rewrite IHF; intuition).
      
      assert(Hs : (fun x : T => flatten (f (var x))) =  (fun x : T => dual_LExp (flatten (dual_LExp (f (var x))))))
        by (extensionality x; generalize(H (var x));auto);rewrite Hs; reflexivity.
      assert(Hs : (fun x : T => flatten (f (var x))) =  (fun x : T => dual_LExp (flatten (dual_LExp (f (var x))))))
        by (extensionality x; generalize(H (var x));auto);rewrite Hs; reflexivity.
    Qed.

    Theorem SubsDual: forall (FX1 FX2 : Subs) t, (E{ FX1})° = F{ FX2} -> (Subst FX1 t)  = (Subst FX2 t)°.
      intros.
      unfold Dual_LExp in *.
      simpl in *. 
      change  ( (fun T : Type => fx (fun x : T => dual_LExp (FX1 T x))))
      with (F{ fun _ x => dual_LExp(FX1 _ x)}) in H.
      LexpSubst.
      unfold Subst.
      extensionality T.
      eapply Flatten_dual.
    Qed.
    
    Theorem SubsDual': forall (FX1 FX2 : Subs) t, (F{ FX1})° = E{ FX2} -> (Subst FX1 t)  = (Subst FX2 t)°.
      intros.
      unfold Dual_LExp in *.
      simpl in *.
      change  ( (fun T : Type => ex (fun x : T => dual_LExp (FX1 T x))))
      with (E{ fun _ x => dual_LExp(FX1 _ x)}) in H.
      LexpSubst.
      unfold Subst.
      extensionality T.
      eapply Flatten_dual.
    Qed.
    

    
    Theorem WeightEF (FX1 FX2 : Subs) w t : 
      S w = Lexp_weight (E{ FX1}) -> 
      (E{ FX1})° = F{ FX2} -> Lexp_weight (Subst FX2 t) <= w.
    Proof.
      intros Hw Eq.
      assert (Lexp_weight (E{ FX1})° = Lexp_weight (F{ FX2})) by
          solve [rewrite Eq; auto].
      inversion H. inversion Hw.
      rewrite subs_weight_weak'.
      rewrite <- H1. rewrite lweight_dual_unit. auto. 
    Qed.

    Theorem WeightFE (FX1 FX2 : Subs) w t : 
      S w = Lexp_weight (F{ FX1}) -> 
      (F{ FX1})° = E{ FX2} -> Lexp_weight (Subst FX2 t) <= w.
    Proof.
      intros Hw Eq.
      assert (Lexp_weight (F{ FX1})° = Lexp_weight (E{ FX2})) by
          solve [rewrite Eq; auto].
      inversion H. inversion Hw.
      rewrite subs_weight_weak'.
      rewrite <- H1. rewrite lweight_dual_unit. auto. 
    Qed.
    


    (* Lists of positive formulas *)
    Fixpoint LexpPos (l: list Lexp) : Prop :=
      match l with
      | nil => True
      | H :: T' => (AsynchronousF H = false) /\ LexpPos T' 
      end.
    
    Fixpoint BlexpPos (l: list Lexp) : bool :=
      match l with
      | nil => true
      | H :: T => andb (negb (AsynchronousF H)) ( BlexpPos T)
      end.
    
    Theorem PosBool : forall l, BlexpPos l = true <-> LexpPos l.
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

    Inductive LexpPos' : list Lexp -> Prop :=
    | l_nil : LexpPos' []
    | l_sin : forall a, (AsynchronousF a = false) -> LexpPos' [a]
    | l_cos : forall a l, LexpPos' [a] -> LexpPos' l -> LexpPos' (a::l).
    
    Hint Resolve l_nil l_sin l_cos.

    (* Properties of lexpPos *)
    Lemma lexpPosUnion a L: LexpPos [a] -> LexpPos L -> LexpPos ([a] ++ L).
    Proof.
      intros.
      simpl; firstorder.
    Qed.  

    Lemma lexpPosUnion_inv a L: LexpPos ([a] ++ L) -> LexpPos [a] /\ LexpPos L.
    Proof.
      intros.
      simpl in H.
      split; firstorder.
    Qed.

    Lemma lexpPos_lexpPos' M: LexpPos' M <-> LexpPos M.
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

    Lemma AsynchronousFlexpPos : forall  l, AsynchronousF l = false -> LexpPos [l].
    Proof.
      intros.
      constructor;auto.
      constructor.
    Qed.

    Lemma NegPosAtom : forall F, IsNegativeAtom F -> IsPositiveAtom F° .
      intros.
      inversion H;try(constructor);auto.
    Qed.

    
    Inductive release : lexp unit-> Prop :=
    | RelNA1 : forall n, false = isPositive n -> release (perp (a0 n))
    | RelNA1' : forall n, true = isPositive n -> release (atom (a0 n))
    | RelNA2 : forall n t, false = isPositive n -> release (perp (a1 n t))
    | RelNA2' : forall n t, true = isPositive n -> release (atom (a1 n t))
    | RelNA3 : forall n t t', false = isPositive n -> release (perp (a2 n t t'))
    | RelNA3' : forall n t t', true = isPositive n -> release (atom (a2 n t t'))
    | RelTop : release top
    | RelBot : release bot
    | RelPar : forall F G, release (par F G)
    | RelWith : forall F G, release (witH F G)
    | RelQuest : forall F, release (quest F)
    | RelForall : forall FX, release (fx FX).

    Definition Release (F:Lexp) := release (F _).
    Hint Unfold Release.
    Hint Constructors release.

    Lemma IsPositiveAtomRelease: forall F, IsPositiveAtom F -> Release F.
      intros.
      inversion H;
        constructor;auto.
    Qed.

    
    (* Some definitions for the proof of completeness *)
    Inductive NotAsynchronous : Lexp -> Prop :=
    | NAAtomP :  forall v,  NotAsynchronous (Atom v)
    | NAAtomN :  forall v,  NotAsynchronous (Perp v)
    | NAZero :  NotAsynchronous Zero
    | NAOne :  NotAsynchronous One
    | NATensor : forall F G,  NotAsynchronous ( F ** G)
    | NAPlus : forall F G,  NotAsynchronous ( Plus F  G)
    | NABang : forall F,  NotAsynchronous ( ! F )
    | NAExists : forall FX,  NotAsynchronous ( Ex FX ).
    Hint Constructors NotAsynchronous.
    
    Theorem AsynchronousEquiv : forall F, NotAsynchronous F <-> ~ Asynchronous F.
    Proof.
      intros.
      split;intro.
      + inversion H;intro Hc;inversion Hc; apply @equal_f_dep with (x:=unit) in H2; inversion H2.
      + indLexp F;try(constructor);
          match goal with [H : ~Asynchronous ?F |- _]
                          => assert(Asynchronous F) by auto; contradiction end.
    Qed.

    Theorem AsyncEqNeg : forall F:Lexp , ~ Asynchronous F <-> AsynchronousF F = false.
      split;intro H.
      + rewrite <- AsynchronousEquiv in  H.
        inversion H;reflexivity.
      + intro HN.
        apply AsyncEqL in HN.
        rewrite H in HN.
        intuition.
    Qed.

    Inductive posOrNegAtom : lexp unit -> Prop :=
    | PPAtom1 :  forall n,  false = isPositive n -> posOrNegAtom (atom (a0 n))
    | PPAtom1' :  forall n,  true = isPositive n -> posOrNegAtom (perp (a0 n))
    | PPAtom2 :  forall n t,  false = isPositive n -> posOrNegAtom (atom (a1 n t))
    | PPAtom2' :  forall n t,  true = isPositive n -> posOrNegAtom (perp (a1 n t))
    | PPAtom3 :  forall n t t',  false = isPositive n -> posOrNegAtom (atom (a2 n t t'))
    | PPAtom3' :  forall n t t',  true = isPositive n -> posOrNegAtom (perp (a2 n t t'))
    | PPZero :  posOrNegAtom zero
    | PPOne :  posOrNegAtom one
    | PPTensor : forall F G,  posOrNegAtom ( tensor F G)
    | PPPlus : forall F G,  posOrNegAtom ( plus F  G)
    | PPBang : forall F,  posOrNegAtom ( bang F )
    | PPExists : forall FX,  posOrNegAtom ( ex FX).
    Hint Constructors posOrNegAtom.
    Definition PosOrNegAtom (F:Lexp) := posOrNegAtom (F _).
    Hint Unfold PosOrNegAtom.

    (* ~ Asynchronous (Subst FX t)*)
    Inductive posFormula : lexp unit -> Prop :=
    | PFZero :  posFormula zero
    | PFOne :  posFormula one
    | PFTensor : forall F G,  posFormula ( tensor F G)
    | PFPlus : forall F G,  posFormula ( plus F  G)
    | PFBang : forall F,  posFormula ( bang F )
    | PFExists : forall FX,  posFormula ( ex FX).
    Hint Constructors posFormula.
    Definition PosFormula (F:Lexp) := posFormula (F _).
    Hint Unfold PosFormula.

    Lemma PosFormulaPosOrNegAtom : forall F, PosFormula F -> PosOrNegAtom F.
      intros.
      unfold PosOrNegAtom.
      inversion H;constructor.
    Qed.

    Lemma ApropPosNegAtom : forall A: AProp, IsPositiveAtom (Atom A) \/ IsNegativeAtom(Atom A).
      intros.
      assert(HC : ClosedA A3) by apply ax_closedA.
      inversion HC;remember(isPositive n); destruct b;intuition.
      left;constructor;auto.
      right;constructor;auto.
      left;constructor;auto.
      right;constructor;auto.
    Qed.

    Lemma ApropPosNegAtom' : forall A: AProp, IsPositiveAtom (Perp A) \/ IsNegativeAtom(Perp A).
      intros.
      assert(HC : ClosedA A3) by apply ax_closedA.
      inversion HC;remember(isPositive n); destruct b;intuition.
      right;constructor;auto.
      left;constructor;auto.
      right;constructor;auto.
      left;constructor;auto.
    Qed.
    
    Lemma NotAsynchronousPosAtoms : forall F, ~ Asynchronous  F -> PosFormula F \/ IsPositiveAtom F \/ IsNegativeAtom F.
      intros.
      caseLexp F;intuition;try (assert(False) by ( apply H; rewrite<- H0; auto); contradiction);
        try(assert(False) by ( apply H; rewrite<- H2; auto); contradiction);
        try(assert(False) by ( apply H; rewrite<- H1; auto); contradiction);
        try(left;constructor).
      generalize( ApropPosNegAtom  A3); intro HA3. destruct HA3;intuition.
      generalize( ApropPosNegAtom'  A3); intro HA3. destruct HA3;intuition.
    Qed.
    
    Lemma NegPosAtomContradiction: forall F, PosOrNegAtom F ->  IsPositiveAtom F -> False.
      intros.
      inversion H0;
        rewrite <- H2 in H;
        inversion H;
        rewrite <- H4  in H1;
        intuition.
    Qed.
    
    Lemma  IsNegativePosOrNegAtom : forall F,  IsNegativeAtom F -> PosOrNegAtom F.
    Proof. 
      intros.
      inversion H;constructor;auto.
    Qed.
    
    Lemma PosOrNegAtomAsync : forall F, PosOrNegAtom F ->  AsynchronousF F = false.
    Proof.
      intros.
      inversion H;autounfold in *;
        try(rewrite <- H0) ; try(rewrite <- H1) ;simpl;auto.
    Qed.


    Lemma NotAsyncAtom : forall A, ~ Asynchronous (A ⁺).
      intros A3 Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotAsyncAtom' : forall A, ~ Asynchronous (A ⁻).
      intros A3 Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotAsyncOne :  ~ Asynchronous (One).
      intro Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotAsyncZero :  ~ Asynchronous (Zero).
      intro Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotAsyncTensor : forall F G,  ~ Asynchronous (Tensor F G).
      intros F G Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotAsyncPlus : forall F G,  ~ Asynchronous (Plus F G).
      intros F G Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotAsyncBang : forall F ,  ~ Asynchronous (Bang F).
      intros F Hn.
      inversion Hn;auto;LexpContr.
    Qed.
    
    Lemma NotAsyncEx : forall FX ,  ~ Asynchronous (Ex FX).
      intros FX Hn.
      inversion Hn;auto;LexpContr.
    Qed.

    Lemma NotPATop :  ~IsPositiveAtom (Top).
      intros  Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPABot :  ~IsPositiveAtom (Bot).
      intros  Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAOne :  ~IsPositiveAtom (One).
      intros  Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAZero :  ~IsPositiveAtom (Zero).
      intros  Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPATensor : forall F G, ~IsPositiveAtom (Tensor F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAPar : forall F G, ~IsPositiveAtom (Par F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAPlus : forall F G, ~IsPositiveAtom (Plus F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAWith : forall F G, ~IsPositiveAtom (With F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPABang : forall F , ~IsPositiveAtom (Bang F).
      intros F Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAQuest : forall F , ~IsPositiveAtom (Quest F).
      intros F Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAExists : forall FX, ~IsPositiveAtom (Ex FX).
      intros FX Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma NotPAForall : forall FX, ~IsPositiveAtom (Fx FX).
      intros FX Hn.
      inversion Hn;LexpContr.
    Qed.

    Lemma IsNegativeOne :  ~ IsNegativeAtom One.
      intro Hn;inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeBot :  ~ IsNegativeAtom Bot.
      intro Hn;inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeZero :  ~ IsNegativeAtom Zero.
      intro Hn;inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeTop :  ~ IsNegativeAtom Top.
      intro Hn;inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeTensor : forall F G, ~ IsNegativeAtom (Tensor F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativePar : forall F G, ~ IsNegativeAtom (Par F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeWith : forall F G, ~ IsNegativeAtom (With F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativePlus : forall F G, ~ IsNegativeAtom (Plus F G).
      intros F G Hn.
      inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeBang : forall F, ~ IsNegativeAtom (! F).
      intros F Hn.
      inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeQuest : forall F, ~ IsNegativeAtom (? F).
      intros F Hn.
      inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeEx : forall F, ~ IsNegativeAtom (Ex F).
      intros F Hn;inversion Hn;LexpContr.
    Qed.
    Lemma IsNegativeFx : forall F, ~ IsNegativeAtom (Fx F).
      intros F Hn;inversion Hn;LexpContr.
    Qed.

    Lemma NotRelTensor: forall F G, ~ Release (F ** G).
      intros F G Hn; inversion Hn.
    Qed.
    Lemma NotRelPlus: forall F G, ~ Release (F ⊕ G).
      intros F G Hn; inversion Hn.
    Qed.
    Lemma NotRelBang: forall F , ~ Release (! F).
      intros F Hn; inversion Hn.
    Qed.
    Lemma NotRelEx: forall F, ~ Release ( Ex F).
      intros F Hn; inversion Hn.
    Qed.
    Lemma NotRelOne: ~ Release One.
      intros Hn; inversion Hn.
    Qed.
    Lemma NotRelZero: ~ Release Zero.
      intros Hn; inversion Hn.
    Qed.

    Hint Resolve NotRelTensor NotRelPlus NotRelBang NotRelEx NotRelOne NotRelZero NotAsyncAtom NotAsyncAtom'.

    Lemma  IsPositiveAtomNotAssync : forall F,  IsPositiveAtom F -> ~ Asynchronous F.
    Proof.
      intros.
      inversion H;auto.
    Qed.

    Lemma NotAsynchronousPosAtoms' : forall G, ~Asynchronous G -> IsPositiveAtom G \/ (PosFormula G \/ IsNegativeAtom G).
      intros G HG.
      apply NotAsynchronousPosAtoms in HG;tauto.
    Qed.
    
    Lemma PosFNegAtomPorOrNegAtom: forall G,  PosFormula G \/ IsNegativeAtom G -> PosOrNegAtom G.
    Proof.
      intros.
      destruct H.
      inversion H; unfold PosOrNegAtom; rewrite <- H1; auto.
      inversion H; unfold PosOrNegAtom;constructor;auto.
    Qed.
    
    Lemma AsyncRelease: forall F, Asynchronous F -> Release F.
    Proof.
      intros.
      inversion H; constructor.
    Qed.
    
    Lemma AsIsPosRelease: forall F, (Asynchronous F \/ IsPositiveAtom F ) -> Release F.
    Proof.
      intros.
      destruct H;auto using AsyncRelease.
      inversion H;constructor;auto.
    Qed.

    Lemma PositiveNegativeAtom : forall At, IsPositiveAtom (At ⁺) -> IsNegativeAtom (At ⁻).
    Proof.
      intros.
      inversion H; try(LexpSubst);try(LexpContr);try(constructor);auto.
    Qed.
    
    

    
    Lemma PositiveNegativeAtomNeg : forall At, IsPositiveAtom (At ⁺) -> ~ IsPositiveAtom (At ⁻).
    Proof.
      intros.
      inversion H;intro; try(LexpSubst);
        apply PositiveNegativeAtom in H;
        apply IsNegativePosOrNegAtom in H;
        eapply NegPosAtomContradiction;eauto.
    Qed.

    
    Lemma NegativePositiveAtomNeg : forall At, IsNegativeAtom (At ⁺) -> ~ IsPositiveAtom (At ⁺).
    Proof.
      intros.
      inversion H;intro; try(LexpSubst);try(LexpContr);try(constructor);auto;
        apply PositiveNegativeAtom in H2;
        apply IsNegativePosOrNegAtom in H2;
        eapply NegPosAtomContradiction;eauto.
    Qed.

    

    Lemma PositiveNegative : forall A, IsPositiveAtom A -> ~ IsNegativeAtom A.
    Proof.
      intros.

      inversion H;intro; try(LexpSubst);try(LexpContr);try(constructor);auto;
        inversion H2;try(LexpContr);
          try(do 2 LexpSubst); try( rewrite <- H4  in H0); intuition.
    Qed.
    

    Lemma PosFIsNegAAsync : forall G, PosFormula G \/ IsNegativeAtom G -> ~ Asynchronous G.
    Proof.
      intros.
      destruct H.
      caseLexp G ;try(LexpSubst);try(LexpContr);try(constructor);auto; try( rewrite <- H0 in H; inversion H);
        try( rewrite <- H2 in H; inversion H);
        try( rewrite <- H1 in H; inversion H);
        inversion H;intro HA; inversion HA ;LexpContr.
      inversion H;intro HA; inversion HA ;LexpContr.
    Qed.

  End Polarities.

  (* Solves goals when there is an hypothesis IsNegativeAtom(F) and F cannot be a negative atom *)
  Ltac invNegAtom :=
    try(
        match goal with
        | [H: IsNegativeAtom ?F |- _] => assert(~ IsNegativeAtom F)
            by (try(apply IsNegativeOne) ;
                try(apply IsNegativeBot) ;
                try(apply IsNegativeTop) ;
                try(apply IsNegativeZero) ;
                try(apply IsNegativeTensor) ;
                try(apply IsNegativePlus) ;
                try(apply IsNegativeWith) ;
                try(apply IsNegativePar) ;
                try(apply IsNegativeBang) ;
                try(apply IsNegativeQuest) ;
                try(apply IsNegativeEx);
                try(apply IsNegativeFx)
               ) ; contradiction
                     
        end
      ).

  (* Solves goals when there is an hipthesis Release(F) and F cannot be released. *)
  Ltac invRel :=
    try(
        match goal with
        | [H: Release ?F |- _] => assert(~ Release F)
            by (
                try(apply NotRelTensor);
                try(apply NotRelPlus);
                try(apply NotRelBang);
                try(apply NotRelEx);
                try(apply NotRelOne);
                try(apply NotRelZero)
              );contradiction
        end).

End Syntax_LL. 


(*****************************************)
(* Module to be imported for LL Formulas *)
(*****************************************) 
Module FormulasLL (DT : Eqset_dec_pol).
  Module Export Sy := Syntax_LL DT.
  
  Module lexp_eq <: Eqset_dec.
    Definition A := Lexp.
    Definition eqA_dec := FEqDec.
  End lexp_eq.  
  
  Hint Rewrite Neg2pos Ng_involutive.
  Hint Resolve wt_refl wt_symm wt_trans.
  Hint Constructors Asynchronous.
  Hint Resolve l_nil l_sin l_cos.
  Hint Constructors release.
  Hint Constructors NotAsynchronous.
  Hint Constructors posOrNegAtom.

  Declare Module Export MSetList : MultisetList lexp_eq.

  (* Some aditional Properties using multisets of formulas *)
  Lemma LPos1 (L M :list Lexp)  : L =mul= M -> LexpPos L -> LexpPos M.
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

  Instance lexpPos_morph : Proper (meq ==> iff) (LexpPos ).
  Proof.
    intros L M Heq .
    split;intro.
    + eapply LPos1;eauto.
    + apply LPos1 with (L:=M);auto.
  Qed.
  
  Lemma LPos2 : forall M N L, L =mul= M ++ N -> LexpPos L -> LexpPos M.
  Proof.
    induction M;intros;simpl;auto.
    assert (L =mul= M ++ (a::N)) by solve[rewrite H; solve_permutation].
    apply IHM in H1;auto.
    firstorder.
    apply LPos1 in H;auto.
    inversion H;auto.
  Qed.

  Lemma LPos3:  forall M N L, L =mul= M ++ N -> LexpPos L -> LexpPos N .
  Proof.
    intros.
    rewrite union_comm in H.
    eapply LPos2 ;eassumption.
  Qed.

  Lemma LexpPosConc : forall M F, LexpPos M -> ~ Asynchronous F ->  LexpPos (M ++ [F]).
    intros.
    assert(M ++ [F] =mul= [F] ++ M) by solve_permutation.
    rewrite H1.
    constructor;auto.
    apply AsyncEqNeg;auto.
  Qed.

  Lemma LexpPosCons : forall F L, LexpPos (F :: L) -> LexpPos L.
    intros.
    inversion H.
    auto.
  Qed.
  

  Lemma LexpPosOrNegAtomConc : forall M F,  LexpPos M ->  PosOrNegAtom F ->  LexpPos (M ++ [F]).
    intros.
    assert(HS : M ++ [F] =mul= [F] ++ M) by solve_permutation.
    rewrite HS.
    constructor;auto using PosOrNegAtomAsync.
  Qed.
  
End FormulasLL.



