(* =============================================================== *)
(* Minimal Specification of LJ to try to generate it automatically *)
(* This file is underdevelopment *)
(* =============================================================== *)

Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Add LoadPath "../../".
Require Export Permutation.
Require Export LL.SequentCalculi.
Require Export LL.StructuralRules.
Require Export LL.Multisets.
Require Export LL.StrongInduction.

Hint Resolve Max.le_max_r.
Hint Resolve Max.le_max_l.


(* Specifying the Object Logic *)
Module PL.

  (* !SD!: SYNTAX *)
  Inductive LForm :Set :=
  | atom : nat -> LForm (* atomic propositions are named with a natural number *)
  | bot : LForm (* false *)
  | conj : LForm -> LForm -> LForm (* conjunction *)
  .

  (* This theorem is needed in Multisets. I can see some difficulties:
     - It may rely on decidability of other types (e.g., Nat in this case 
     - The cases as conj seems to be solvable automatically (as done below )
   *)
  (* !SD! *)
  Theorem LForm_dec_eq : forall F G : LForm, {F = G} + {F <> G}.
    induction F;destruct G;
      try(right;discriminate); (* case equal *)
      try(match goal with [|- {?X =  ?X } + {?X <> ?X}] => left;auto end); (* case different *)
    try( (* inductive cases *)
        generalize(IHF1 G1);intro;
        generalize(IHF2 G2);intro;
        destruct H;destruct H0;subst;try(right;intro;inversion H;contradiction);auto).
    (* The hard part...relying on decidability of other datatypes *)
    generalize(eq_nat_decide n n0);intro Hn.
    destruct Hn.
    apply eq_nat_is_eq in e;subst;auto.
    right; intro;rewrite eq_nat_is_eq in n1.
    inversion H.
    contradiction.
  Qed.
  
  (* ========================================*)
  (* !SI!: Some definitions in order to define multisets on object level formulas
   * I assume that the object logic (always) uses multisets to represent contexts *)
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
  (* ========================================*)
  
  (* ========================================*)
  (* RULES *)
  (* This should be straightforward from the rules of the system *)
  Reserved Notation " L ';' n '|-P-' F" (at level 80).
  Inductive sq : list LForm -> nat -> LForm -> Prop :=
  | init : forall (L L' :list LForm) a, L =mul= atom a :: L' -> L ; 0 |-P- atom a
  | botL : forall (L L' :list LForm) G , L =mul= bot :: L' -> L ; 0 |-P- G
  | cR : forall L F G n m , L ; n |-P- F -> L ; m |-P- G -> L ; S (max n m) |-P- conj F G
  | cL : forall L G G' F L' n, L =mul= (conj G G') :: L' -> G :: G' :: L' ; n |-P- F -> L ; S n |-P- F
  where "L ; n |-P- F" := (sq L n F).
  (* ========================================*)


  (* !SD!: Exchange *)
  (* This Theorem is needed in one of the cases for Completeness. *)
  (* This theorem also looks difficult to generalize to arbitrary systems *)
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
  Qed.

  (* !SI! *)
  (* Some Multiset stuff that we may later improve *)
  Lemma Contradiction_mset : forall a L,  meq []  (a :: L) -> False.
    intros.
    contradiction_multiset.
  Qed.
  Lemma Contradiction_mset' : forall a L,  meq  (a :: L) [] -> False.
    intros.
    symmetry in H.
    contradiction_multiset.
  Qed.
  
  Definition meqPL := meq.
  
End PL.

Export ListNotations.

Notation " L  '|-P-' n ';' F" := (PL.sq L n F) (at level 80).

Module SLL := SRule PL.F_dec.
Export SLL.


(* Numbers for the predicates *)
Definition rg := 1%nat. (* UP PREDICATE *)
Definition lf := 3. (* DOWN predicate *)
(* Numbers for the functional constructors *)
Definition bt := 0%nat. (* bottom *)
Definition pr := 1%nat. (* atoms / propositions *)
Definition cj := 2%nat. (* conjunction *)

(* ======================================= *)
(* !SD!: Encoding of Rules *)
(* ======================================= *)
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



(* =========================================  *)
(* !SI!: Definition independent of the system *)
(* =========================================  *)
Definition Theory := BLEFT :: INIT :: CRIGHT :: CLEFT :: nil.
Hint Unfold Theory .

Fixpoint encodeTerm (F: PL.LForm) :=
  match F with
  | PL.bot => (Cte PL.bot)
  | PL.atom x => FC1 pr (Cte (PL.atom x))
  | PL.conj x y => FC2 cj (encodeTerm x) (encodeTerm y)
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

(* END OF DEFINITIONS *)
(* ============================================ *)

(* !SD!: Lemmas in this section must be generated. 
 * It seems that all of them are the same and then, easy to generate
 * There are basically 3 lemmas for each connective. The main difference I can see
 * is the distinction between unary and binary constructors. 
 *)
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
End InversionTerm.
(****************************************)


(* Injection of encodeTerm *)
(* !SI! *)
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
(* !SI! *)
Lemma encodeFLEq : forall F G,  encodeFL F = encodeFL G -> F = G.
  intros.
  destruct F;unfold encodeFL in *;LexpSubst;  apply A1InvT in H0;apply encodeTEq in H0;subst;auto.
Qed.


(* Encode Right only produces right atoms *)
(* !SI! *)
Inductive RightAtom: Lexp -> Prop :=
| at_r : forall t, RightAtom ((Atom (A1 rg t))).
Hint Constructors RightAtom.

(* Encode Left only produces left atoms *)
(* !SI! *)
Inductive LeftAtom : Lexp -> Prop :=
| at_l : forall t, LeftAtom ((Atom (A1 lf t))).
Hint Constructors LeftAtom.

(* Encode List only produces left atoms *)
(* !SI! *)
Inductive LeftAtomL: list Lexp -> Prop :=
| lf_nil : LeftAtomL  nil
| lf_cons : forall L F, LeftAtom F -> LeftAtomL L -> LeftAtomL (F :: L) .
Hint Constructors LeftAtomL.

(* !SI! *)
Lemma encodeRightRight : forall F, RightAtom (encodeFR F).
Proof with InvTac.
  intros.
  destruct F;unfold encodeFR ...
Qed.

(* !SI! *)
Lemma encodeLeftLeft : forall F, LeftAtom (encodeFL F).
Proof with InvTac.
  intros.
  destruct F;unfold encodeFL ...
Qed.

(* !SI! *)
Lemma encodeListLeft : forall L, LeftAtomL (encodeList L).
Proof with InvTac.
  intros.
  induction L ...
  constructor ...
  apply encodeLeftLeft.
Qed.

(* !SI! *)
Lemma EncodeFRLFContr : forall F t, encodeFR F <> ((A1 lf t) ⁻)°.
  intros F t HF.
  rewrite AtomNeg in HF.
  
  destruct F;compute in HF;
    match goal with [HF : ?F = ?G |- False ] =>
                    apply @equal_f_dep with (x:=unit) in HF;inversion HF
    end.
Qed.


(* !SI! *)
Lemma EncodeFLRGContr : forall LA t, LeftAtom LA -> LA <> ((A1 rg t) ⁻)°.
  intros.
  inversion H.
  intro HF.
  rewrite AtomNeg in HF.
  apply @equal_f_dep with (x:=unit) in HF.
  inversion HF.
Qed.

(* !SI! *)
Lemma EncodeFLRGContr' : forall F t, encodeFL F <> ((A1 rg t) ⁻)°.
  intros F t HF.
  
  generalize(encodeLeftLeft F); intro HLL.
  apply EncodeFLRGContr with (t:=t) in HLL.
  contradiction.
Qed.

(* !SI! *)
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

(* !SI! *)
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



                                                                                               

(* !SI! *)
Lemma EncSidesCorrect' : forall F L M t t', 
    encodeFR F :: encodeList L =mul= M ++ [((A1 lf t) ⁻)°] ++ [((A1 rg t') ⁻)°] ->
    encodeFR F = ((A1 rg t') ⁻)° /\ encodeList L =mul= M ++ [((A1 lf t) ⁻)°].
  intros.
  MReplaceIn (M ++ [((A1 lf t) ⁻)°] ++ [((A1 rg t') ⁻)°]) ( (M ++ [((A1 lf t) ⁻)°]) ++ [((A1 rg t') ⁻)°])  H.
  apply EncSidesCorrect in H.
  auto.
Qed.

Lemma EncSidesCorrect'' : forall F L M t t', 
    encodeFR F :: encodeList L =mul=  ([((A1 rg t) ⁻)°] ++ [((A1 lf t') ⁻)°]) ++ M ->
    encodeFR F = ((A1 rg t) ⁻)° /\ encodeList L =mul= M ++ [((A1 lf t') ⁻)°].
  intros.
  MReplaceIn (([((A1 rg t) ⁻)°] ++ [((A1 lf t') ⁻)°]) ++ M) (M ++ [((A1 lf t') ⁻)°] ++ [((A1 rg t) ⁻)°]) H.
  apply EncSidesCorrect';auto.
Qed.





                                                                                               


(* !SI! *)
Lemma multisetEncode : forall L L' : list PL.LForm, PL.MSFormulas.meq L L' -> encodeList L =mul= encodeList L'.
Proof.
  intros L L' H.

  apply Permutation_meq.
  apply PL.MSFormulas.Permutation_meq in H.
  apply Permutation_map; auto.
Qed.

(* ============================================= *)
(* !SD!: Easy to generate (one per each rule *)
Lemma IsPBLEFT : ~ IsPositiveAtom BLEFT.
Proof with InvTac.
  auto ...
Qed.
(* !SD!: Easy to generate (one per each rule *)
Lemma IsPINIT : ~ IsPositiveAtom INIT.
Proof with InvTac.
  auto ...
Qed.
(* !SD!: Easy to generate (one per each rule *)
Lemma IsPCLEFT : ~ IsPositiveAtom CLEFT.
Proof with InvTac.
  auto ...
Qed.
(* !SD!: Easy to generate (one per each rule *)
Lemma IsPCRIGHT : ~ IsPositiveAtom CRIGHT.
Proof with InvTac.
  auto ...
Qed.
Hint Resolve IsPINIT IsPCLEFT IsPCRIGHT IsPBLEFT .
(* ============================================= *)

(* !SI! *)
Lemma TermFlattenG: forall (t:Term) (T:Type) ,   flattenT (t (term T)) =  (t T).
  intros.
  assert(ClosedT t) by apply ax_closedT.
  induction H; try(reflexivity).
  simpl. rewrite IHClosedT. auto.
  simpl. rewrite IHClosedT1. rewrite IHClosedT2. auto.
Qed.
(* !SI! *)
Lemma TermFlatten: forall F (T:Type) ,   flattenT (encodeTerm F (term T)) =  (encodeTerm F T).
  intros.
  induction F;auto;
    simpl;
    rewrite IHF1;
    rewrite IHF2;
    auto.
Qed.

(* !SI! *)
Lemma AtomFlatten : forall F G n m,   (fun T : Type => perp (a1 n (fc2 m (flattenT (encodeTerm F (term T))) (encodeTerm G T))))=
                                      Perp (A1 n (FC2 m (encodeTerm F) (encodeTerm G))).
  intros.
  
  extensionality T.
  
  rewrite TermFlatten.
  reflexivity.
Qed.

(* !SI! *)
Lemma AtomFlatten' : forall F G n m,   (fun T : Type => atom (a1 n (fc2 m (flattenT (encodeTerm F (term T))) (encodeTerm G T))))=
                                       Atom (A1 n (FC2 m (encodeTerm F) (encodeTerm G))).
  intros.
  extensionality T.
  rewrite TermFlatten.
  reflexivity.
Qed.

(* !SI! *)
Lemma AtomFlatten'' : forall F  n,   (fun T : Type => atom (a1 n (flattenT (encodeTerm F (term T)))))=
                                     Atom (A1 n (encodeTerm F)).
  intros.
  extensionality T.
  rewrite TermFlatten.
  reflexivity.
Qed. 

(* !SI! *)
Lemma AtomFlatten2 : forall F n, (A1 n (encodeTerm F)) ⁺ = fun T : Type => atom (a1 n (flattenT (encodeTerm F (term T)))).
  intros.
  extensionality T.
  rewrite TermFlatten;auto.
Qed.

(* !SI! *)
Lemma AtomFlatten3 : forall F n, (A1 n (encodeTerm F)) ⁺ = fun T : Type => atom (a1 n  (encodeTerm F T)).
  intros.
  extensionality T.
  reflexivity.
Qed.

(* !SI! *)
Lemma FlattenEncTerm:  forall F G n m,  ( (A1 n (FC2 m (encodeTerm F) (encodeTerm G))) ⁺) =
                                        Dual_LExp (fun T : Type => perp (a1 n (fc2 m (flattenT (encodeTerm F (term T))) (encodeTerm G T)))).
  intros.
  rewrite AtomFlatten.
  reflexivity.
Qed.

(* !SI! *)
Lemma Equiv1 : forall F, (A1 lf (encodeTerm F)) ⁺ = encodeFL F.
  intro;reflexivity.
Qed.
(* !SI! *)
Lemma Equiv2 : forall F, (A1 rg (encodeTerm F)) ⁺ =  encodeFR F.
  intro;reflexivity.
Qed.


(* !SI! *)
Ltac conv := 
  simpl;
  try (rewrite AtomFlatten);
  try (rewrite AtomFlatten');
  try (rewrite <- AtomFlatten3);
  try (rewrite AtomFlatten'');
  try(rewrite <- AtomFlatten2);
  try(rewrite Equiv1);
  try(rewrite Equiv2).


Ltac magic :=
  try(match goal with [ H : PL.MSFormulas.meq ?L ?L' |- _ ] => apply multisetEncode in H ; rewrite H end);
  InvTac; conv ; subst ;simpl; unfold encodeSequent ; 
  try(match goal with [|- _ =mul= _] => unfold Theory ;  try(solve_permutation) ;eauto
                 | [ |-  |-F- _ ; encodeFR ?F :: encodeList ?L; UP [?L'] ] =>
                   MReplace(encodeFR F :: encodeList L) (encodeList L ++[encodeFR F])
      end ).
Ltac tri_store' :=
  match goal with 
    [ |- |-F- _ ; ?L ; UP (?F :: ?L')]
    => apply tri_store;magic ;MReplace (L ++ [F]) ( [F] ++ L)
  end.

  
(* !SD!: *)
(* We need to analyze this one. The proof looks like the paper proof... however,
 * some (Coq) bureaucracy is required. Some automation may work *)
Theorem Soundness: forall L F n, L  |-P- n ; F -> ( encodeSequent L F ).
Proof with magic .  
  intros L F n HD.
  dependent induction n generalizing L F using strongind; inversion HD ...
  + (* case init *)
    eapply tri_dec2 with (F:= INIT) ...
    eapply tri_ex with (t:= (Cte (PL.atom a))) ...
    eapply tri_tensor with (N:= [A1 rg (FC1 pr (Cte (PL.atom a))) ⁺ ; (A1 lf (FC1 pr (Cte (PL.atom a)))) ⁺])
                             (M:= encodeList L') ...
    eapply tri_tensor with (N:=[(A1 rg (FC1 pr (Cte (PL.atom a)))) ⁺])
                             (M:= [(A1 lf (FC1 pr (Cte (PL.atom a)))) ⁺]) ...
    apply Init1 ...
    apply Init1 ...
  +  (* case bottom *)
    eapply tri_dec2 with (F:= BLEFT) ...
    eapply tri_tensor with (N:= [(A1 lf (Cte PL.bot)) ⁺] ) (M:=  (A1 rg (encodeTerm F)) ⁺ :: encodeList L') ...
    apply Init1 ...
  + (* Case Conjunction Right *)
      eapply tri_dec2 with (F:= CRIGHT) ...
      eapply tri_ex with (t:= encodeTerm F0) ...
      eapply tri_ex with (t:= encodeTerm G) ...
      eapply tri_tensor with (N:= [(A1 rg (FC2 cj (encodeTerm F0)  (encodeTerm G))) ⁺])
                               (M:= encodeList L) ...
      apply Init1 ...
      apply tri_rel ...
      apply tri_with ...
      (* Branch F *)
      tri_store'.
      apply H in H1  ... (* using inductive hypothesis *)
      (* Branch G *)
      tri_store'.
      apply H in H3  ... (* using inductive hypothesis *)
  + (* Conjunction Left *)
    eapply tri_dec2 with  (F:= CLEFT) ... 
    eapply tri_ex with (t:= encodeTerm G) ...
    eapply tri_ex with (t:= encodeTerm G') ...
    eapply tri_tensor with (N:= [encodeFL (PL.conj G G')])
                             (M:=  (A1 rg (encodeTerm F)) ⁺ :: encodeList (L')) ...
    apply Init1 ...
    apply tri_rel ...
    apply tri_par ...
    tri_store'.
    tri_store'.
    MReplace([encodeFL G'] ++ [encodeFL G] ++ encodeList L' ++ [encodeFR F])
            ([encodeFR F] ++ [encodeFL G] ++ [encodeFL G'] ++ encodeList L').
    apply H in H3 ... (* using inductive hypothesis *)
Qed.

(***********************)


(* !SI! *)
Lemma AtomsTheoryFalse : forall A B, Theory =mul= Atom A :: B -> False.
Proof with InvTac. 
  intros.
  unfold Theory in H.
  multisetContr... 
Qed.

(* !SI! *)
Lemma AtomsTheoryFalse' : forall A B, Theory =mul= Perp A :: B -> False.
Proof with InvTac. 
  intros.
  unfold Theory in H.
  multisetContr... 
Qed.

(* !SI! *)
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

(* !SI! *)
Lemma LeftRightAtom :  forall F t, encodeFR F = (A1 rg t) ⁺ -> encodeFL F = (A1 lf t) ⁺.
  intros.
  destruct F; unfold encodeFR in H; LexpSubst;unfold encodeFL;
    apply A1InvT in H0;rewrite H0;reflexivity.
Qed.

(* !SI! *)
Lemma RightLeftAtom :  forall F t, encodeFL F = (A1 lf t) ⁺ -> encodeFR F = (A1 rg t) ⁺.
  intros.
  destruct F; unfold encodeFL in H ; LexpSubst;unfold encodeFR;
    apply A1InvT in H0;rewrite H0;reflexivity.
Qed.

(* !SI! *)
Lemma encodeListIN : forall L F M, encodeList L =mul= [encodeFL F] ++ M -> In F L.
Proof with InvTac.
  induction L; simpl in *;intros ...
  apply DestructMSet in H.

  (*!! Multiset reasoning on H *)
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

(* !SI! *)
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

(* !SI! *)
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

(* !SI! *)
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

(* !SI! *)
Lemma encodeListFRIN : forall F G L M, encodeFR G :: encodeList L =mul= M ++ [encodeFL F] -> In F L.
  intros.
  generalize( NotEqFRFL F G); intro HFG.
  rewrite union_comm in H; simpl in H.
  apply multFalse in H.
  inversion H; [contradiction|]. (*!! from HFG and H *)
  apply EncodeListMembers;auto.
Qed.

(* !SI! *)
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

(* !SI! *)
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

(* !SI! *)
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

(* !SD!: This lemma is concerned with the "shape" of formulas containing Conjunction (in the 
 * object logic). Similar lemmas need to be generated for each connective 
 * It also looks difficult to generate 
*)
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


Lemma inv_ex_aux B M FX :  |-F- B; M ;  DW (E{ FX }) ->  exists t, |-F- B; M ;  DW (Subst FX t) .
Proof with magic.
  intros.
  inversion H ...
  exists t ...
Qed.

Ltac inv_ex H :=
    apply inv_ex_aux in H;  destruct H as [t  H]; unfold Subst in H; simpl in H.

Lemma inv_tensor_aux B M F G : |-F- B; M ; DW (F ** G) ->
                                           exists M1 M2,  M =mul= M1 ++ M2 /\
                                                          |-F- B ; M1 ; DW (F ) /\
                                                                        |-F- B ; M2 ; DW (G ) .
                                                                        
Proof with magic.
  intros.
  inversion H ...
  eexists;eauto.
Qed.

Ltac inv_tensor H :=
  let M1 := fresh "M1" in
  let M2 := fresh "M2" in
  let HM1M2 := fresh "HM1M2" in
  let HF := fresh "HF" in
  let HG := fresh "HG" in encodeFR F :: encodeList L =mul=
  apply inv_tensor_aux in H;  destruct H as [M1 [M2 [HM1M2 [HF HG]]]].


Lemma InvINIT : forall L F, |-F- Theory ;(encodeFR F) :: encodeList L ; DW(INIT) -> exists L' a, PL.meqPL L (F:: L') /\ F = PL.atom a.
Proof with magic. 
  intros.
  unfold INIT in H.
  (* first the exists *)
  inv_ex H.
  (* now the tensor *)
  inv_tensor H.
 
  (* now the tensor in HF *)
  inv_tensor HF.
  (* HF0 and HG0 must finish *)
  apply InvI1 in HF0 ...
  apply InvI1 in HG0 ...

  (* Deducing facts *)
  rewrite HM1M0 in HM1M2;clear HM1M0.
  apply EncSidesCorrect'' in HM1M2.
  destruct HM1M2 as [HM1 HM2].
  rewrite AtomNeg in *.
  assert(Hat: exists atom, F = PL.atom atom) by 
      (unfold encodeFR in HM1 ;LexpSubst;
       LexpSubst;
       apply InvEncTermAt in H0;auto).
  destruct Hat as [a Hat];subst.
  generalize( LeftRightAtom (PL.atom a) ( (fun T : Type => fc1 pr (t T))) HM1); intros HL.
  rewrite <- HL in HM2.
  rewrite union_comm in HM2.
  apply  encodeListIN in HM2.
  rewrite  PL.MSFormulas.In_to_in in HM2.
  apply PL.MSFormulas.member_then_meq in HM2.
  destruct HM2.
  eexists;eexists;split ...
  apply H.
Qed.
  
(* !SD! *)
(* Inversion of Bottom Left *)
(* Same as the previous one *)
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

(* !SD! *)
(* Inversion of Conjunction Right *)
(* The number of sucessors (S) used depends on the number of rules that need to be applied. This number should be easy to extact from the shape of the bipole *)

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



(* !SD! Same as the previous one *)
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
             encodeFR F :: encodeFL G :: encodeFL G' :: encodeList L').
  solve_permutation.
  
  rewrite HM in H16;clear HM.
  assumption.
  

  (* cannot be from B *)
  apply AtomsTheoryFalse in H7. contradiction.
  (* cannot be a release *)
  inversion H3;subst.
  unfold lf in H7. simpl in H7. intuition.
Qed.


(* !SD! *)
(* From the previous lemmas, this one should be easy to generate (some automation is needed).  *)

Lemma Theory_formulas: forall F B, Theory =mul= F :: B ->
                                   F = BLEFT \/ F = INIT \/ 
                                   F =  CRIGHT \/ F =  CLEFT.
  intros.
  unfold Theory in H.
       assert (In F [BLEFT; INIT; CRIGHT; CLEFT]).
       apply In_to_in.
       rewrite H; auto.
       repeat (try ( destruct H0; eauto)).
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
  + (* Inductive case *)
    unfold Theory in H.
    inversion H0;subst.
    ++ (* The formula was taken from the context M *)
      (* This is inconsistent by Lemma encodePositive *)
      generalize( encodePositive L F);intro HPos.
      inversion HPos;subst.
      assert(encodeFR F = F0 \/ In F0 (encodeList L)). 
      eapply DestructMSet'; eauto.
      destruct H1;subst.
      contradiction.
      assert(IsPositiveAtom F0) by( eapply PositiveIn;eauto).
      contradiction.
      
    ++ (* the formula was taken from the Theory *)
      generalize(Theory_formulas F0 B' H3); intro HCase .


       
       destruct HCase  as [HCase | [HCase |  [HCase | HCase]]];subst.
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
Qed.

