(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Focused System Meta-theory
In this file we prove several invertibility lemmas for the focused system. 
 *)


(* Add LoadPath "../" .  *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export LL.SequentCalculiBasicTheory.
Require Import LL.Eqset.

Set Implicit Arguments.


Module FLLMetaTheory (DT : Eqset_dec_pol).
  
  Module Export Sys :=  SqBasic DT.
  Ltac EquivPosCase H IH m L Hinv :=
    match goal with
      [_ : AsynchronousF _ = false |- _] =>
      
      apply IH  with(m:=L_weight L) in Hinv;auto  using le_plus_r;
      simpl;eapply tri_store;auto
    end.

  Hint Rewrite Neg2pos Ng_involutive.
  Hint Constructors Asynchronous.
  Hint Constructors IsNegativeAtom.
  Hint Resolve l_nil l_sin l_cos.
  Hint Unfold Lexp_weight Dual_LExp.
  (*Hint Constructors Release. *)
  Hint Constructors NotAsynchronous.
  Hint Resolve wt_refl wt_symm wt_trans.
  (* Hint Constructors PosOrPosAtom. *)
  (*Hint Constructors NotPosOrPosAtom.
  Hint Resolve exp_weight_inv. *)
  Hint Unfold Exp_weight.

  Theorem EquivAuxBot : forall B  L L' M ,  |-F- B ; M ; UP (L ++ L') -> |-F- B ; M ;  UP (L ++ [Bot] ++ L').
  Proof with solveF.
    intros.
    remember (L_weight L) as w.
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .
    induction w as [| w' IH] using strongind ; intros M B L' L H Hw  ;  destruct L as [|l] ...
    
    + simpl in Hw. (* Heqw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction.
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl;simpl in H;inversion Hw'; inversion H;subst;solveF;
        try(
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := (apply tri_store;solveF; apply IH with (m:= L_weight  L);solveF;try omega ) in
                            match l with
                            | Perp _ => solve_tac1
                            | Atom _ => solve_tac1
                            | 1   => solve_tac1
                            | 0   => solve_tac1
                            | _ ** _ => solve_tac1
                            | _ ⊕ _ => solve_tac1
                            | ! _  => solve_tac1
                            | E{ _ }   => solve_tac1
                            | Bot => apply tri_bot;apply IH with (m:= L_weight  L);solveF;try(omega)
                            | ? _ => apply tri_quest;apply IH with (m:= L_weight  L);solveF;try(omega)
                            end
            end ) .
      ++ (* par *)
        inversionF H ...
        apply IH  with (L:= F :: G :: L) (m:= (Exp_weight  F) + (Exp_weight G) + L_weight L) in H6 ...  omega.
      ++(* with *)
        inversion H...
        apply IH with (L:= F :: L) (m:= (Exp_weight  F) + L_weight  L) in H7;autounfold;try(omega) ...
        apply IH with (L:= G :: L) (m:= (Exp_weight  G) + L_weight  L) in H8;autounfold;try(omega) ...
      ++ (* forall *)
        inversion H...
        simpl; eapply tri_fx;auto; intro x. eapply IH with (L:=Subst FX x  :: L) ...
        rewrite <- subs_weight_weak with (x:=x).  omega.
  Qed.
  
  
  Theorem EquivAuxWith : forall B  L L' M F G ,
      |-F- B ; M ; UP (L ++ [F] ++ L') ->
                   |-F- B ; M ; UP (L ++ [G] ++ L') ->
                                |-F- B ; M ;  UP (L ++ [F & G] ++ L').
  Proof with solveF .
    intros.
    remember (L_weight  L) as w.
    generalize dependent L .
    generalize dependent L' . 
    generalize dependent B .
    generalize dependent M . 
    generalize dependent w .  
    induction w as [| w' IH] using strongind  ; intros  M B L' L H H' Hw  ;  destruct L as [|l] ...  
    + simpl in Hw. (* Heqw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction.  
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl;simpl in H;inversion Hw' ;inversionF H;solveF;subst;
        try(
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := (inversionF H'; apply tri_store;solveF; apply IH with (m:= L_weight  L);auto;try omega ) in
                            match l with
                            | 1   => solve_tac1
                            | 0   => solve_tac1
                            | _ ** _ => solve_tac1
                            | _ ⊕ _ => solve_tac1
                            | ! _  => solve_tac1
                            | E{ _ }   => solve_tac1
                            | Atom _ => solve_tac1
                            | Perp _ => solve_tac1
                            | Bot => inversion H';solveF;subst; apply tri_bot; apply IH with (m:= L_weight  L);auto
                            end end ) .
      ++ (* par *)
        inversion H;solveF;inversion H';solveF;subst; apply tri_par ...
        eapply IH with (L:= F0 :: G0 :: L) (m:= Exp_weight(F0) + Exp_weight(G0) +  L_weight L) ...
        omega. 
      ++ (* with *)
        inversion H ...
        inversion H' ...
        apply tri_with .
        eapply IH with (L:= F0 :: L) (m:= Exp_weight(F0) + L_weight L) ...
        autounfold ; omega.
        eapply IH with (L:= G0 :: L) (m:= Exp_weight(G0) + L_weight L) ...
        autounfold ; omega.
      ++  (* quest *)
        inversion H ...
        inversion H';subst ...
        apply tri_quest.
        eapply IH with   (m:= L_weight L) ...
        omega.
      ++ (* forall  *)
        inversion H ...
        inversion H' ...
        assert(forall x, |-F- B; M; UP (((Subst FX x) ::L) ++ [F & G] ++ L')) as Hp.
        intro.
        generalize(H4 x);intros; generalize(H5 x);intros.
        eapply IH with (m:=  Exp_weight  (Subst FX x) + L_weight  L ) ...
        rewrite <- subs_weight_weak with (x:=x).  omega ...
        apply tri_fx ...
  Qed.



  Theorem EquivAuxPar : forall B  L L' M F G  n,  n |-F- B ; M ; UP (L ++ [F ; G] ++ L') -> |-F- B ; M ;  UP (L ++ [F $ G] ++ L').
  Proof with solveF .
    intros.
    remember (L_weight  L) as w.
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent n .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind ; intros n M B L' L H Hw  ;  destruct L as [|l] ...
    + simpl. simpl in H.
      eapply tri_par;auto.
      eapply AdequacyTri1;eauto.
    + simpl in Hw. (* Heqw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction.
    + simpl in Hw. inversion Hw.
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;inversion Hw' ;inversionF H;solveF;
        try(
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := apply tri_store;solveF; eapply IH  with (m:=  L_weight L) ;eauto;try omega in
                                                  match l with
                                                  | 1   => solve_tac1
                                                  | 0   => solve_tac1
                                                  | _ ** _ => solve_tac1
                                                  | _ ⊕ _ => solve_tac1
                                                  | ! _  => solve_tac1
                                                  | E{ _ }   => solve_tac1
                                                  | Atom _ => solve_tac1
                                                  | Perp _ => solve_tac1
                                                  | Bot => apply tri_bot ; eapply IH  with (m:=  L_weight L);eauto
                                                  | Par _ _ => apply tri_par ;
                                                               eapply IH  with (L:= F0 :: G0 :: L) (m:= Exp_weight F0 + Exp_weight G0 +  L_weight L);eauto;simpl;omega
                                                  | ? _ => apply tri_quest; eapply IH  with (m:=  L_weight L);eauto; omega
                                                  end end ) .
      ++ (* with *)
        apply IH  with (L:= F0 :: L) (m:=  Exp_weight F0 + L_weight L) in H8;autounfold;try(omega);auto.
        apply IH  with (L:= G0 :: L) (m:=  Exp_weight G0 + L_weight L) in H9;autounfold;try(omega);auto.
      ++ (* forall *)
        assert(forall x, |-F- B; M; UP (((Subst FX x) ::L) ++ [F $ G] ++ L')) as Hp.
        intro.
        generalize(H5 x);intros.
        eapply IH with (m:=  exp_weight(FX unit tt) + L_weight L ) ;eauto.
        simpl.
        rewrite <- subs_weight_weak with (x:=x). auto.
        simpl. eapply tri_fx;auto;intro.
  Qed.

  Hint Resolve AsyncEqNeg.
  Theorem EquivAuxSync : forall B  L L' M  F ,  ~ Asynchronous F ->  |-F- B ; M ++ [F] ; UP (L ++ L') -> |-F- B ; M ;  UP (L ++ [F] ++ L').
  Proof with solveF .
    intros.
    remember (L_weight  L) as w.
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .  
    
    induction w as [| w' IH] using strongind; intros   M   B  L'  L  H1 Hw; destruct L as [|l] ...
    + simpl in Hw. (* Hw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction. 
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;inversion Hw';inversionF H1;subst;solveF;
        
        try(
            match goal with
              [ H : |-F- _; (_ ++ [?F]) ++ [?G]; UP (?L ++ ?L') |- |-F- _ ; _ ; UP ( ?G :: ?L  ++ ?F :: ?L')] =>
              assert (Hch:  (M ++ [F]) ++ [G] =mul=  (M ++ [G]) ++ [F]) by solve_permutation;
              rewrite Hch in H;
              apply IH  with (m:=  L_weight L) in H;auto using le_plus_r
            end).
      ++ (* bot *)
        apply tri_bot.
        apply IH    with (m:=  L_weight L);auto.
      ++ (* PAR *)
        apply IH  with (L:= F0 :: G :: L) (m:= Exp_weight F0 + Exp_weight G +  L_weight L) in H7;try(simpl; omega);auto.
      ++ (* WITH *)
        apply IH  with (L:= F0 :: L) (m:= Exp_weight F0 + L_weight L) in H8;try(autounfold;simpl; omega);auto.
        apply IH  with (L:= G :: L) (m:= Exp_weight G + L_weight L) in H9;try(autounfold;simpl; omega);auto.
      ++ (* quest *)
        apply IH  with  (m:= L_weight L) in H6;try(simpl; omega);auto.
      ++ (* forall *)
        assert(forall x, |-F- B; M; UP (((Subst FX x) ::L) ++ [F] ++ L')) as Hp.
        intro.
        generalize(H5 x);intros.
        eapply IH with (m:=  exp_weight(FX unit tt) + L_weight L ) ;eauto.
        rewrite <- subs_weight_weak with (x:=x). auto.
        eapply tri_fx;auto. 
  Qed.
  
  Theorem EquivAuxQuest : forall B  L L' M  n F,  n |-F- B ++ [F] ; M ; UP (L ++ L') ->  |-F- B ; M ;  UP (L ++ [? F] ++ L').
  Proof with solveF .
    intros.
    remember (L_weight L) as w.
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent n .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind ; intros n M B L' L H Hw  ;  destruct L as [|l] ...
    + simpl. simpl in H.
      eapply tri_quest;auto.
      eapply AdequacyTri1;eauto.
    + simpl in Hw. (* Heqw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction.
    + simpl in Hw. inversion Hw.
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl in *;inversion Hw';inversionF H;solveF;
        try(
            match goal with
              [ Hx : _ |-F- _ ++ [?F]; _ ++ [_]; UP (?L ++ ?L') |- _] =>
              apply IH  with (m:=  L_weight L) in Hx;auto using le_plus_r
            end).
      ++ (* bot *)
        apply tri_bot.
        apply IH  with (m:=  L_weight L) in H5;auto using le_plus_r.
      ++ (* par *)
        apply IH  with (L:=F0 :: G :: L)  (m:=  Exp_weight F0 + Exp_weight G + L_weight L) in H7;auto using le_plus_r.
        simpl. omega.
      ++ (* with *)
        apply IH  with (L:=F0 :: L)  (m:=  Exp_weight F0 + L_weight L) in H8;auto;try(autounfold;simpl;omega).
        apply IH  with (L:=G :: L)  (m:=  Exp_weight G + L_weight L) in H9;auto;try(autounfold;simpl;omega).
      ++ (* quest *)
        apply tri_quest.
        eapply IH  with   (m:=  L_weight L);auto;try(autounfold;simpl;omega).
        MReplace ( (B ++ [F0]) ++ [F]) ((B ++ [F]) ++ [F0]) ...
        eauto.
      ++ (* FORALL *)
        assert(forall x, |-F- B ; M; UP (((Subst FX x) ::L) ++ [? F] ++ L')) as Hp.
        intro.
        generalize(H5 x);intros.
        eapply IH with (m:=  exp_weight(FX unit tt) + L_weight L ) ;simpl;eauto.
        rewrite <- subs_weight_weak with (x:=x). auto.
        eapply tri_fx;auto.
  Qed.


  Theorem EquivAuxTop : forall B  L L' M ,  |-F- B ; M ;  UP (L ++ [Top] ++ L').
  Proof with solveF .
    intros.
    remember (L_weight  L) as w.
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind;  intros M B L' L Hw  ;  destruct L as [|l] ...
    + simpl in Hw. (* Heqw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction.
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl in *;inversion Hw'; solveF;
        try(apply tri_store;solveF;auto  ; apply IH  with (m:=  L_weight L);try(omega);auto).
      ++ (* bot *)
        apply tri_bot.
        apply IH  with (m:=  L_weight L);try(omega);auto.
      ++ (*  PAR *)
        apply tri_par. 
        eapply IH  with  (L:= F :: G :: L) (m:= Exp_weight F + Exp_weight G + L_weight L);
          auto; try(rewrite H2);simpl;autounfold;try(omega).
      ++ (* with *)
        apply tri_with.
        eapply IH  with  (L:= F :: L) (m:= Exp_weight F + L_weight L);
          auto; try(rewrite H2);simpl;autounfold;try(omega).
        eapply IH  with  (L:= G :: L) (m:= Exp_weight G + L_weight L);
          auto; try(rewrite H2);simpl;autounfold;try(omega).
      ++ (* quest *)
        apply tri_quest.
        apply IH  with (m:=  L_weight L);try(omega);auto.
      ++ (* forall *)
        apply tri_fx.
        intro.
        apply IH with (L:= Subst FX x :: L) (m:= exp_weight  (FX unit tt) + L_weight L);simpl; try( rewrite Hw');auto.
        rewrite <- subs_weight_weak with (x:=x). auto.
  Qed.  
  
  Theorem EquivAuxForAll : forall B  L L' M   FX, (forall x,  |-F- B ; M ; UP (L ++ [Subst FX x]++ L')) ->  |-F- B ; M ;  UP (L ++ [F{FX}] ++ L'). 
  Proof with solveF .  
    intros.
    remember (L_weight  L) as w.
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .   
    
    induction w as [| w' IH] using strongind ; intros M B L' L H Hw ;  destruct L as [|l] ...
    + simpl in Hw. (* Heqw is inconsisten *)
      apply exp_weight0LF in Hw. contradiction.  
    + caseLexp l ; inversion Hw as [Hw'];solveF; 
        try( 
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := assert(Hp: forall x,  |-F- B; M ++ [l]; UP (L ++ [Subst FX x] ++ L')) by
                                    (intro;generalize (H x); intro Hp'; try(inversionF Hp';solveF); 
                                     apply IH  with (m:= L_weight  L) in Hp;auto);
                                              apply tri_store;subst;solveF; simpl in Hw';inversion Hw';
                                                                                     apply IH  with (m:= L_weight  L) in Hp;try(omega);auto in
                                                                                         match l with
                                                                                         | Atom _ => solve_tac1
                                                                                         | Perp _ => solve_tac1
                                                                                         | 1   => solve_tac1
                                                                                         | 0   => solve_tac1
                                                                                         | Plus _ _ => solve_tac1
                                                                                         | _ ** _ => solve_tac1
                                                                                         | ! _  => solve_tac1
                                                                                         | E{ _ }  => solve_tac1
                                                                                         end
            end) . 
      ++ (* bot *) 
        assert(Hp: forall x,  |-F- B; M; UP (L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp'; inversion Hp'; subst ...
        apply IH  with (m:= L_weight  L) in Hp; try(apply tri_bot);try(omega);auto.
      ++ (* par *)
        assert(Hp: forall x,  |-F- B; M; UP ( F :: G :: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp'; inversion Hp'; subst ... auto.
        apply IH  with (L:= F :: G :: L) (m:= Exp_weight  F + Exp_weight G + L_weight  L) in Hp ...
        subst. simpl in Hw';inversion Hw';auto ...
        omega.
      ++ (* With *)
        assert(Hp1: forall x,  |-F- B; M; UP ( F:: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp1'; inversion Hp1'; subst ... auto.
        assert(Hp2: forall x,  |-F- B; M; UP ( G:: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp2'; inversion Hp2'; subst ... auto.
        inversion Hw'. subst. 
        apply IH  with (L:= F :: L) (m:= Exp_weight F + L_weight L) in Hp1;try(omega); subst;autounfold;simpl;try(omega); auto.
        apply IH  with (L:= G :: L) (m:= Exp_weight G + L_weight L) in Hp2;try(omega); subst;autounfold;simpl;try(omega); auto.
      ++  (* quest *)
        assert(Hp: forall x,  |-F- B ++ [F]; M; UP (L ++ [Subst FX x] ++ L')) .
        intro; generalize (H x); intro Hp'; inversion Hp'; subst;LexpContr;intuition ... auto.
        apply IH  with (m:= L_weight  L) in Hp;auto. 
        subst;inversion Hw';omega .
      ++ (* forall *)
        subst.
        assert(Hp: forall x x', |-F- B; M; UP ((Subst FX0 x') :: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp'; inversion Hp'; subst ... auto.
        apply tri_fx;intro.
        apply IH with (L:= Subst FX0 x :: L) (m:= Exp_weight  (Subst FX0  x) + L_weight  L) ...
        simpl in Hw';inversion Hw'. autounfold.
        rewrite <- subs_weight_weak with (x:=x). auto.
  Qed.

  Theorem EquivUpArrow : forall B L L' M n, n |-F- B ; M ; UP L -> L =mul= L' ->|-F- B ; M ;  UP L'.
  Proof with solveF .
    intros.
    remember (L_weight L) as w.
    generalize dependent n .
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind;  intros ;  destruct L as [|l] ...
    + assert (L'= []) by( apply emp_mult;auto) ...
      subst.
      eapply AdequacyTri1;eauto.
    + inversion Heqw.
      generalize(exp_weight0  l);intros.
      omega.
    + assert (L'= []) by( apply emp_mult;auto).
      subst.
      eapply AdequacyTri1;eauto.
    + destruct L'.
      (* H0 is inconsisten *) 
      apply DestructMulFalse in H0. contradiction.
      apply DestructMSet2 in H0 as Heq.
      destruct Heq as [Heq | Heq].
      ++ (* case 1 *)
        destruct Heq;subst.
        inversionF H;subst;try(simpl in Heqw; inversion Heqw; subst;simpl;try(omega)).
        +++ (* bottom *)
          eapply IH with (L' :=L') in H6;auto.
        +++ (* par *)
          eapply IH with (L' := F::G::L') in H6;auto.
          simpl. autounfold. omega.
        +++ (* with *)
          eapply IH with (m:= L_weight (F::L)) (L:= F ::L) (L' := F :: L') in H7;auto.
          eapply IH with (m:= L_weight (G::L)) (L := G :: L) (L' := G :: L') in H8;auto.
          simpl. autounfold. omega.
          simpl. autounfold. omega.
        +++  (* quest *)
          eapply IH with (m:= L_weight L) (L' :=L') in H6;auto. 
          omega.
        +++  (* store *)
          eapply IH with (m:= L_weight L) (L' :=L') in H8;auto.
          generalize(exp_weight0  a);intro.
          omega.
        +++ (* forall *)
          eapply tri_fx;auto.
          intro. 
          generalize (H6 x);intro.
          eapply IH with (m:= Exp_weight (Subst FX x) + L_weight L) (L' := Subst FX x :: L') in H1;auto.
          simpl. rewrite <- subs_weight_weak with (x:=x). auto.
      ++ (* case 2 *)
        destruct Heq as [L1 [L2 [L1' [L2' Heq]]]].
        destruct Heq as [Heq [Heq1 Heq2]];subst.
        inversion H;subst. 
        +++ (* top *)
          eapply EquivAuxTop with (L:= a :: L1').
        +++ (* bottom *)
          eapply IH with (m:= L_weight(L1 ++ a :: L2))(L:=L1 ++ a :: L2) (L' := [a] ++ L1' ++ L2') in H5 ...
          simpl in H5. 
          eapply AdequacyTri2 in H5. destruct H5.
          apply EquivAuxBot with (L:= a :: L1') ...
          apply AdequacyTri1 in H1 ... 
          simpl in Heqw. inversion Heqw. auto ...
        +++ (* par *)
          eapply IH with (m:= L_weight(F :: G :: L1 ++ a :: L2))
                         (L:=F :: G :: L1 ++ a :: L2)
                         (L' := [a] ++ L1' ++ [F ; G] ++ L2') in H5  ...
          eapply AdequacyTri2 in H5. destruct H5.
          eapply EquivAuxPar with (L:= a :: L1');eauto.
          simpl in Heqw. inversion Heqw. auto.
          simpl. rewrite Nat.add_assoc. auto ...
        +++ (* with *)
          eapply IH with (m:= L_weight(F :: L1 ++ a :: L2))
                         (L:=F :: L1 ++ a :: L2)
                         (L' := [a] ++ L1' ++ [F ] ++ L2') in H6 ...
          eapply IH with (m:= L_weight(G :: L1 ++ a :: L2))
                         (L:=G :: L1 ++ a :: L2)
                         (L' := [a] ++ L1' ++ [G ] ++ L2') in H7 ...
          
          apply EquivAuxWith with (L := a :: L1'); simpl;auto .
          simpl in Heqw. inversion Heqw. auto.
          simpl. rewrite plus_assoc_reverse. apply le_plus_r.
          simpl in Heqw. inversion Heqw.  autounfold. omega.
        +++ (* quest *)
          eapply IH with (m:= L_weight(L1 ++ a :: L2))(L:=L1 ++ a :: L2) (L' := [a] ++ L1' ++ L2') in H5 ...
          eapply AdequacyTri2 in H5. destruct H5.
          eapply EquivAuxQuest with (L := a :: L1');eauto.
          simpl in Heqw. inversion Heqw. omega.
        +++ (* copy *)
          eapply IH with (m:= L_weight(L1 ++ a :: L2))(L:=L1 ++ a :: L2) (L' := [a] ++ L1' ++ L2') in H7 ...
          eapply EquivAuxSync with (L:=a :: L1');eauto.
          simpl in Heqw. rewrite L_weightApp in Heqw. simpl in Heqw.
          rewrite L_weightApp. 
          generalize(exp_weight0  l);intro.
          apply GtZero in H1.
          destruct H1. 
          rewrite H1 in Heqw. simpl in Heqw.
          inversion Heqw. 
          simpl. autounfold. omega.
        +++ (* forall *)
          assert(forall x, |-F- B; M; UP ((a :: L1' ) ++ [Subst FX x] ++ L2')) ...
          intro x.
          eapply IH with (m:= L_weight(Subst FX x :: L1 ++ a :: L2)) (L:=Subst FX x :: L1 ++ a :: L2)  ...
          inversion Heqw. simpl.
          rewrite <- subs_weight_weak with (x:=x) ...
          eapply EquivAuxForAll with (L:= a::L1') ...
  Qed.

  Theorem EquivUpArrow2 : forall B L L' M , |-F- B ; M ; UP L -> L =mul= L' ->|-F- B ; M ;  UP L'.
    intros.
    apply AdequacyTri2 in H.
    destruct H.
    eapply EquivUpArrow in H;eauto.
  Qed.
  
  (* Weakening *)
  Theorem TriWeakening : forall B L F X n, n |-F- B ; L ; X -> n |-F- B ++ [F] ; L ; X.
  Proof with solveF .
    intros.
    generalize dependent L .
    generalize dependent B .
    generalize dependent F .
    generalize dependent X .
    generalize dependent n . 
    induction n using strongind;intros ...
    + (* Base *)
      inversionF H ...
      apply trih_init2 with (B' := B' ++ [F]) ... eauto.
    + (* Inductive *)
      inversion H0;subst ...
      ++ eapply H in H3;auto.
         eapply H in H4;auto. 
         eapply trih_tensor;eauto.
      ++  eapply H with (B := B ++ [F0]) (F:=F) in H2 ...
          eapply trih_quest ...
          MReplace ( (B ++ [F]) ++ [F0]) ( (B ++ [F0]) ++ [F]) .
          auto.
      ++ eapply H in H4 ...
         eapply trih_dec1 with (F:=F0);eauto.
      ++ eapply H with (F:=F) in H4;auto.
         rewrite H3. rewrite H3 in H4.
         eapply trih_dec2 with (F:=F0);eauto.
      ++ eapply H in H2;auto.
         eapply trih_ex;eauto.
  Qed.
  
  (* Up and Down relation *)
  Lemma UpExtension: forall B M L F n, LexpPos (M ++ [F]) -> n |-F- B; M ++ [F] ; UP L ->
                                                                                  exists m, m<= S n /\ m |-F- B; M ; UP (L ++ [F]).
  Proof with solveF .
    intros.
    remember (L_weight  L) as w.
    generalize dependent L .
    generalize dependent B .
    generalize dependent M .
    generalize dependent n .
    generalize dependent w .

    induction w as [| w' IH] using strongind .  intros n  M HPos  B L HD Hw ...
    + (* w = 0 *)
      destruct L. (* L must be empty. The second case is trivial *)
      exists ((S n)).
      split;auto.
      simpl.
      eapply trih_store ;auto.
      
      generalize(LPos3 M [F] (meq_refl (M ++ [F])) HPos);intro.
      inversion H;auto.

      simpl in Hw.
      apply AsyncEqNeg;auto.
      
      apply exp_weight0LF in Hw;contradiction.

    + intros. 
      destruct L. (* L cannot be empty *)
      inversion Heqw ...
      inversionF H0;auto;subst;inversion Heqw;subst ...
      ++ (* top *)
        exists 0%nat;split ...
      ++ (* bot *)
        apply IH with (m:= L_weight  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega.
      ++  (* PAR *)
        apply IH with (m:= Exp_weight  F0 + Exp_weight  G + L_weight  L) in H5 ...
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl ... omega.
      ++ (* with *)
        apply IH with (m:= Exp_weight  F0 + L_weight  L) in H6 ...
        apply IH with (m:= Exp_weight  G + L_weight L) in H7 ...
        destruct H6 as [n'  [IHn IHd]].
        destruct H7 as [m'  [IHn' IHd']].
        simpl.
        exists (S (Init.Nat.max n' m'));split ...
        apply le_n_S.
        rewrite Max.succ_max_distr.
        apply Nat.max_le_compat;auto.
        autounfold. omega.
        autounfold. omega.
      ++  (* quest *)
        apply IH with (m:= L_weight  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl; eauto.
        omega. 
      ++ (* Store *) 
        MReplaceIn ((M ++ [F]) ++ [l]) ((M ++ [l]) ++ [F]) H7.
        apply IH with (m:= L_weight L) in H7;auto.
        destruct H7.
        destruct H1.
        exists (S x).
        split;auto.
        omega.
        eauto using WeightLeq ...
        MReplace ((M ++ [l]) ++ [F]) ((M ++ [F]) ++ [l]) ...
      ++  (* FORALL *)
        assert(forall x, exists m, m <= S n0 /\ m |-F- B; M; UP ((Subst FX x :: L)  ++ [F])).
        intro.
        generalize (H5 x);intro.
        eapply IH with (m:=Exp_weight (Subst FX x) + L_weight L) ...
        rewrite <- subs_weight_weak with (x:=x). auto.
        apply ax_subs_prop in H1.
        destruct H1 as [n H1].
        destruct H1 as [H1 H1'].
        exists (S n). split.
        omega.
        eapply trih_fx.
        intro x.
        generalize (H1' x); intro Hx ...
  Qed.
End FLLMetaTheory.