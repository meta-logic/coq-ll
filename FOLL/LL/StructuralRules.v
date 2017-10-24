(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Structural Rules 
In this file we prove several invertibility lemmas for the focused system. 
 *)


(*Add LoadPath "../" . *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export SequentCalculi.
Require Import Eqset.
Require Import AuxResults.
Set Implicit Arguments.


Module SRule (DT : Eqset_dec_pol).
  
  Module Export Sys :=  SqSystems DT.
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
  Proof with InvTac.
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
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl;simpl in H;inversion Hw'; inversion H;InvTac;subst;
        try(
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := (apply tri_store;InvTac; apply IH with (m:= L_weight  L);InvTac;try omega ) in
                            match l with
                            | Perp _ => solve_tac1
                            | Atom _ => solve_tac1
                            | 1   => solve_tac1
                            | 0   => solve_tac1
                            | _ ** _ => solve_tac1
                            | _ ⊕ _ => solve_tac1
                            | ! _  => solve_tac1
                            | E{ _ }   => solve_tac1
                            | Bot => apply tri_bot;apply IH with (m:= L_weight  L);InvTac;try(omega)
                            | ? _ => apply tri_quest;apply IH with (m:= L_weight  L);InvTac;try(omega)
                            end
            end ) .
      ++ (* par *)
        inversion H...
        apply IH  with (L:= F :: G :: L) (m:= (Exp_weight  F) + (Exp_weight G) + L_weight L) in H6;auto;simpl ...  omega.
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
  Proof with InvTac .
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
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl;simpl in H;inversion Hw' ;inversion H;InvTac;subst;
        try(
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := (inversion H';InvTac;subst; apply tri_store;InvTac; apply IH with (m:= L_weight  L);InvTac;try omega ) in
                            match l with
                            | 1   => solve_tac1
                            | 0   => solve_tac1
                            | _ ** _ => solve_tac1
                            | _ ⊕ _ => solve_tac1
                            | ! _  => solve_tac1
                            | E{ _ }   => solve_tac1
                            | Atom _ => apply tri_store;InvTac;  apply IH with (m:= L_weight  L) ; InvTac
                            | Perp _ => apply tri_store;InvTac;  apply IH with (m:= L_weight  L) ; InvTac
                            | Bot => inversion H';InvTac;subst; apply tri_bot; apply IH with (m:= L_weight  L);auto
                            end end ) .
      ++ (* par *)
        inversion H;InvTac;inversion H';InvTac;subst; apply tri_par ...
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
        generalize(H4 x);intros; generalize(H7 x);intros.
        eapply IH with (m:=  Exp_weight  (Subst FX x) + L_weight  L ) ...
        rewrite <- subs_weight_weak with (x:=x).  omega ...
        apply tri_fx ...
  Qed.



  Theorem EquivAuxPar : forall B  L L' M F G  n,  n |-F- B ; M ; UP (L ++ [F ; G] ++ L') -> |-F- B ; M ;  UP (L ++ [F $ G] ++ L').
  Proof with InvTac .
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
    +

      caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl;simpl in H;inversion Hw' ;inversion H;InvTac;subst;
        try(
            match goal with [|- |-F- _ ; _ ; UP (?l :: _) ] =>
                            let solve_tac1 := apply tri_store;InvTac; eapply IH  with (m:=  L_weight L) ;eauto;try omega in
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
  Proof with InvTac .
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
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl in *;inversion Hw';inversion H1;subst;InvTac;
        
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
  Proof with InvTac .
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
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl in *;inversion Hw';inversion H;subst;InvTac;
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
  Proof with InvTac .
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
    + caseLexp l ;inversion Hw as [Hw'];subst;auto;simpl in *;inversion Hw'; InvTac;
        try(apply tri_store;try(autoLexp);auto  ; apply IH  with (m:=  L_weight L);try(omega);auto).
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
        rewrite H0;auto.
        rewrite <- subs_weight_weak with (x:=x). auto.
  Qed.

  Theorem EquivAuxForAll : forall B  L L' M   FX, (forall x,  |-F- B ; M ; UP (L ++ [Subst FX x]++ L')) ->  |-F- B ; M ;  UP (L ++ [F{FX}] ++ L').
  Proof with InvTac .
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
    + caseLexp l ; inversion Hw as [Hw']; simpl in *;InvTac;
        try(
            assert(Hp: forall x,  |-F- B; M ++ [l]; UP (L ++ [Subst FX x] ++ L'))
            by (
                intro; generalize (H x); intro Hp'; simpl in *;subst; inversion Hp';subst;LexpContr;auto);
            apply IH  with (m:= L_weight  L) in Hp;  subst;simpl; try(apply tri_store;autoLexp);try(omega);auto;
            simpl in Hw';inversion Hw';try(omega);auto).
      ++ (* bot *)
        assert(Hp: forall x,  |-F- B; M; UP (L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp'; inversion Hp'; subst ...
        apply IH  with (m:= L_weight  L) in Hp; try(apply tri_bot);try(omega);auto.
        subst;simpl in Hw';inversion Hw';auto.
      ++ (* par *)
        assert(Hp: forall x,  |-F- B; M; UP ( F :: G :: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp'; inversion Hp'; subst;LexpContr;auto.
        LexpSubst. auto.
        assert(Asynchronous (F $ G)) by auto;contradiction.
        apply IH  with (L:= F :: G :: L) (m:= Exp_weight  F + Exp_weight G + L_weight  L) in Hp.
        apply tri_par. simpl in Hp. auto.
        subst. simpl in Hw';inversion Hw';auto.
        simpl. omega.
      ++ (* With *)
        subst.
        assert(Hp1: forall x,  |-F- B; M; UP ( F:: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp1'; inversion Hp1'; subst;LexpContr;intuition.
        LexpSubst;auto.
        assert(Hp2: forall x,  |-F- B; M; UP ( G:: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp2'; inversion Hp2'; subst;LexpContr;intuition.
        LexpSubst;auto.
        inversion Hw'.
        apply IH  with (L:= F :: L) (m:= Exp_weight F + L_weight L) in Hp1;try(omega); subst;autounfold;simpl;try(omega); auto.
        apply IH  with (L:= G :: L) (m:= Exp_weight G + L_weight L) in Hp2;try(omega); subst;autounfold;simpl;try(omega); auto.
      ++  (* quest *)
        assert(Hp: forall x,  |-F- B ++ [F]; M; UP (L ++ [Subst FX x] ++ L')) .
        intro; generalize (H x); intro Hp'; inversion Hp'; subst;LexpContr;intuition.
        subst;LexpSubst;auto.
        apply IH  with (m:= L_weight  L) in Hp. apply tri_quest;auto.
        subst;inversion Hw';omega.
        auto.
      ++ (* forall *)
        subst.
        assert(Hp: forall x x', |-F- B; M; UP ((Subst FX0 x') :: L ++ [Subst FX x] ++ L')).
        intro; generalize (H x); intro Hp'; inversion Hp'; subst;LexpContr;auto.
        assert(Asynchronous (F{ FX0})) by auto;contradiction.
        LexpSubst;auto.
        apply tri_fx;intro.
        apply IH with (L:= Subst FX0 x :: L) (m:= Exp_weight  (Subst FX0  x) + L_weight  L).
        simpl in Hw';inversion Hw'. autounfold.
        rewrite <- subs_weight_weak with (x:=x). auto.
        intro. simpl.
        apply Hp;auto.
        simpl. auto.
  Qed.

  Theorem EquivUpArrow : forall B L L' M n, n |-F- B ; M ; UP L -> L =mul= L' ->|-F- B ; M ;  UP L'.
  Proof with InvTac .
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
    + destruct L'. (* as [_| l']. *)
      (* H0 is inconsisten *) 
      apply DestructMulFalse in H0. contradiction.
      apply DestructMSet2 in H0 as Heq.
      destruct Heq as [Heq | Heq].
      ++ (* case 1 *)
        destruct Heq;subst.
         inversion H;subst;try(simpl in Heqw; inversion Heqw; subst;simpl;try(omega)).
         +++  (* top *)
           eapply tri_top.
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
          eapply IH with (m:= L_weight(L1 ++ a :: L2))(L:=L1 ++ a :: L2) (L' := [a] ++ L1' ++ L2') in H5 .
          simpl in H5. 
          eapply AdequacyTri2 in H5. destruct H5.
          
          apply EquivAuxBot with (L:= a :: L1') ...
          apply AdequacyTri1 in H1 ...

          simpl in Heqw. inversion Heqw. auto ...
          solve_permutation.
          reflexivity.
        +++ (* par *)
          eapply IH with (m:= L_weight(F :: G :: L1 ++ a :: L2))
                           (L:=F :: G :: L1 ++ a :: L2)
                           (L' := [a] ++ L1' ++ [F ; G] ++ L2') in H5 .
          eapply AdequacyTri2 in H5. destruct H5.
          
          eapply EquivAuxPar with (L:= a :: L1');eauto.
          simpl in Heqw. inversion Heqw. auto.
          simpl. rewrite Nat.add_assoc. auto ...
          solve_permutation.
          reflexivity.
        +++ (* with *)
          eapply IH with (m:= L_weight(F :: L1 ++ a :: L2))
                           (L:=F :: L1 ++ a :: L2)
                           (L' := [a] ++ L1' ++ [F ] ++ L2') in H6 .
          eapply IH with (m:= L_weight(G :: L1 ++ a :: L2))
                           (L:=G :: L1 ++ a :: L2)
                           (L' := [a] ++ L1' ++ [G ] ++ L2') in H7 .
          
          apply EquivAuxWith with (L := a :: L1'); simpl;auto.
          simpl in Heqw. inversion Heqw. auto.
          simpl. rewrite plus_assoc_reverse. apply le_plus_r.

          solve_permutation.
          reflexivity.
          simpl in Heqw. inversion Heqw. simpl.
          autounfold. omega.
          solve_permutation.
          reflexivity.
          
        +++ (* quest *)
          eapply IH with (m:= L_weight(L1 ++ a :: L2))(L:=L1 ++ a :: L2) (L' := [a] ++ L1' ++ L2') in H5 .
          eapply AdequacyTri2 in H5. destruct H5.
          eapply EquivAuxQuest with (L := a :: L1');eauto.
          
          simpl in Heqw. inversion Heqw. auto.
          simpl. omega.
          solve_permutation.
          reflexivity.

        +++ (* copy *)
          eapply IH with (m:= L_weight(L1 ++ a :: L2))(L:=L1 ++ a :: L2) (L' := [a] ++ L1' ++ L2') in H7 .

          eapply EquivAuxSync with (L:=a :: L1');eauto.

          simpl in Heqw. rewrite L_weightApp in Heqw. simpl in Heqw.
          rewrite L_weightApp.

          generalize(exp_weight0  l);intro.
          apply GtZero in H1.
          destruct H1.
          rewrite H1 in Heqw. simpl in Heqw.
          
          inversion Heqw.
          simpl. autounfold. omega.
          rewrite <- Heq2.
          solve_permutation.
          
          reflexivity.
        +++ (* forall *)
          
          assert(forall x, |-F- B; M; UP ((a :: L1' ) ++ [Subst FX x] ++ L2')).
          intro x.
          eapply IH with (m:= L_weight(Subst FX x :: L1 ++ a :: L2)) (L:=Subst FX x :: L1 ++ a :: L2)  ;auto.
          inversion Heqw.
          simpl.
          rewrite <- subs_weight_weak with (x:=x). auto.

          solve_permutation.

          apply EquivAuxForAll in H1.
          apply H1.
  Qed.

  Theorem EquivUpArrow2 : forall B L L' M , |-F- B ; M ; UP L -> L =mul= L' ->|-F- B ; M ;  UP L'.
    intros.
    apply AdequacyTri2 in H.
    destruct H.
    eapply EquivUpArrow in H;eauto.
  Qed.



  (* Weakening *)
  Theorem TriWeakening : forall B L F X n, n |-F- B ; L ; X -> n |-F- B ++ [F] ; L ; X.
    intros.
    generalize dependent L .
    generalize dependent B .
    generalize dependent F .
    generalize dependent X .
    generalize dependent n .
    induction n using strongind;intros;auto.
    + (* Base *)
      inversion H;subst.
      ++ eapply trih_init1;auto.
      ++ apply trih_init2 with (B' := B' ++ [F]);auto.
         rewrite H1.  solve_permutation.

      ++ eapply trih_one.
      ++ eapply trih_top.
    + (* Inductive *)
      inversion H0;subst.
      ++ eapply H in H3;auto.
         eapply H in H4;auto.
         eapply trih_tensor;eauto.
      ++ eapply H in H2;auto.
         eapply trih_plus1;eauto.
      ++ eapply H in H2;auto.
         eapply trih_plus2;eauto.
      ++ eapply H in H2;auto.
         eapply trih_bang;eauto.
      ++ eapply H in H3;auto.
         eapply trih_rel;eauto.
      ++ eapply H in H2;auto.
         eapply trih_bot;eauto.
      ++ eapply H in H2;auto.
         eapply trih_par;eauto.
      ++ eapply H in H2;auto.
         eapply H in H3;auto.
         eapply trih_with;eauto.
      ++  eapply H with (B := B ++ [F0]) (F:=F) in H2;auto.
          eapply trih_quest;auto.
          assert( (B ++ [F]) ++ [F0] =mul= (B ++ [F0]) ++ [F]) by solve_permutation.
          rewrite H1.
          auto.
      ++ eapply H in H3;auto.
         eapply trih_store;eauto.
      ++ eapply H in H4;auto.
         eapply trih_dec1 with (F:=F0);eauto.
      ++ eapply H with (F:=F) in H4;auto.
         rewrite H3. rewrite H3 in H4.
         eapply trih_dec2 with (F:=F0);eauto.
      ++ eapply H in H2;auto.
         eapply trih_ex;eauto.
      ++ assert(forall x,  n |-F- B ++ [F]; L; UP (Subst FX x :: M)).
         intro.
         generalize(H2 x);intro.
         eapply H in H1;eauto.
         eapply trih_fx; auto.

  Qed.
   
  (* Up and Down relation *)
  Lemma UpExtension: forall B M L F n, LexpPos (M ++ [F]) -> n |-F- B; M ++ [F] ; UP L ->
                                                                                  exists m, m<= S n /\ m |-F- B; M ; UP (L ++ [F]).
  Proof with InvTac .
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
      inversion H0;auto;subst;inversion Heqw;subst ...
      ++ (* top *)
        exists 0%nat;split ...
      ++ (* bot *)
        apply IH with (m:= L_weight  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega.
      ++  (* PAR *)
        apply IH with (m:= Exp_weight  F0 + Exp_weight  G + L_weight  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl ...
        simpl. omega.
      ++ (* with *)
        apply IH with (m:= Exp_weight  F0 + L_weight  L) in H6;auto.
        apply IH with (m:= Exp_weight  G + L_weight L) in H7;auto.
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
        assert(exists m0 : nat, m0 <= S n0 /\ m0 |-F- B; M ++ [l]; UP (L ++ [F])).
        apply IH with (m:= L_weight  L);eauto using WeightLeq.
        apply LPos1 with (L:= [l] ++ (M ++ [F]));auto.
        rewrite app_assoc_reverse ...
        
        apply lexpPosUnion;auto.
        apply AsynchronousFlexpPos;auto.
        apply AsyncEqNeg;auto.
        assert((M ++ [l]) ++ [F] =mul=  (M ++ [F]) ++ [l]) by solve_permutation.
        rewrite H1;auto.
        destruct H1 as [n'  [IHn IHd]]. 
        exists (S n');split;auto. omega. 
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
End SRule.