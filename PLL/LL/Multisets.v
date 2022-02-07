(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Multisets

Representation of multisets and some needed results about them.
 *)

Require Export Permutation.
Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sets.Multiset.
Require Export List.
Require Export PeanoNat Lia.
Require Export Eqset.
Export ListNotations.

Module MultisetList (EQ : Eqset_dec).

  Definition A := EQ.A.
  Definition eqA_dec := EQ.eqA_dec.
  Definition eq_dec := EQ.eq_dec.
  Definition eqA := EQ.eqA.

  (*   Fixpoint countIn (a: A) (l: list A) : nat :=
    match l with
      | nil => 0
      | x::xs => 
        match eqA_dec a x with
          | left _ => S(countIn a xs)
          | right _ => countIn a xs
        end
    end.
   *)

  Fixpoint removeElem (el: A) (l: list A) : list A :=
    match l with
    | nil => nil
    | hd::tl => 
      match eq_dec el hd with
      | left _ => tl
      | right _ => hd::removeElem el tl
      end
    end. 

  Fixpoint removeAll (l m: list A) : list A :=
    match m with
    | nil => l
    | hd::tl => removeAll (removeElem hd l) tl
    end.

  Definition Multiset := list A.

  Definition empty : Multiset := nil.
  Definition singleton a : Multiset := a :: nil.
  Definition union := app (A:=A).


  Definition mult := count_occ eq_dec.
  Definition meq X Y := forall a, mult X a = mult Y a.

  Definition rem := removeElem.
  Definition diff := removeAll.

  Definition member x M := mult M x > 0.

  Notation "X =mul= Y" := (meq X Y) (at level 70).
  Notation "X <>mul Y" := (~meq X Y) (at level 50).
  Notation "X / Y" := (diff X Y) .
  Notation "x # M" := (mult M x)(at level 10).
  Notation "x € M" := (member x M) (at level  10).

  Lemma in_countIn : forall a l, In a l -> a # l > 0.
  Proof.
    intros. apply count_occ_In; auto.
  Qed.

  (** count_occ_inv_nil *)

  Lemma empty_empty : forall M, (forall x, x # M = 0) -> M = [].
  Proof.
    intros.
    eapply (count_occ_inv_nil eq_dec); eauto.
  Qed.


  (** count_occ_nil *)

  Lemma countIn_nil : forall (x : A), x # [] = 0%nat.
  Proof. auto. Qed. 

  (** count_occ_not_In *)

  Lemma countIn_not_In: forall x l, ~ In x l <-> x # l = 0%nat.
  Proof.
    intros.
    apply count_occ_not_In.
  Qed.

  (** count_occ_inv_nil  *)

  Theorem countIn_inv_nil : forall (l : list A), (forall x:A, x # l = 0%nat) <-> l = [].
  Proof.
    intros. apply count_occ_inv_nil.
  Qed.

  (** count_occ_cons_eq *)

  Lemma countIn_cons_eq : forall (l : list A) (x y : A), y = x -> y # (x::l) = S (y # l).
  Proof.
    intros. apply count_occ_cons_eq; auto.
  Qed.

  (** count_occ_cons_neq *)

  Lemma countIn_cons_neq : forall (l : list A) (x y : A), y <> x -> y # (x::l) = y # l.
  Proof.
    intros. apply count_occ_cons_neq; auto.
  Qed.

  (** count_occ_In  *)

  Lemma countIn_In: forall x l, In x l <-> x # l > 0.
  Proof.
    intros. apply count_occ_In.
  Qed.

  #[export] Hint Resolve in_eq 
       in_cons
       not_in_cons
       in_nil
       in_split
       in_inv : core .

  Lemma mult_eqA_compat: forall x y M, x = y -> x # M = y # M.
  Proof.
    induction M; auto.
    intros.
    intuition. simpl.
    destruct (eq_dec a x); destruct (eq_dec a y); auto.
    rewrite H in e. contradiction.
    rewrite <- H in e. contradiction.
  Qed.

  Lemma meq_multeq: forall M N, M =mul= N -> (forall x, x # M = x # N).
  Proof. auto. Qed.

  Lemma multeq_meq: forall M N, (forall x, x # M = x # N) -> M =mul= N.
  Proof. auto. Qed.

  Lemma diff_empty_l : forall M: list A, [] / M = [].
  Proof.
    induction M; auto.
  Qed.

  Lemma diff_empty_r : forall M, M / [] = M.
  Proof.
    induction M; auto.
  Qed.

  Lemma empty_mult: forall x, x # [] = 0%nat.
  Proof. auto. Qed.

  Lemma union_mult: forall x M N, x # (M ++ N) = (x # M + x # N).
  Proof.
    induction M; auto.
    intros; simpl. destruct (eq_dec a x); auto. rewrite IHM. auto.
  Qed.

  Lemma union_mult2: forall x a N, x # (a :: N) = (x # [a] + x # N).
  Proof.
    intros.
    change (a::N) with ([a] ++ N).
    apply union_mult.
  Qed.

  Lemma mult_remove_in : forall x a M,
      x = a -> (x # (rem a M)) = ((x # M) - 1)%nat.
  Proof.
    induction M; auto.
    intro x_a.
    simpl. 
    destruct (eq_dec a a0); destruct (eq_dec a0 x); subst.
    auto with arith.
    contradiction.
    contradiction.
    simpl.
    destruct (eq_dec a0 a); auto.
    contradiction.
  Qed.

  Lemma mult_remove_not_in : forall M a x,
      x <> a -> x # (rem a M) = x # M.

  Proof.
    induction M; intros; auto.
    simpl; destruct (eq_dec a0 a); subst.
    destruct (eq_dec x a); auto.
    contradiction.
    destruct (eq_dec a x); subst; auto.
    contradiction.
    simpl.
    destruct (eq_dec a x); subst; auto.
  Qed.

  Lemma remove_perm_single : forall x a b M,
      x # (rem a (rem b M)) = x # (rem b (rem a M)).
  Proof.
    intros x a b M.
    case (eq_dec x a); case (eq_dec x b); intros x_b x_a.
    (* x=b,  x=a *)
    rewrite !mult_remove_in; trivial.
    (* x<>b, x=a *)
    rewrite mult_remove_in; trivial.
    do 2 (rewrite mult_remove_not_in; trivial).
    rewrite mult_remove_in; trivial.
    (* x=b,  x<>a *)
    rewrite mult_remove_not_in; trivial.
    do 2 (rewrite mult_remove_in; trivial).
    rewrite mult_remove_not_in; trivial.
    (* x<>b, x<>a *)
    rewrite !mult_remove_not_in; trivial.
  Qed.

  Lemma remove_perm_single' : forall a b M,
      (rem a (rem b M)) =mul= (rem b (rem a M)).
  Proof.
    intros.
    apply multeq_meq; intros.
    apply remove_perm_single.
  Qed.

  Lemma diff_mult_comp : forall x N M M',
      M =mul= M' -> x # (M / N) = x # (M' / N).
  Proof.
    induction N.
    intros; apply meq_multeq; trivial.
    intros M M' MM'.
    simpl.
    apply IHN.
    apply multeq_meq.
    intro x'.
    case (eq_dec x' a).
    intro xa; rewrite !mult_remove_in; trivial.
    erewrite meq_multeq with (N:=M'); trivial. 
    intro xna; rewrite !mult_remove_not_in; trivial.
  Qed.

  Lemma diff_perm_single : forall x a b M N, 
      x # (M / (a::b::N)) = x # (M / (b::a::N)).

  Proof.
    intros x a b M N.
    simpl; apply diff_mult_comp.
    apply multeq_meq.
    intro x'; apply remove_perm_single.
  Qed.

  Lemma diff_perm : forall M N a x,
      x # ((rem a M) / N) = x # (rem a (M / N)).

  Proof.
    intros M N; generalize M; clear M.
    induction N.
    auto.
    intros M b x.
    change (rem b M / (a::N)) with (M / (b::a::N)).
    rewrite diff_perm_single.
    simpl; apply IHN.
  Qed.

  Lemma diff_mult_step_eq : forall M N a x,
      x = a -> x # (rem a M / N) = (x # (M / N)) - 1%nat.

  Proof.
    intros M N a x x_a.
    rewrite diff_perm.
    rewrite mult_remove_in; trivial.
  Qed.

  Lemma diff_mult_step_neq : forall M N a x,
      x <> a -> x # (rem a M / N) = x # (M / N).

  Proof.
    intros M N a x x_a.
    rewrite diff_perm.
    rewrite mult_remove_not_in; trivial.
  Qed.

  Lemma diff_mult : forall M N x,
      x # (M / N) = (x # M) - (x # N).

  Proof.
    induction N.
    (* induction base *)
    simpl; intros; lia.
    (* induction step *)
    intro x; simpl.
    destruct (eq_dec a x); simpl.
    (* x = a *)
    fold rem.
    rewrite diff_mult_step_eq; auto.
    rewrite (IHN x).
    lia.
    (* x <> a *)
    fold rem.
    rewrite diff_mult_step_neq; auto.
  Qed.

  Lemma singleton_mult_in: forall x y, y = x -> x # [y] = 1%nat.
  Proof. intros. simpl. destruct (eq_dec y x); [trivial | contradiction]. Qed.

  Lemma singleton_mult_notin: forall x y, y <> x -> x # [y] = 0%nat.
  Proof. intros. simpl. destruct (eq_dec y x); [ contradiction | trivial]. Qed.

  #[export] Hint Unfold meq 
       empty
       singleton
       mult
       union
       diff : core .

  #[export] Hint Resolve mult_eqA_compat 
       meq_multeq
       multeq_meq
       empty_mult
       union_mult
       diff_mult
       singleton_mult_in
       singleton_mult_notin : core .

  #[export] Hint Rewrite empty_mult
       union_mult
       diff_mult using trivial : core.


  (*   Parameter mset_ind_type: forall P : Multiset -> Type,
        P empty -> (forall M a, P M -> P (M ++ [a])) -> forall M, P M. *)

  Lemma rem_to_diff : forall a M, rem a M =mul= M / [a].
  Proof. auto. Qed.


  Ltac mset_unfold := repeat progress unfold member.

  Ltac try_solve_meq :=
    (intros; (* try rewrite !rem_to_diff; *)
     match goal with 
     | |- _ =mul= _ => 
       ( apply multeq_meq
         ; intro
         ; try_solve_meq
       )
     | _ => 
       (    mset_unfold ; repeat progress (
                                   (*               try rewrite union_mult2; *)
	                           try rewrite union_mult;
                                   try rewrite diff_mult;
                                   try rewrite countIn_nil
                                 (*               try rewrite count_occ_nil *)
                                 )
            ; try lia
            ; try congruence
            ; try solve [auto]
       )
     end
    ).

  Ltac solve_meq :=
    (solve [try_solve_meq] ||
     fail "Goal is not an equality between multisets or fails to prove").

  Ltac try_solve_meq_ext :=
    (
      let go x := (solve [clear x; try_solve_meq_ext]) in (
        mset_unfold;
        intros; 
        try solve_meq;
        (match goal with
         | H : ?A =mul= ?B |- _ =>
           ( (try_solve_meq; rewrite (meq_multeq H); go H)
             || (try_solve_meq; rewrite <- (meq_multeq H); go H)
           )
         | H : ?a = ?b |- _ =>
           ( (rewrite (singleton_mult_in H); go H)
             || (rewrite H; go H)
             || (rewrite <- H; go H)
             || (rewrite (mult_eqA_compat H); go H)
             || (rewrite <- (mult_eqA_compat H); go H)
           )
         | H : ?a <> ?b |- _ =>
           (rewrite (singleton_mult_notin H); go H)
         | |- _ =mul= _ =>
           ( apply multeq_meq; try_solve_meq_ext )
         end || try_solve_meq))).

  Ltac solve_meq_ext :=
    (solve [try_solve_meq_ext] || 
     fail "Couldn't show multisets equality"). 




  Lemma meq_refl : forall M, M =mul= M.
  Proof.  solve_meq. Qed.

  Lemma meq_sym : forall M N, M =mul= N -> N =mul= M.
  Proof. solve_meq_ext. Qed.

  Lemma meq_trans :
    forall M N P, M =mul= N -> N =mul= P -> M =mul= P.
  Proof. solve_meq_ext. Qed.


  #[export] Hint Resolve meq_refl meq_sym meq_trans : core.

  #[export] Instance meq_Equivalence : Equivalence meq.
  Proof.
    split; eauto.
  Qed.

  #[export] Instance union_morph : Proper (meq ==> meq ==> meq) union.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  #[export] Instance insert_morph : Proper (eq ==> meq ==> meq) cons.

  Proof. intros a b ab c d cd.  subst.
         change (b::c) with ([b] ++ c).
         change (b::d) with ([b] ++ d).
         rewrite cd.  auto. Qed.

  #[export] Instance member_morph : Proper (eq ==> meq ==> iff) member.

  Proof. intros a b ab L1 L2 H; subst. unfold member. rewrite H. intuition. Qed.


  #[export] Instance union_morph': Proper (meq ==> meq ==> iff) (meq).
  Proof.
    intros a b ab c d cd; split;
      solve_meq_ext.
  Qed.

  #[export] Instance mult_morph : Proper (meq ==> eq ==> eq) mult.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  #[export] Instance diff_morph : Proper (meq ==> meq ==> meq) diff.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  #[export] Instance remove_morph : Proper (eq ==> meq ==> meq) removeAll.

  Proof. intros a b ab c d cd. solve_meq_ext. Qed.

  #[export] Instance rem_morph : Proper (eq ==> meq ==> meq) rem.

  Proof. intros a b ab c d cd; subst. 
         assert (rem b c =mul= c / [b]) as H1 by auto. 
         assert (rem b d =mul= d / [b]) as H2 by auto. 
         rewrite H1, H2, cd; auto. Qed.

  (*  Section MultisetLemmas. *)

  (*      Lemma mset_ind : forall P : Multiset -> Prop,
      P empty -> (forall M a, P M -> P (M ++ [a])) -> forall M, P M.

    Proof. exact mset_ind_type. Qed.

    Lemma mset_ind_set : forall P : Multiset -> Set,
        P empty -> (forall M a, P M -> P (M ++ [a])) -> forall M, P M.

    Proof. exact mset_ind_type. Qed. *)

  Lemma meq_cons_app a M : a :: M =mul= [a] ++ M.
  Proof. auto. Qed.   
  Lemma union_comm_app : forall M N, (M ++ N) =mul= (N ++ M).
  Proof. solve_meq. Qed.
  Lemma union_comm_cons : forall a M, (a :: M) =mul= (M ++ [a]).
  Proof. intros. rewrite meq_cons_app; solve_meq. Qed.
  Lemma union_assoc_app : forall M N P, M ++ N ++ P =mul= (M ++ N) ++ P.
  Proof. solve_meq. Qed.

  Section facts_remove.

    Lemma rem_a : forall a, rem a ([a]) =mul= [].
    Proof.
      intros; simpl.
      case (eq_dec a a); auto.
    Qed.

    Lemma rem_ab : forall a b, b = a -> rem a ([b]) =mul= [ ].
    Proof.
      intros; subst. apply rem_a.
    Qed.

    Lemma rem_not_ab : forall a b, b <> a -> rem a ([b]) =mul= [b].
    Proof.
      intros; simpl.
      case (eq_dec a b); auto; intros. 
      symmetry in e. contradiction.
    Qed.

    Lemma rem_aM_app : forall a M, rem a ([a] ++ M) =mul= M.
    Proof.
      intros; simpl.
      case (eq_dec a a); auto; intros.
      contradiction.
    Qed.

    Lemma rem_abM_app : forall a b M, b = a -> rem a ([b] ++ M) =mul= M.
    Proof.
      intros; simpl.
      case (eq_dec a b); auto; intros.
      symmetry in H.
      contradiction.
    Qed.

    Lemma rem_not_abM_app : forall a b M, b <> a -> rem a ([b] ++ M) =mul= [b] ++ rem a M.
    Proof.
      intros; simpl.
      case (eq_dec a b); auto; intros.
      symmetry in e.
      contradiction.
    Qed.

    Lemma rem_aM_cons : forall a M, rem a (a :: M) =mul= M.
    Proof.
      intros.
      change (a :: M) with ([a] ++ M).
      apply rem_aM_app.
    Qed.

    Lemma rem_to_union_app: forall L M x, M =mul= [x] ++ L -> L =mul= (rem x M).
    Proof.
      intros. rewrite H. rewrite rem_aM_app. auto.
    Qed.
    Lemma rem_to_union_cons: forall L M x, M =mul= x :: L -> L =mul= (rem x M).
    Proof.
      intros. rewrite H. rewrite rem_aM_cons. auto.
    Qed.

  End facts_remove.



  Lemma member_singleton (x y : A) : x € [y] -> x = y.
  Proof.
    unfold member; intros.
    case (eq_dec x y); [trivial | intro x_neq_y].
    assert (x # [y] = 0%nat); [auto | idtac].
    rewrite H0 in H; lia.
  Qed.




  Lemma emp_mult : forall M, M =mul= [] <-> M = [].
  Proof.
    split; intros; subst; auto.
    eapply (count_occ_inv_nil eq_dec); intros.
    apply meq_multeq with (x:=x) in H; auto.
  Qed.

  Lemma union_perm M N P : M ++ N ++ P =mul= M ++ P ++ N.
  Proof. solve_meq. Qed.
  #[export] Hint Resolve union_perm : core.

  Lemma union_nil M : M ++ [] =mul= M.
  Proof. solve_meq. Qed.

  Lemma notempty_member M : ~ M =mul= [] -> exists N a, M =mul= [a] ++ N.

  Proof.
    intros H.
    destruct M.
    absurd ([] =mul= []); auto.
    exists M. exists a. auto. 
  Qed.

  Lemma not_empty M x : x € M -> M =mul= [] -> False.

  Proof.
    unfold member; intros mult_x_M M_is_empty.
    absurd (x # M = 0%nat).
    lia.
    assert (x # [] = 0%nat); [auto | idtac].
    assert (x # M = x # []); [apply meq_multeq; trivial | idtac].
    lia.
  Qed.

  Lemma member_union_l a M N : a € M -> a € (M ++ N).
  Proof. unfold member; intro H. rewrite union_mult. lia. Qed.

  Lemma member_union_r a M N : a € N -> a € (M ++ N).
  Proof. unfold member; intro H. rewrite union_mult. lia. Qed.       

  Lemma mult_insert : forall M a, (a # (M ++ [a])) > 0.
  Proof.
    intros M a.
    replace (a # (M ++ [a])) with ((a # M) + (a # [a]))%nat.
    replace (a # [a]) with 1%nat.
    lia.
    symmetry; auto.
    auto.
  Qed.

  Lemma singleton_member a : a € [a].
  Proof.
    unfold member. assert (a # [a] = 1%nat); [idtac | lia].
    apply singleton_mult_in; auto with sets.
  Qed.

  Lemma member_insert_app a M : a € ([a] ++ M).
  Proof. apply member_union_l. apply singleton_member. Qed.
  Lemma member_insert_cons a M : a € (a :: M).
  Proof. change (a :: M) with ([a] ++ M). apply member_union_l. apply singleton_member. Qed. 
  Lemma member_diff_member a M N : a € (M / N) -> a € M.
  Proof. unfold member. rewrite (diff_mult M N). lia. Qed.
  #[export] Hint Resolve singleton_member  member_insert_app member_insert_cons: core.
  Lemma diff_member_ly_rn a M N : a € M -> ~a € N -> a € (M / N).
  Proof. unfold member; intros H H0. rewrite diff_mult. lia. Qed.

  Lemma diff_remove_both a M N :
    a € M -> a € N -> M / N =mul= (rem a M) / (rem a N).
  Proof.
    unfold member; intros H H0.
    apply multeq_meq; intro x.
    rewrite !diff_mult.
    destruct (eq_dec x a); subst. 
    rewrite !mult_remove_in; auto.
    rewrite !Nat.sub_1_r.
    rewrite <- (Nat.sub_succ (Nat.pred (a # M)) _).
    rewrite !Nat.succ_pred_pos; auto.
    rewrite !mult_remove_not_in; auto.
  Qed.

  Lemma member_union a M N : a € (M ++ N) -> a € M \/ a € N.
  Proof. unfold member. rewrite (union_mult _ M N). lia. Qed.

  Lemma member_meq_union a M N M' N' :
    M ++ N =mul= M' ++ N' -> (a € M \/ a € N) -> ~a € N' -> a € M'.
  Proof.
    unfold member; intros.
    assert (((a#M)+ (a#N))%nat
            = ((a#M') + (a#N'))%nat).
    rewrite <- !union_mult.
    apply meq_multeq; trivial.
    lia.
  Qed.

  Lemma meq_union_meq M N P : M ++ P =mul= N ++ P -> M =mul= N.
  Proof.
    intros; try_solve_meq.
    assert (((x#M) + (x#P))%nat
            = ((x#N) + (x#P))%nat).
    rewrite <- !union_mult.
    apply meq_multeq; trivial.
    lia.
  Qed.

  Lemma meq_union_meq2 M N P : P ++ M =mul= P ++ N -> M =mul= N.
  Proof.
    intros; try_solve_meq.
    assert (((x#P) + (x#M))%nat
            = ((x#P) + (x#N))%nat).
    rewrite <- !union_mult.
    apply meq_multeq; trivial.
    lia.
  Qed.

  #[export] Hint Resolve meq_union_meq meq_union_meq2 : core .

  Lemma meq_meq_union M N P : M =mul= N -> M ++ P =mul= N ++ P.
  Proof. solve_meq. Qed.
  #[export] Hint Resolve meq_meq_union : core.
  Lemma meq_ins_ins_eq a a' M M' :
    M ++ [a] =mul= M' ++ [a'] -> a = a' -> M =mul= M'.
  Proof.
    intros.
    cut (M ++ [a] =mul= M' ++ [a']).
    rewrite H0; intro; apply meq_union_meq with [a']; trivial.
    trivial.
  Qed.

  Lemma member_ins_ins_meq a a' M M' :
    M ++ [a] =mul= M' ++ [a'] -> a' <> a -> a € M'.

  Proof.
    unfold member; intros.
    assert (((a#M) + 1)%nat = ((a#M') + 0)%nat).
    erewrite <- singleton_mult_in with (x:=a) (y:=a); auto.
    erewrite  <- (singleton_mult_notin _ _ H0).
    rewrite <- !union_mult.
    apply meq_multeq; trivial.
    lia.
  Qed.

  Lemma meq_ins_rem a M : a € M -> M =mul= (rem a M) ++ [a].

  Proof.
    unfold member; intros.
    apply multeq_meq; intro.
    rewrite union_mult.
    (*       rewrite diff_mult. *)
    case (eq_dec a x); intro x_a.
    (* x =A= a *)
    rewrite singleton_mult_in; trivial.
    assert (x#M = a#M).
    apply mult_eqA_compat; auto.
    rewrite mult_remove_in; auto.
    lia.
    (* ~ x =A= a *)
    rewrite !singleton_mult_notin; auto.
    rewrite mult_remove_not_in; auto.
  Qed.


  Lemma insert_meq M N a : a :: M =mul= a :: N -> M =mul= N.
  Proof.
    intros.
    eapply meq_union_meq with (P:=[a]).
    rewrite union_comm_app, (union_comm_app N _).
    auto.
  Qed.
  #[export] Hint Resolve insert_meq : core.

  Lemma meq_insert_remove a M : a € M -> a :: (rem a M) =mul= M.
  Proof.
    intros. symmetry.
    change (a :: rem a M) with ([a] ++ rem a M).
    rewrite union_comm_app.
    apply meq_ins_rem; auto.
  Qed.

  Lemma insert_remove_noteq a a' M :
    a <> a' -> rem a (a' :: M) =mul= a' :: (rem a M).
  Proof.
    intros.
    change (a' :: M) with ([a'] ++ M).
    rewrite rem_not_abM_app. auto. firstorder. Qed. 

  (*     Lemma meq_cons a M N :
      M ++ [a] =mul= N -> exists N', N =mul= N' ++ [a] /\ M =mul= N'.     
    Proof.
      intros.
      exists (rem a N); split.
      assert (aN: a € N).
      rewrite <- H.
      rewrite (union_comm_app M [a]).
      apply member_insert_app.
      set (N' := N) in |- * at 1.
      rewrite (meq_ins_rem _ _ aN); unfold N'; clear N'.
      rewrite (meq_remove_insert a (N / [a])).
      apply meq_ins_rem; trivial.    
      rewrite <- H.
      symmetry.
      apply meq_remove_insert. 
    Qed. *)

  Lemma meq_diff_meq M N P : M =mul= N -> M / P =mul= N / P.

  Proof. solve_meq. Qed.

  (*  Section Decidability. *)

  Lemma member_dec a M : {a € M}+{~a € M}.

  Proof.
    intros; case (Compare_dec.zerop (a # M)); intro.
    right; mset_unfold. lia.
    left; auto.
  Qed.

  Lemma empty_dec : forall M, {M =mul= empty}+{~ M =mul= empty}.

  Proof.
    induction M; intros.
    left; solve_meq.
    right; intro emp.
    absurd (a # (a :: M) = a # []); auto.
    rewrite empty_mult; rewrite union_mult2.
    set (w := singleton_member a); unfold member in w.
    lia.
  Qed.

  (*
 End Decidability. *)

  (*     Lemma insert_diff a M N :
       a :: M / N =mul= empty -> a € N /\ M / rem a N =mul= empty.

    Proof.
      intros.
      assert (a € N).
      destruct (member_dec a N); trivial.
      exfalso.
      apply not_empty with empty a; auto.
      fold (member a empty).
      rewrite <- H.
      apply member_insert.
      split; trivial.
      rewrite <- H.
      Check diff_remove_both.
      symmetry.
      erewrite diff_remove_both with (a:=a); auto.

       erewrite member_insert. a M).  H0).
      solve_meq.
    Qed.
   *)
  Lemma diff_MM_empty M : M / M =mul= [].
  Proof. solve_meq. Qed.

  Lemma ins_meq_union M N P a :
    M ++ [a] =mul= N ++ P -> a € N -> M =mul= (N / [a]) ++ P.
  Proof.
    mset_unfold; intros.
    apply multeq_meq; intro x.
    assert (((x # M) + ( x # [a]))
            = ((x#N) + (x#P))).
    rewrite <- !union_mult.
    apply meq_multeq; trivial.
    case (eq_dec x a); intro x_a.
    (* x =A= a *)
    assert (x#N = a#N).
    apply mult_eqA_compat; trivial.
    rewrite union_mult.
    rewrite diff_mult.
    rewrite singleton_mult_in; auto.
    assert (((x#M) + 1)%nat = ((x#N) + (x#P))%nat).
    rewrite <- (singleton_mult_in _ _ (symmetry x_a)); trivial.
    lia.
    (* ~ x =A= a *)
    rewrite union_mult.
    rewrite diff_mult.
    assert ( a <> x) by auto.
    rewrite (singleton_mult_notin _ _ H2).
    assert (((x#M) + 0)%nat = ((x#N) + (x#P))%nat).
    rewrite <- (singleton_mult_notin _ _ H2); trivial.
    lia.
  Qed.

  Lemma mem_memrem M a b : a <> b -> a € M -> a € (M / [b]).
  Proof.
    unfold member; intros.
    rewrite diff_mult.
    rewrite singleton_mult_notin, Nat.sub_0_r;
      auto.
  Qed.

  Lemma member_notempty M x : x € M -> ~ M =mul= [].
  Proof.
    unfold not; intros.
    absurd (x # M = 0%nat).
    unfold member in H; lia.
    erewrite meq_multeq with (N:=[]); auto.
  Qed.

  Lemma singleton_notempty x : ~ [x] =mul= [].
  Proof. intro. apply emp_mult in H. inversion H. Qed.

  Lemma union_isempty M N : M ++ N =mul= [] -> M =mul= [].
  Proof.
    intros.
    eapply emp_mult in H.
    apply app_eq_nil in H.
    destruct H; subst; auto.
  Qed.

  Lemma union_notempty M N : ~ M =mul= [] -> ~ M ++ N =mul= [].
  Proof.
    compute in *; intros; apply H. apply union_isempty with N; trivial.
  Qed.

  Lemma remove_union a L R :
    a € L -> rem a (L ++ R) =mul= (rem a L) ++ R.
  Proof.
    intros.
    apply multeq_meq; intros.
    rewrite !rem_to_diff.
    repeat (rewrite diff_mult || rewrite union_mult).
    destruct (eq_dec a x).
    rewrite singleton_mult_in; trivial.
    erewrite mult_eqA_compat with (y:=a); auto.
    unfold member in H; lia.
    rewrite singleton_mult_notin; trivial.
    lia.
  Qed.

  (*  End MultisetLemmas. *)
  (*
 Section Multiset. *)

  Lemma multiset_meq_non_empty : forall M,
      ~ M =mul= [] -> M <> nil.
  Proof.
    intros.
    destruct M; auto.
    intro.
    inversion H0.
  Qed.

  Lemma multiset_meq_empty : forall M,
      M =mul= [] ->  M = [].   
  Proof.
    apply emp_mult.
  Qed.

  Lemma member_list_multiset : forall l,
      forall x, In x l -> member x l.
  Proof.
    induction l.
    (* base step *)
    intros x x_In_nil; absurd (In x nil); auto.
    (* induction step *)
    simpl; intros x x_In_al; case x_In_al.
    intro ax; rewrite ax; apply member_insert_cons.
    intro x_In_l; mset_unfold.
    change (a :: l) with ([a] ++ l).
    rewrite union_mult.
    assert ((x # l) > 0).
    apply (IHl x); trivial.
    lia.
  Qed.


  (*   End Multiset. *)

  Add Parametric Relation : Multiset meq
      reflexivity proved by meq_refl
      symmetry proved by meq_sym
      transitivity proved by meq_trans as eq_ms.


  (** Compatibility of Multiset and Permutation *)
  (* Lemma meq_nil : [] =mul= [].
Proof. solve_meq. Qed.
   *)
  Lemma eq_step : forall a x,
      a = x -> x # [a] = 1%nat.
  Proof. intros. simpl. case (eq_dec a x); [trivial | contradiction]. Qed.

  Lemma not_eq_zero : forall a x,
      a <> x -> x # [a] = 0%nat. 
  Proof. intros. simpl. case (eq_dec a x); [contradiction | trivial]. Qed.

  Lemma union_mult_step_eq : forall M N a x,
      a = x -> x # ( [a] ++ (M ++ N)) = x # (M ++ N) + 1.
  Proof.
    intros M N a x x_a.
    rewrite union_mult. 
    rewrite eq_step; auto. lia.
  Qed.

  Lemma eq_then_meq: forall M N,
      M = N -> M =mul= N.
  Proof. intros; destruct M; subst; apply multeq_meq; auto. Qed.

  Lemma union_left : forall M N1 N2, N1 =mul= N2 -> (N1 ++ M) =mul= (N2 ++ M).
  Proof. solve_meq. Qed.

  Lemma union_right : forall M N1 N2, N1 =mul= N2 -> (M ++ N1) =mul= (M ++ N2).
  Proof. solve_meq. Qed.

  #[export] Hint Resolve union_left union_right : core.

  Lemma union_rotate x y z : x ++ (y ++ z) =mul= z ++ (x ++ y).
  Proof. solve_meq. Qed.

  Lemma union_reverse x y z : x ++ (y ++ z) =mul= z ++ (y ++ x).
  Proof. solve_meq. Qed.

  Lemma meq_congr x y z t : x =mul= y -> z =mul= t -> x ++ z =mul= y ++ t.
  Proof. solve_meq. Qed.

  Lemma union_perm_left x y z : x ++ (y ++ z) =mul= y ++ (x ++ z).
  Proof. solve_meq. Qed.

  Lemma union_perm_left' x a z : x ++ (a :: z) =mul= a :: (x ++ z).
  Proof. change ( x ++ (a :: z) =mul= a :: (x ++ z)) with
         (x ++ ([a] ++ z) =mul= [a] ++ (x ++ z)). 
         apply union_perm_left. Qed.

  Lemma union_perm_left'' x a z : (a :: x) ++ z  =mul= a :: (x ++ z).
  Proof. auto. Qed.

  #[export] Hint Resolve union_rotate 
       union_reverse 
       meq_congr 
       union_perm_left 
       union_perm_left'
       union_perm_left'' : core.

  Lemma multiset_twist1 x y z t : x ++ ((y ++ z) ++ t) =mul= (y ++ (x ++ t)) ++ z.
  Proof. solve_meq. Qed.

  Lemma multiset_twist2 x y z t : x ++ ((y ++ z) ++ t) =mul= (y ++ (x ++ z)) ++ t.
  Proof. solve_meq. Qed.

  #[export] Hint Resolve multiset_twist1 multiset_twist2 : core .

  Lemma treesort_twist1 x y z t u :
    u =mul= (y ++ z) ->
    x ++ (u ++ t) =mul= (y ++ (x ++ t)) ++ z.
  Proof.
    intros.
    apply multeq_meq; intros.
    apply meq_multeq with (x:=x0) in H.
    rewrite !union_mult.
    rewrite !union_mult in H.
    lia.
  Qed.

  Lemma treesort_twist2 x y z t u :
    u =mul= (y ++ z) ->
    x ++ (u ++ t) =mul= (y ++ (x ++ z)) ++ t.
  Proof.
    intros. 
    apply multeq_meq; intros.
    apply meq_multeq with (x:=x0) in H.
    rewrite !union_mult.
    rewrite !union_mult in H.
    lia.
  Qed.

  #[export] Hint Resolve treesort_twist1 treesort_twist2 : core.

  Lemma my_p x y z t : ((x ++ y) ++ z) ++ t =mul= t ++ (z ++ (x ++ y)).
  Proof. solve_meq. Qed.

  #[export] Hint Resolve my_p : core.

  Lemma meq_skip : forall a M1 M2, M1 =mul= M2 -> a :: M1 =mul= a :: M2.
  Proof. intros. change (a :: M1 =mul= a :: M2) with ([a] ++ M1 =mul= [a] ++ M2). 
         apply union_right; auto.
  Qed.

  Lemma meq_swap : forall a b M1 M2, M1 =mul= M2 -> (a :: b:: M1) =mul= (b :: a :: M2).
  Proof.
    intros.
    change  (a :: b:: M1 =mul= b :: a :: M2)
    with ([a] ++ [b] ++ M1 =mul= [b] ++ [a] ++ M2).
    apply multeq_meq; intros.
    apply meq_multeq with (x:=x) in H.
    rewrite !union_mult.
    lia.
  Qed.

  Lemma meq_swap_cons a b M : (a :: b:: M) =mul= (b :: a :: M).
  Proof.
    rewrite meq_swap; auto.
  Qed.

  Lemma union_rotate_cons a b c M : (a :: b :: c :: M) =mul= (c :: a :: b :: M).
  Proof. change ((a :: b :: c :: M) =mul= (c :: a :: b :: M)) with 
         (([a] ++ [b] ++ [c] ++ M) =mul= ([c] ++ [a] ++ [b] ++ M)). solve_meq. Qed.

  #[export] Hint Resolve meq_skip meq_swap meq_swap_cons union_rotate_cons : core.


  Lemma pair_app (F G: A) : [F; G] = [F]++[G].
  Proof. auto. Qed.

  Ltac app_normalize_aux :=
    try rewrite !pair_app; 
    repeat
      match goal with
      | |- _ =mul= ?a::?M => change (a :: M) with
                             ([a] ++ M)
      | |- ?a::?M =mul= _ => change (a :: M) with
                             ([a] ++ M)    
      | |- _ =mul= _++?a::?M++?N => change (a::M++N) with
                                    ([a]++M++N)    
      | |- _++?a::?M++?N =mul= _ => change (a::M++N) with
                                    ([a]++M++N)             
      end.

  Lemma union_assoc_cons
    : forall a (M N P : list A), a :: M ++ N ++ P =mul= (a :: M ++ N) ++ P.
  Proof.
    intros. rewrite app_assoc.
    auto.
  Qed.
  #[export] Hint Resolve union_assoc_cons: core.

  Ltac app_normalize := repeat (
                            rewrite <- !union_assoc_cons ||
                            rewrite <- !app_assoc || 
                            rewrite app_nil_l); auto.


  Lemma perm_cons_single a b: a::[b] =mul= b::[a].
  Proof. 
    change (a :: [b] =mul= b :: [a]) with
    ([a] ++ [b] =mul= [b] ++ [a]). 
    rewrite union_comm_app.
    auto. Qed.

  Lemma perm_cons a b L: a::b::L =mul= b::a::L.
  Proof. 
    change (a :: b :: L =mul= b :: a :: L) with
    ([a] ++ [b] ++ L =mul= [b] ++ [a] ++ L). auto. Qed.

  #[export] Hint Resolve perm_cons_single perm_cons : core.

  Lemma union_middle : forall M N1 N2 : list A, N1 =mul= N2 -> N1 ++ M =mul= M ++ N2.
  Proof.
    intros.
    rewrite union_comm_app.
    auto.
  Qed.


  Ltac perm_simplify := app_normalize; repeat (
                                           rewrite app_nil_r || auto ||
                                           match goal with
                                           | [ |- ?L1 =mul= ?L1 ] => reflexivity
                                           | [ |- (?A1++_) =mul= (?A1++_) ] => apply union_right
                                           | [ |- (_++?A1) =mul= (?A1++_) ] => apply union_middle  
                                           | [ |- (_++?A1) =mul= (_++?A1) ] => apply union_left
                                           | [ |- (?A1::_) =mul= (?A1::_) ] => apply meq_skip
                                           | [ |- _  =mul= (?L1++_) ] => (
                                               rewrite (union_perm_left L1) at 1 ||
                                               rewrite <- (union_perm_left' L1) at 1 ||
                                               rewrite (union_comm_app L1) at 1 ||
                                               rewrite (meq_cons_app L1) at 1 )
                                           | [ |- _  =mul= (?A1::_) ] => (
                                               rewrite union_perm_left' ||
                                               rewrite perm_cons ||
                                               rewrite <- meq_cons_app  ||
                                               rewrite perm_cons_single ) 
                                           | [ |- _ =mul= _ ] => fail
                                           end). 

  Ltac solver_permute :=
    match goal with
    | [ |- _ =mul= _ ] => perm_simplify; fail "perm failed"
    | [ |- _ ] => fail "perm can't solve this system."
    end. 

  Ltac solv_P :=
    try rewrite !union_perm_left';
    repeat
      match goal with
      | |- _ =mul= ?a::?M => change (a :: M) with
                             ([a] ++ M); try rewrite !union_perm_left'
      | |- ?a::?M =mul= _ => change (a :: M) with
                             ([a] ++ M) ; try rewrite !union_perm_left'              
      end.

  Ltac solve_permutation := 
    solve [auto | solv_P; unfold meq; intro; rewrite !union_mult; lia | timeout 3 solver_permute ].

  Lemma In_union_or : forall x N M, (x € (N ++ M)) <->  x € M \/ x € N.
  Proof.
    split; intros;
      unfold member in *; unfold mult in *. apply countIn_In in H. 
    apply in_app_or in H. destruct H;[right;apply countIn_In | left;apply countIn_In]; auto.
    apply countIn_In.
    rewrite <- countIn_In in H. apply or_comm in H. rewrite <- countIn_In in H.
    apply in_or_app; auto.
  Qed.

  Lemma In_union_or' : forall x M, x € M -> forall N, x € (N ++ M).
  Proof.
    intros.
    apply In_union_or.
    left; auto.
  Qed.
  Lemma In_to_in : forall x M, In x M <-> x € M.
  Proof.
    split;intros;
      destruct M;
      unfold member in *;
      unfold mult in *;
      apply countIn_In; auto.
  Qed.

  Lemma meq_In_In: forall L1 L2, L1 =mul= L2 -> (forall x, x € L1 <-> x € L2).
  Proof.
    unfold meq in *.
    unfold member in *.
    split;
      intros P.
    rewrite <- H; auto.
    rewrite H; auto.
  Qed.

  Lemma meq_cons_In :
    forall l1 l2 e, ([e] ++ l1) =mul= l2 -> e € l2.
  Proof.
    intros.
    eapply meq_In_In with (L2:=[e] ++ l1).
    rewrite <- H; eauto.
    apply In_union_or.
    right.
    apply In_to_in.
    firstorder.
  Qed.


  (** Properties about  diff *)

  Lemma nil_rem: forall M, [] / M = [].
  Proof. induction M; intros; auto. Qed.

  Lemma rem_nil: forall M, M / [] = M.
  Proof. auto. Qed.

  Lemma remove_in_not : forall x a M, x <> a -> x € M -> x € (rem a M).
  Proof.
    unfold member; intros.
    apply mult_remove_not_in with (M:=M) in H.
    rewrite H; auto.
  Qed.

  (*  Lemma permut_remove_hd :
    forall l l1 l2 a,
       [a] ++ l =mul= l1 ++ ([a] ++ l2) -> l =mul= l1 ++ l2.
  Proof.
    intros.
    symmetry in H.
    apply rem_to_union in H.
    rewrite rem_to_diff in H.
    rewrite H.
    apply multeq_meq. intro x.
    rewrite diff_mult.
    rewrite !union_mult.
    lia.
Qed. *)


  Lemma rem_skip : forall a M1 M2, M1 =mul= M2 -> (rem a M1) =mul= (rem a M2).
  Proof.
    intros.
    rewrite H; auto.
  Qed.


  Lemma rem_perm_not : forall M a x,
      x <> a -> rem a ([x] ++ M) =mul= [x] ++ (rem a M).
  Proof.
    simpl; intros.
    case (eq_dec a x); auto; intros.
    symmetry in e.
    contradiction.
  Qed.

  Lemma principal : forall L M M0 a b,
      a <> b -> L =mul= a :: M -> L =mul= b :: M0 -> 
      M0 =mul= a :: (rem a M0) /\ M =mul= b :: (rem b M) .
  Proof.
    intros L M M0 a b Eq I1 I2.
    rewrite meq_cons_app in I1, I2.

    split; rewrite meq_cons_app.
    rewrite I1 in I2.
    apply rem_to_union_app in I2.
    rewrite rem_perm_not in I2; auto.
    rewrite I2.
    simpl.
    case (eq_dec a a); intros; auto.
    contradiction.
    rewrite I2 in I1.
    apply rem_to_union_app in I1.
    rewrite rem_perm_not in I1; auto.
    rewrite I1.
    simpl.
    case (eq_dec b b); intros; auto.
    contradiction.
  Qed.

  Lemma seconda : forall L M M0 N a b,
      a <> b -> L =mul= a :: M -> L =mul= b :: (M0 ++ N) -> 
      exists L', M0 ++ N =mul= a :: L'.
  Proof.
    intros L M M0 N a b Eq I1 I2.
    exists (rem b M).
    rewrite I1 in I2.
    apply rem_to_union_app in I2.
    rewrite I2.
    apply rem_perm_not; auto.
  Qed.

  Lemma seconda_sec : forall L M M0 a b,
      a <> b -> L =mul= a :: M -> L =mul= b :: M0 -> 
      exists L1 L2, M0 =mul= a :: L1 /\  M =mul= b :: L2.
  Proof.
    intros L M M0 a b NEq I1 I2.
    exists ((rem a M0)).
    exists ((rem b M)).
    refine (principal _ _ _ _ _ NEq I1 I2).
  Qed.

  Lemma meq_swap' : forall L a M N, 
      L =mul= a :: M ->
      L =mul= a :: N ->
      M =mul= N.
  Proof.
    intros.
    rewrite H0 in H.
    apply rem_to_union_cons in H.
    rewrite H.
    simpl.
    case (eq_dec a a); intros; auto.
    contradiction.
  Qed.

  Lemma meq_eq_s : forall L A B M N, 
      L =mul= A ++ M ->
      L =mul= B ++ N ->
      A =mul= B ->
      M =mul= N.
  Proof.
    intros L X B M N P1 P2 P3.
    rewrite P3 in P1.
    rewrite P2 in P1.
    revert L X M N P1 P2 P3.
    induction B; intros; auto.

    eapply IHB with (L:= B ++ N); auto.
    change (a :: B) with ([a] ++ B) in *.

    apply rem_to_union_app in P1.
    rewrite P1.
    simpl.
    case (eq_dec a a); intros; auto.
    contradiction.
  Qed.

  Lemma mem_step : forall a x,
      a = x -> x € [a].
  Proof. intros; subst. apply singleton_member. Qed.
  (*  Lemma mem_step_not : forall a x,
   a <> x -> ~ x € [a].
Proof. intros. compute. case (eq_dec a x); [contradiction | trivial].

   intros. inversion H0. Qed. *)

  Lemma member_then_eq : forall a L,
      a € L -> exists P1 P2, L = P1 ++ [a] ++ P2.
  Proof.
    intros.
    apply in_split. 
    apply In_to_in; auto.
  Qed.
  
  Lemma member_then_meq : forall a L,
      a € L -> exists P, L =mul= a :: P.
  Proof.
    intros.
    assert (exists P1 P2, L = P1 ++ [a] ++ P2).
    apply member_then_eq; auto.
    do 2 destruct H0.
    exists (x++x0).
    rewrite H0.
    solve_permutation.
  Qed.


  Lemma seconda_pri : forall L M M0 N a b,
      a <> b -> L =mul= a :: M -> L =mul= b :: (M0 ++ N) -> 
      exists L1 L2, M0 =mul= a :: L1 \/ N =mul= a :: L2 .
  Proof.
    intros L M M0 N a b Eq I1 I2.
    rewrite meq_cons_app in I1, I2.
    assert (exists L1 L2, M0 ++ N =mul= [a] ++ L1 /\ M =mul= [b] ++ L2 ).
    refine (seconda_sec _ _ _ _ _ Eq I1 I2 ).
    repeat destruct H.
    rewrite H in I2.
    rewrite H0 in I1.
    rewrite union_perm_left in I2.
    assert (x0 =mul= x).
    rewrite union_assoc_app in I1, I2.
    eapply meq_eq_s.
    exact I1.
    exact I2.
    auto.

    assert (a € (M0 ++ N)). 
    rewrite H. apply In_union_or. 
    right. apply In_to_in.  firstorder.
    apply In_union_or in H2.
    destruct H2;
      apply member_then_meq in H2;
      destruct H2.
    exists x1, x1.
    right; auto.
    exists x1, x1.
    left; auto.
  Qed.

  Lemma solsls : forall M N X a,
      M ++ N =mul= a :: X -> 
      (exists L1, M =mul= a :: L1 ) \/ (exists L2, N =mul= a :: L2).
  Proof.
    intros.
    assert (a € (M ++ N)). 
    rewrite H. apply member_insert_cons. 
    apply In_union_or in H0.
    destruct H0.
    apply member_then_meq in H0. 
    destruct H0. right.
    exists x; auto.
    apply member_then_meq in H0. 
    destruct H0. left.
    exists x; auto.   
  Qed.
  Arguments solsls [M N X a].
  #[export] Hint Resolve solsls : core .
  Lemma solsls2 : forall M N X Y a,
      M ++ N =mul= a :: Y -> 
      M =mul= a :: X -> Y =mul= N ++ X.
  Proof.
    intros M N X Y a P1 P2.
    symmetry in P1.
    rewrite P2 in P1.

    apply rem_to_union_app in P1.
    rewrite union_comm_app, P1.
    symmetry. apply rem_aM_cons. 
  Qed.

  Arguments solsls2 [M N X Y a].
  #[export] Hint Resolve solsls2: core.
  Lemma member_unit : forall a b,
      b = a <-> a € [b].
  Proof.
    split; intros.
    unfold member.
    simpl.
    destruct (eq_dec b a); auto.
    contradiction.
    apply In_to_in in H.
    firstorder.
  Qed.

  Lemma member_due : forall a b L,
      b <> a -> a € ([b] ++ L) -> a € L.
  Proof.
    intros a b L notExp H.
    apply In_union_or in H.
    destruct H as [a_L | a_b]; auto.
    apply member_unit in a_b.
    contradiction.
  Qed.

  Lemma se_i3 : forall A B,
      A = B <-> [A] =mul= [B].
  Proof.
    split; intros.
    -
      rewrite H; auto.
    -
      eapply  meq_cons_In in H.
      unfold member in H.
      apply countIn_In in H.
      inversion H.
      rewrite H0; auto.
      inversion H0.
  Qed. 

  Lemma se_i2 : forall A B L M,
      B = A -> ([A] ++ L =mul= [B] ++ M) -> [A] =mul= [B] /\ L =mul= M.
  Proof.
    intros.
    symmetry in H0.
    apply rem_to_union_app in H0.
    rewrite rem_abM_app in H0; auto.
    split; auto.
    apply se_i3; auto.
  Qed.
  
  Lemma se_i : forall A B L1 L2,
      [A] ++ L1 =mul= [A] ++ [B] ->
      [B] ++ L2 =mul= [A] ++ [B] -> L1 ++ L2 =mul= [A] ++ [B].
  Proof.
    intros.
    symmetry in H.
    apply rem_to_union_app in H.
    symmetry in H0.
    rewrite union_comm_app in H0.
    apply rem_to_union_app in H0.
    rewrite rem_aM_app in H, H0; auto.
    rewrite H, H0; rewrite union_comm_app; auto.
  Qed.

  Lemma aunion_comm : forall M L1 L2, M =mul= (L1 ++ L2) -> M =mul= (L2 ++ L1).
  Proof.
    intros.
    rewrite union_comm_app; auto.
  Qed.

  Lemma seconda_sec' : forall M M0 a b,
      b <> a -> a :: M =mul= b :: M0 -> 
      exists L, M0 =mul= a :: L /\  M =mul= b :: L.
  Proof.
    intros.
    change (a :: M =mul= b :: M0) with
    ([a] ++ M =mul= [b] ++ M0) in H0.
    remember ([a] ++ M).
    remember ([b] ++ M0).
    apply eq_then_meq in Heql.
    apply eq_then_meq in Heql0.
    rewrite H0 in Heql.
    assert(exists L1 L2, M0 =mul= [a] ++ L1 /\  M =mul= [b] ++ L2).
    refine ( seconda_sec _ _ _ _ _ _ Heql Heql0); auto.
    repeat destruct H1.
    assert (x =mul= x0).
    rewrite H1 in Heql0.
    rewrite H2 in Heql.
    rewrite union_assoc_app in Heql0, Heql.
    eapply meq_eq_s.
    exact Heql0. exact Heql. rewrite union_comm_app; auto.
    rewrite <- H3 in *.
    exists x; auto.
  Qed.

  Lemma seconda_pri' : forall M M0 N a b,
      a <> b -> a :: M =mul= b :: (M0 ++ N) -> 
      exists L1 L2, M0 =mul= a :: L1 \/ N =mul= a :: L2 .
  Proof.
    intros.
    change (a :: M =mul= b :: M0 ++ N) with
    ([a] ++ M =mul= [b] ++ M0 ++ N) in H0.
    remember ([a] ++ M).
    remember ([b] ++ (M0 ++ N)).
    apply eq_then_meq in Heql.
    apply eq_then_meq in Heql0.
    rewrite H0 in Heql.
    eapply seconda_pri; eauto. Qed.  

  (* Lemma union_empty : forall L a,
     [a] ++ L =mul= [a] -> L =mul= {}.
  Proof.
  intros.
  eapply rem_to_union in H.
  rewrite rem_a in H.
  auto.
Qed.  *)


  Lemma not_eq_in : forall x y M, y <> x -> 
                                  x € ([y] ++ M) ->  x € M.
  Proof.
    intros.
    apply In_union_or in H0.
    destruct H0; auto.
    apply member_unit in H0.
    contradiction.
  Qed.

  Lemma rem_not_abM a b M : b <> a -> rem a ([b] ++ M) =mul= [b] ++ rem a M.
  Proof.
    intros.
    simpl.
    destruct (eq_dec a b); auto.
    symmetry in e. contradiction.
  Qed.

  Lemma resolvers2: forall a b M, a :: M =mul= [b] -> b = a /\ M = [].
  Proof.
    intros.
    change (a :: M) with ([a] ++ M) in H.
    split.
    apply meq_cons_In in H;
      apply member_unit; auto.

    assert (M =mul= []).
    destruct (empty_dec M); auto.
    destruct (eq_dec a b);
      eapply rem_to_union_app in H.
    rewrite rem_abM_app in H; auto.
    rewrite rem_not_abM in H; auto.
    apply meq_multeq with (x:=a) in H.
    rewrite union_mult, singleton_mult_in in H; auto.
    simpl in H.
    inversion H.

    apply emp_mult in H0; auto.
  Qed.

  Lemma resolvers: forall a b c M, a :: M =mul= [b; c] -> 
                                   a = b \/ a = c.
  Proof.
    intros.
    assert ([a] ++ M =mul= [b] ++ [c]) by auto.
    symmetry in H.
    apply rem_to_union_app in H.

    (*  simpl in *. *)
    case (eq_dec a c); intros.
    right; auto.
    case (eq_dec a b); intros.
    left; auto.

    assert (exists L, [c] =mul= [a] ++ L /\  M =mul= [b] ++ L).

    eapply seconda_sec'; auto.
    repeat destruct H1.

    symmetry in H1.
    apply meq_cons_In in H1.
    apply member_unit in H1.
    right; auto.
  Qed.

  Lemma resolvers3: forall a b, [a] =mul= [b] <-> b = a.
  Proof.
    split; intros; subst; auto.
    apply meq_cons_In in H;
      apply member_unit; auto.
  Qed.

  Lemma MulSingleton : forall F M, [F] =mul= M -> M = [F].
  Proof.
    induction M; intros.
    *
      apply emp_mult in H; auto.
    *
      symmetry in H. apply resolvers2 in H.
      destruct H; subst; auto.
  Qed.

  Lemma DestructMulFalse l L : l :: L =mul= [] -> False.
  Proof.
    intro H. 
    assert (l :: L =mul= []) by auto.
    symmetry in H. 
    eapply rem_to_union_app in H. simpl in H. 
    rewrite H in H0.
    eapply singleton_notempty; eauto.
  Qed.

  Lemma permut_remove_hd :
    forall l l1 l2 a,
      [a] ++ l =mul= l1 ++ ([a] ++ l2) -> l =mul= l1 ++ l2.
  Proof.
    intros.
    symmetry in H.
    apply rem_to_union_app in H.
    rewrite H.
    rewrite union_perm_left.
    rewrite rem_aM_app; auto.
  Qed.

  Lemma Permutation_meq :
    forall M N, Permutation M N <-> M =mul= N.
  Proof.
    split; intros H.
    - 
      induction H; intros; eauto.
    - 
      revert N H.
      induction M; intros.
      symmetry in H.
      rewrite  emp_mult in H; subst; auto.
      assert (a :: M =mul= N) by apply H.
      apply meq_cons_In in H.
      apply In_to_in in H.
      destruct (In_split _ _ H) as (h2,(t2,H1)).
      subst N.
      apply Permutation_cons_app.
      apply IHM.
      eapply permut_remove_hd with a; auto.
  Qed.

  Lemma right_union : forall L M a,
      a :: L =mul= a :: M -> L =mul= M.
  Proof.
    intros.
    eapply rem_to_union_app in H.
    rewrite rem_aM_cons in H.
    auto.
  Qed.

  Lemma DestructMSet: forall F G M1 M2,
      F :: M1 =mul= G :: M2 ->
      (( F = G /\ M1 =mul= M2 )  \/
       exists M2', M2 =mul= F :: M2' /\ M1 =mul= G :: M2').
  Proof.
    intros.
    destruct (eq_dec F G).
    - left.
      rewrite e in H.
      apply right_union in H; auto.
    - right.
      apply seconda_sec'; auto.
  Qed.


  Lemma DestructMSet2_aux a L M: L =mul= [a] ++ M -> 
                                 exists T1 T2, L = T1 ++ [a] ++ T2.
  Proof.
    intros.
    induction M.
    - rewrite app_nil_r in H. 
      symmetry in H.
      apply MulSingleton in H.  
      do 2 eexists [].
      simpl; auto.
    - assert (member a L) as Hm.
      rewrite H.
      apply In_union_or.
      right. apply member_unit; auto.
      apply member_then_eq in Hm.
      auto.
  Qed.

  Lemma DestructMSet2' l L l' L' x:  L =mul= l' :: x -> L' =mul= l :: x ->
                                     (exists L1 L2 L1' L2', L= L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2').
  Proof.
    intros.
    apply DestructMSet2_aux in H.
    apply DestructMSet2_aux in H0.
    do 2 destruct H.
    do 2 destruct H0.
    exists x0, x1, x2, x3.
    auto.
  Qed.

  Lemma DestructMSet2 : forall l L l' L', l :: L =mul= l' :: L' ->
                                          (l = l' /\ L =mul= L') \/
                                          (exists L1 L2 L1' L2', L= L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2' /\ L1 ++ L2 =mul= L1' ++ L2' ) .
  Proof.
    intros.
    destruct (eq_dec l l'); [left | right].
    * rewrite e in H.
      apply right_union in H; auto.
    *
      eapply seconda_sec' in H; auto.
      do 2 destruct H.
      assert (L' =mul= l :: x) by auto.
      assert (L =mul= l' :: x) by auto.

      apply DestructMSet2_aux in H.
      apply DestructMSet2_aux in H0.
      do 2 destruct H.
      do 2 destruct H0.
      exists x2, x3, x0, x1.
      split; auto.
      split; auto.
      rewrite H0 in H2.
      rewrite H in H1.
      rewrite union_perm_left in H2, H1.
      apply right_union in H1.
      apply right_union in H2.
      rewrite H1, H2; auto.
  Qed.

  Lemma EmptyMS : forall a (M:list A), [] <> M ++ [a].
  Proof.
    intros; intro.
    symmetry in H.
    apply app_eq_nil in H.
    inversion H.
    inversion H1.
  Qed.

  Lemma meq_cons_append : forall l x,
      (x :: l) =mul= (l ++ x :: nil).
  Proof.
    intros.
    solve_permutation.
  Qed.


End MultisetList.
