(* This file is part of the Linear Logic formalization in Coq:
https://github.com/brunofx86/LL *)

(** ** Strong Induction

Most of the proofs in this library require the strong induction
principle. This file defines such principle.
 *)

Section StrongIndPrinciple.

  Variable P: nat -> Prop.

  Hypothesis P0: P O.

  Hypothesis Pn: forall n, (forall m, m<=n -> P m) -> P (S n).
  
  Lemma strind_hyp : forall n, (forall m, ((m <= n) -> P m)).
  Proof.
    induction n; intros m H;inversion H;auto.
  Qed.
  (** Strong induction principle *)
  Theorem strongind: forall n, P n.
  Proof. 
    induction n; auto.
    apply Pn.
    apply strind_hyp.
  Qed.

End StrongIndPrinciple.