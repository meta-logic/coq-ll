(* This file is part of the Linear Logic  formalization in Coq: https://github.com/meta-logic/coq-ll *)

(** ** Auxiliar Results

Some arithmetic results needed in the proofs. 
*)


Require Import Arith.

Lemma GtZero : forall n, n >0 -> exists n', n = S n'.
Proof.
  intros.
  destruct n.
  inversion H.
  exists n;auto.
Qed.


Lemma plus_le_reg_r: forall n m q : nat, n + q <= m + q -> n <= m.
Proof.
  intros.
  assert (n+q = q + n) by (apply plus_comm).
  assert (m+q = q + m) by (apply plus_comm).
  rewrite H0 in H. rewrite H1 in H.
  eapply plus_le_reg_l in H.
  assumption.
Qed.
