Add LoadPath "../".

(*****************)
(* DYADIC SYSTEM *)
(*****************)

Require Import LL.SequentCalculi.
Require Import LL.Focusing.TriSystem.

Example ex1 : |-- []; [1 ; ⊥].
eapply sig2_bot;auto.
eapply sig2_one;auto.
Qed.

Example ex2: forall a b, |-- [] ; [? (a ⁻) $  ? (b ⁻) $ (a ⁺ ** ! b ⁺)].
intros.
do 2 (eapply sig2_par;auto). 
do 2 (eapply sig2_quest;auto).
eapply sig2_tensor with (M:=[]) (N:=[]);auto.
+ eapply sig2_copy with (F:= a ⁻);auto.
  eapply sig2_init;auto.
+ eapply sig2_bang;auto.
  eapply sig2_copy with (F:= b ⁻);auto.
  eapply sig2_init;auto.
Qed.

(************)
(* FOCUSING *)
(************)
Example ex1F : exists n, n |-F- []; [] ; UP [1 ; ⊥].
eexists. (* number of steps *)
eapply tri_store;auto.
eapply tri_bot.
eapply tri_dec1 with (F:=1);auto.
eapply tri_one.
Qed.

Example ex2F: forall a b, exists n, n |-F- [] ; [] ; UP [? (a ⁻) $  ? (b ⁻) $ (a ⁺ ** ! b ⁺)].
intros.
eexists.
eapply tri_par.
eapply tri_quest.
eapply tri_par.
eapply tri_quest.
eapply tri_store;auto.
simpl.
eapply tri_dec1 with (F:=a ⁺ ** (! b ⁺)) ;auto.
eapply tri_tensor with (M:=[]) (N:=[]);auto.
eapply tri_init2;auto.
eapply tri_bang;auto.
eapply tri_store;auto.
simpl.
eapply tri_dec1 with (F:=b ⁺);auto.
eapply tri_init2;auto.
Qed.




