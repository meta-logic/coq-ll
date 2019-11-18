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


(** A simple transition system  s1 -> s2, s2 -> s3*)

Example TS : forall s1 s2 s3,
    exists n, n |-F- [ (s1 ⁺) ** (s2 ⁻) ; (s2 ⁺) ** (s3 ⁻) ] ; [] ; UP [(s1 ⁺) -o (s3 ⁺)] .
Proof with auto ; try solver_permute.
  intros.
  eexists.
  unfold imp;simpl.
  eapply tri_par.
  do 2(apply tri_store;auto);simpl.
  eapply tri_dec2 with (F:= s1 ⁺ ** s2 ⁻)...
  eapply tri_tensor with (N:=  [s1 ⁻]) (M:=  [s3 ⁺])...
  eapply tri_init1.
  eapply tri_rel...
  eapply tri_store...
  eapply tri_dec2 with (F:= s2 ⁺ ** s3 ⁻)...
  eapply tri_tensor with (N:=  [s2 ⁻]) (M:=  [s3 ⁺])...
  eapply tri_init1.
  eapply tri_rel...
  eapply tri_store...
  eapply tri_dec1 with (F:= s3 ⁺)...
  eapply tri_init1.
Qed.

(** Producing n tokens:
- Rules: from a produces 2 bs ; from b produce to as.
- Goal: from a produce b a a 
 *)
Example Tokens : forall a b,
    exists n, n |-F- [ (a ⁺) ** ((b ⁻) $ (b ⁻) )  ; (b ⁺) ** ((a ⁻) $ (a ⁻) ) ] ; [ ] ; UP [(a ⁺) -o ( (b ⁺) ** (a ⁺) ** (a ⁺)) ] .
Proof with auto ; try solver_permute.
  intros.
  eexists.
  eapply tri_par.
  do 2(apply tri_store;auto);simpl.
  eapply tri_dec2 with (F:= a ⁺ ** (b ⁻ $ b ⁻))...
  eapply tri_tensor with (N:=  [a ⁻ ]) (M:= [(b ⁺) ** (a ⁺) ** (a ⁺)])...
  eapply tri_init1.
  eapply tri_rel...
  eapply tri_par.
  do 2(apply tri_store;auto);simpl.
  eapply tri_dec2 with (F:= b ⁺ ** (a ⁻ $ a ⁻))...
  eapply tri_tensor with (N:=  [b ⁻ ]) (M:= [(b ⁺) ** (a ⁺) ** (a ⁺); b ⁻])...
  eapply tri_init1.
  eapply tri_rel...
  eapply tri_par.
  do 2(apply tri_store;auto);simpl.
  eapply tri_dec1 with (F:= (b ⁺) ** (a ⁺) ** (a ⁺))...
  eapply tri_tensor with (N:= [b ⁻; a ⁻]) (M:= [a ⁻])...
  eapply tri_tensor with (N:= [b ⁻]) (M:= [a ⁻])...
  eapply tri_init1.
  eapply tri_init1.
  eapply tri_init1.
Qed.







