Require Import lambda2.
Import Nat.
Require Import List.
Import List.ListNotations.
(*  ===============================Examples================================*)

Definition t1 := &0.
Definition t2 := (&0) >> (&1).
Definition t3 := Pi 0 (&0 >> &1).

Compute FVb 0 t1.
Compute FVb 1 t1.

Compute FVb 0 t2.

Compute FVb 0 t3.
Compute FVb 1 t3.

Compute FVl t2.
Compute FVl t3.


Definition M := #0.
Definition N := #1.
Definition app := M!N.
Definition tapp := M!!t1.
Definition abs := Abs 0 t1 M.
Definition tabs := Tabs 0 M.

Compute app.
Compute abs.

Definition d1 := (0 :* t1).
Definition d2 := (TStd 1).

Compute dec2st d1.
Compute dec2st d2.

Definition G1 := [TStd 0; 1 :* t1].

Compute check_type G1 0.
Compute check_term G1 0.
Compute check_term G1 1.

Example cntxt2 : l2_context [1 :* (&0); TStd 0].
Proof.
  constructor; auto.
  + constructor; auto. constructor.
  + simpl. reflexivity.
Qed.


Compute subs ((&0) >> (&1)) 0 (&2). 
Compute subs (Pi 0 (&0 >> &1)) 0 (&2).

Example var_typing : [0 :* &0; TStd 0] ⊢ (#0 :# &0).
Proof.
  constructor.
  + repeat constructor.
  + simpl. left. trivial.
Qed.