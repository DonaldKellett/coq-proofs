Require Import List.

Theorem correctness_of_hd : 
   (forall A:Type, 
   (forall (default : A) (x : A) (lst : list A), 
   (hd default nil) = default /\ (hd default (x :: lst)) = x)).
Proof.
  intros.
  refine (conj _ _).
    simpl.
    reflexivity.

    simpl.
    reflexivity.
Qed.
