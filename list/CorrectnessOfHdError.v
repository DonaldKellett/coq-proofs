Require Import List.

Theorem correctness_of_hd_error : 
   (forall A:Type, 
   (forall (x : A) (lst : list A), 
   (hd_error nil : option A) = None /\ (hd_error (x :: lst)) = Some x)).
Proof.
  intros.
  refine (conj _ _).
    simpl.
    reflexivity.

    simpl.
    reflexivity.
Qed.
