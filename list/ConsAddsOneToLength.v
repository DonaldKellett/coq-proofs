Require Import List.

Theorem cons_adds_one_to_length : 
   (forall A:Type, 
   (forall (x : A) (lst : list A), 
   length (x :: lst) = (S (length lst)))).
Proof.
  intros.
  induction lst.
    simpl.
    reflexivity.

    simpl.
    reflexivity.
Qed.
