Require Import List.

Theorem tl_is_correct :
  forall (A : Type) (x : A) (lst : list A),
  (tl nil = (nil : list A)) /\ (tl (x :: lst) = lst).
Proof.
  intros.
  refine (conj _ _).
    simpl.
    reflexivity.

    simpl.
    reflexivity.
Qed.
