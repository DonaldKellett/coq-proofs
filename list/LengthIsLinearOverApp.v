Require Import List.

Theorem length_is_linear_over_app :
  forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
    simpl.
    reflexivity.

    simpl.
    rewrite IHl1.
    reflexivity.
Qed.
