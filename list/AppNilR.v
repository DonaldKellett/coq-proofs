Require Import List.

Theorem app_nil_r : (forall A:Type, (forall l:list A, forall l:list A, l ++ nil = l)).
Proof.
  intros.
  induction l0.
    simpl.
    reflexivity.

    simpl.
    rewrite IHl0.
    reflexivity.
Qed.
