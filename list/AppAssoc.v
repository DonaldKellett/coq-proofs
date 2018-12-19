Require Import List.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
    simpl.
    reflexivity.

    simpl.
    rewrite IHl.
    reflexivity.
Qed.
