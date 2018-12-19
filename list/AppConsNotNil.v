Require Import List.

Theorem app_cons_not_nil : forall A (x y:list A) (a:A), nil <> x ++ a :: y.
Proof.
  unfold not.
  intros.
  induction x.
    discriminate H.

    discriminate H.
Qed.
