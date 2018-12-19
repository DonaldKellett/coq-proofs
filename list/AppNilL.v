Require Import List.

Theorem app_nil_l : (forall A:Type, (forall l:list A, nil ++ l = l)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
