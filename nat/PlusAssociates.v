(* The addition of the natural numbers is associative *)
Theorem plus_associates : forall n m p : nat, (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction n as [| n' IHn].
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
Qed.