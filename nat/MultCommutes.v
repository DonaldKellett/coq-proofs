(*
  NOTE: This proof depends on:

  - plus_associates (defined in PlusAssociates.v)
  - plus_commutes (defined in PlusCommutes.v)
  - plus_p_right (defined in LeftDistributive.v)
*)

(*
  Add load path containing the files mentioned above -
  feel free to edit path as required
*)
Add LoadPath "/path/to/lemmas_and_theorems".

(* Require the theorems and lemmas mentioned above *)
Require Export PlusAssociates.
Require Export PlusCommutes.
Require Export LeftDistributive.

Lemma n_times_S_m_eq_n_plus_n_times_m : forall n m : nat, n * S m = n + n * m.
Proof.
  intros.
  induction n as [| n' IHn].
    reflexivity.

    simpl.
    rewrite IHn.
    apply f_equal.
    rewrite <- plus_associates.
    symmetry.
    rewrite <- plus_associates.
    apply plus_p_right.
    apply plus_commutes.
Qed.

Theorem mult_commutes : forall n m : nat, n * m = m * n.
Proof.
  intros.
  induction n as [| n' IHn].
    simpl.
    induction m as [| m' IHm].
      reflexivity.

      simpl.
      assumption.

    simpl.
    rewrite IHn.
    rewrite n_times_S_m_eq_n_plus_n_times_m.
    reflexivity.
Qed.
