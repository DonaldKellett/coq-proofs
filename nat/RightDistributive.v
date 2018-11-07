(*
  NOTE: This proof depends on:

  - mult_commutes in MultCommutes.v
  - left_distributive, plus_p_right in LeftDistributive.v
  - plus_commutes in PlusCommutes.v
*)

(*
  Add load path containing required files -
  feel free to edit path as necessary
*)
Add LoadPath "/path/to/lemmas_and_theorems".

(* Require lemmas and theorems *)
Require Export MultCommutes.
Require Export LeftDistributive.
Require Export PlusCommutes.

Theorem right_distributive : forall n m p : nat, (n + m) * p = n * p + m * p.
Proof.
  intros.
  rewrite mult_commutes.
  rewrite left_distributive.
  rewrite mult_commutes.
  rewrite plus_commutes.
  symmetry.
  rewrite plus_commutes.
  apply plus_p_right.
  rewrite mult_commutes.
  reflexivity.
Qed.
