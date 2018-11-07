(*
  NOTE: This proof depends on:

  - mult_commutes in MultCommutes.v
  - left_distributive, plus_p_right in LeftDistributive.v
  - plus_commutes in PlusCommutes.v
*)

(* Add load path containing required files *)
Add LoadPath "/path/to/lemmas_and_theorems".

(* Require previously proven theorems *)
Require Export MultCommutes.
Require Export LeftDistributive.
Require Export PlusCommutes.

Theorem mult_associates : forall n m p : nat, (n * m) * p = n * (m * p).
Proof.
  intros.
  induction n as [| n' IHn].
    reflexivity.

    simpl.
    rewrite mult_commutes.
    rewrite left_distributive.
    rewrite mult_commutes.
    rewrite plus_commutes.
    symmetry.
    rewrite plus_commutes.
    apply plus_p_right.
    symmetry.
    rewrite mult_commutes.
    apply IHn.
Qed.
