(*
  NOTE: This proof depends on plus_commutes and plus_associates
  defined in PlusCommutes.v and PlusAssociates.v
*)

(*
  Add the load path containing the two theorems -
  feel free to edit the load path accordingly
*)
Add LoadPath "/path/to/folder/containing/PlusCommutesAndPlusAssociates".

(* Require the two theorems mentioned above *)
Require Export PlusCommutes.
Require Export PlusAssociates.

(* A useful lemma for the proof below *)
Lemma plus_p_right : forall n m p : nat, n = m -> n + p = m + p.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(*
  Multiplication of natural numbers distributes
  over addition to the left, i.e. a(b + c) = ab + ac
*)
Theorem left_distributive : forall n m p : nat, n * (m + p) = n * m + n * p.
Proof.
  intros.
  induction n as [| n' IHn].
    reflexivity.

    simpl.
    rewrite IHn.
    symmetry.
    rewrite plus_associates.
    rewrite plus_commutes.
    symmetry.
    rewrite plus_associates.
    rewrite plus_commutes.
    rewrite <- plus_associates.
    symmetry.
    rewrite <- plus_associates.
    apply plus_p_right.
    apply plus_p_right.
    apply plus_commutes.
Qed.
