(*
  Zero is a two-sided identity
  Note that the proof that zero is a left identity is trivial
  as it is explicitly stated by Peano's axioms
  So we only need to prove that it is a right identity
*)
Lemma O_rid_plus : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| k IHn].
    (* Base case - when n = 0, the identity is trivial *)
    reflexivity.

    (* Inductive case *)
    simpl. (* using Peano's axioms *)
    rewrite IHn. (* assuming our theorem holds for n = k *)
    reflexivity. (* it holds for n = k + 1 as well *)
Qed.

(*
  Proof that n + S m = S (n + m)
  This is extremely useful for proving the commutativity
  of addition on the natural numbers
*)
Lemma n_plus_S_m_eq_S_n_plus_m : forall n m : nat, n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| k IHn].
    (* Base case: n = 0 *)
    simpl. (* Using Peano's axioms on both sides *)
    reflexivity.

    (* Inductive case *)
    simpl. (* Using Peano's axioms on both sides *)
    rewrite IHn. (* Assuming our hypothesis is true for n = k *)
    reflexivity. (* Then it is also true for n = k + 1 *)
Qed.

(*
  The addition of the natural numbers is commutative
  This is the main theorem we want to prove
*)
Theorem plus_commutes : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| k IHn].
    (* Base case: n = 0 *)
    simpl. (* Using Peano's axioms on the LHS (the RHS requires a lemma) *)
    symmetry. (* Flip LHS and RHS to apply our lemma *)
    apply O_rid_plus. (* Apply our first lemma *)

    (* Inductive case *)
    simpl. (* Using Peano's axioms on the LHS (the RHS requires a lemma) *)
    rewrite IHn. (* Assuming our hypothesis holds true for n = k *)
    symmetry. (* Flip LHS and RHS to apply lemma *)
    apply n_plus_S_m_eq_S_n_plus_m. (* Apply our second lemma *)
Qed.
