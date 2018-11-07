## nat

Simple proofs involving the natural numbers as formulated by Peano's axioms.

### Synopsis

- `PlusCommutes.v` - A proof `plus_commutes` of the commutativity of addition of the natural numbers.  Also contains two lemmas, namely `O_rid_plus : forall n : nat, n + 0 = n` and `n_plus_S_m_eq_S_n_plus_m : forall n m : nat, n + S m = S (n + m)`.
- `PlusAssociates.v` - A proof `plus_associates` of the associativity of addition of the natural numbers.
- `LeftDistributive.v` - A proof `left_distributive` that multiplication distributes over addition to the left on the natural numbers.  Also contains a lemma `plus_p_right : forall n m p : nat, n = m -> n + p = m + p`.  **This proof depends on `plus_commutes` and `plus_associates`; make sure to require `PlusCommutes` and `PlusAssociates` before compiling this file.**
- `MultCommutes.v` - A proof `mult_commutes` of the commutativity of multiplication of the natural numbers.  Also contains a lemma `n_times_S_m_eq_n_plus_n_times_m : forall n m : nat, n * S m = n + n * m`.  **This proof depends on `plus_commutes`, `plus_associates` and `plus_p_right`; make sure to require `PlusCommutes`, `PlusAssociates` and `LeftDistributive` before compiling this file.**
- `MultAssociates.v` - A proof `mult_associates` of the associativity of multiplication of the natural numbers.  **This proof depends on `plus_commutes`, `mult_commutes`, `left_distributive` and `plus_p_right`; make sure to require `PlusCommutes`, `LeftDistributive` and `MultCommutes` before compiling this file.**
