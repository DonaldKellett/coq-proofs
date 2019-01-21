(*
  KnightsOnAChessboard.v

  In international chess, a knight is a chess piece which can
  move 2 squares in any of the 4 cardinal directions followed
  by either a left or right turn of 1 square.  This means that
  each move of a knight traces an L-shape on the chessboard.
  An interesting consequence of this movement pattern is that
  it allows a knight to effectively jump past any chess piece
  which may be blocking its way, making it the only chess piece
  in international chess to possess this ability.

  However, what is even more interesting is that this movement
  pattern actually allows a knight to reach any square within
  the given chessboard, only subject to the condition that no
  same-color chess piece is occupying its desired square.  This
  is what the given file seeks to prove, extending the statement
  beyond the typical 8x8 chessboard to an infinite chessboard
  stretching both rightwards and upwards.
*)

(*
  Enable argument inference to hide arguments for universal
  instantiation, making proof more readable
*)
Set Implicit Arguments.

(* All possible legal moves of a knight *)
Inductive KnightCanReach : nat * nat -> Prop :=
  | NoMoves : KnightCanReach (0, 0)
  | MoveRL : forall n m : nat, KnightCanReach (n, m) -> KnightCanReach (S (S n), S m)
  | MoveRR : forall n m : nat, KnightCanReach (n, S m) -> KnightCanReach (S (S n), m)
  | MoveUL : forall n m : nat, KnightCanReach (S n, m) -> KnightCanReach (n, S (S m))
  | MoveUR : forall n m : nat, KnightCanReach (n, m) -> KnightCanReach (S n, S (S m))
  | MoveLL : forall n m : nat, KnightCanReach (S (S n), S m) -> KnightCanReach (n, m)
  | MoveLR : forall n m : nat, KnightCanReach (S (S n), m) -> KnightCanReach (n, S m)
  | MoveDL : forall n m : nat, KnightCanReach (n, S (S m)) -> KnightCanReach (S n, m)
  | MoveDR : forall n m : nat, KnightCanReach (S n, S (S m)) -> KnightCanReach (n, m)
.

(*
  A knight can reach any desired square on a(n) (potentially
  infinite) chessboard through a series of legal moves starting
  from the leftmost corner of the chessboard, defined as the
  origin (0, 0)
*)
Theorem knight_can_go_anywhere :
  forall square : nat * nat, KnightCanReach square.
Proof.
  intros square.
  destruct square as [n m].
  induction n.
    induction m.
      exact NoMoves.

      exact (MoveDR (MoveUL (MoveRL IHm))).

    exact (MoveLL (MoveRR (MoveUR IHn))).
Qed.