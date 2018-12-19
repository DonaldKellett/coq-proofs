Require Import List.

Fixpoint tl_error (A : Type) (l : list A) : option (list A) :=
  match l with
    | nil => None
    | _ :: l' => Some l'
  end
.

Theorem tl_error_is_correct :
  forall (A : Type) (x : A) (lst : list A),
  (tl_error A (nil : list A) = None) /\ (tl_error A (x :: lst) = Some lst).
Proof.
  intros.
  refine (conj _ _).
    simpl.
    reflexivity.

    simpl.
    reflexivity.
Qed.
