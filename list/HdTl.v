Require Import List.

Theorem hd_tl : 
   (forall A:Type, 
   (forall (default : A) (x : A) (lst : list A), 
   (hd default (x::lst)) :: (tl (x::lst)) = (x :: lst))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
