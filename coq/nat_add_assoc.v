Inductive nat : Type :=
  | O : nat
  | S (n: nat): nat.

Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Theorem nat_add_assoc : forall (a b c:nat), (a + b) + c = a + (b + c).
Admitted.
