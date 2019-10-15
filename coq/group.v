Load naturals.

Structure group := {
    X :> Set;
    
    id : X;
    op : X -> X -> X;
    inv : X -> X;

    associativity : forall (x y z : X), op (op x y) z = op x (op y z);
    left_inverse : forall (x : X), op x (inv x) = id;
    right_inverse : forall (x : X), op (inv x) x = id;
    left_identity : forall (x : X), x = op id x;
    right_identity : forall (x : X), x = op x id;
}.

Fixpoint applyN (X : Type) (x : X) (op : X -> X -> X) (n : N) : X :=
  match n with
    (* Wrong base case; can't get to id *)
  | O => id
  | S n' => op x (applyN x op n')
  end.

Theorem inv_inv (G : group) : forall (g : A G), inv (inv g) = g.
Proof.
  Qed.


Theorem inv_dist (G : group) : 
        forall (a b : X G), inv (op a b) = op (inv a) (inv b).
Proof.
  Qed.

