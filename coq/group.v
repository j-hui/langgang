Load naturals.

Structure group := {
    X : Type;
    id : X;
    op : X -> X -> X;
    inv : X -> X;

    associativity : forall (x y z : X), op (op x y) z = op x (op y z);
    left_inverse : forall (x : X), op x (inv x) = id;
    right_inverse : forall (x : X), op (inv x) x = id;
    left_identity : forall (x : X), x = op id x;
    right_identity : forall (x : X), x = op x id;
}.


Check inv.
Check op.
Fixpoint applyN (G : group) (x : X G) (n : N) : X G :=
  match n with
  | O => id G
  | S n' => op G x (applyN G x n')
  end.

Theorem inv_inv (G : group) : forall (g : X G), inv G (inv G g) = g.
Proof.
  intros.
  simpl.
Qed.


Theorem inv_dist (G : group) : 
        forall (a b : X G), inv (op a b) = op (inv a) (inv b).
Proof.
  Qed.

Theorem left_cancel (G : group) :
        forall (a u v : X), op a u = op a v -> u = v.
Proof.
  Qed.

