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

Theorem inv_unique (G : group) :
  forall (a u v : X G), inv G a = u /\ inv G a = v -> u = v.
Proof.
Admitted.

Theorem inv_inv (G : group) : forall (g : X G), inv G (inv G g) = g.
Proof.
Admitted.

Theorem inv_dist (G : group) : 
        forall (a b : X G), inv G (op G a b) = op G (inv G a) (inv G b).
Proof.
Admitted.

Theorem left_cancel (G : group) :
        forall (a u v : X G), op G a u = op G a v -> u = v.
Proof.
Admitted.
  

