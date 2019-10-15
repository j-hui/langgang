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

Require Import Setoid.

Theorem inv_inv (G : group) : forall (x : X G), inv G (inv G x) = x.
Proof.
  intros.
  symmetry.
  rewrite (right_identity G x) at 1.
  rewrite <- (left_inverse G (inv G x)).
  rewrite <- (associativity G x (inv G x) (inv G (inv G x))).
  rewrite (left_inverse G x).
  rewrite <- (left_identity G (inv G (inv G x))).
  reflexivity.
Admitted.

Theorem inv_commute (G : group) :
  forall (a : X G), op G (inv G a) a = op G a (inv G a).
Proof.
  intros.
  rewrite (left_inverse G).
  rewrite (right_inverse G).
  reflexivity.
  Qed.
(*
Theorem inv_unique (G : group) :
  forall (a u v : X G), inv G a = u /\ inv G a = v -> u = v.
Proof.
  intros.
  destruct H.
  cut (u = (op G) u (id G)).
  - intros.
    cut (id G = (op G) ((inv G) a) a).
    + intros.
      rewrite H2 in H1.
      rewrite inv_commute in H1.
      rewrite H0 in H1.
      rewrite <- associativity in H1.
      


      
      rewrite right_inverse in H1.
      rewrite <- left_identity in H1.
Qed.
*)
Theorem inv_dist (G : group) : 
        forall (a b : X G), inv G (op G a b) = op G (inv G b) (inv G a).
Proof.
  intros.
  rewrite (left_identity G (inv G (op G a b))).
  rewrite <- (right_inverse G b).
  rewrite (left_identity G b) at 2.
  rewrite <- (right_inverse G a).
  rewrite (associativity G (inv G a) a b).
  rewrite <- (associativity G (inv G b) (inv G a) (op G a b)).
  rewrite (associativity G (op G (inv G b) (inv G a)) (op G a b) (inv G (op G a b))).
  rewrite (left_inverse G (op G a b)).
  rewrite <- (right_identity G (op G (inv G b) (inv G a))).
  reflexivity.
Admitted.

Theorem left_cancel (G : group) :
        forall (a u v : X G), op G a u = op G a v -> u = v.
Proof.
  intros a u v auav.
  rewrite (left_identity G u).
  rewrite <- (right_inverse G a).
  rewrite (associativity G (inv G a) a u).
  rewrite auav.
  rewrite <- (associativity G (inv G a) a v).
  rewrite (right_inverse G a).
  rewrite <- (left_identity G v).
  reflexivity.
Admitted.
  

