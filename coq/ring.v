Structure ring := {
    X :> Set;
    
    add_id : X;
    add : X -> X -> X;
    mult : X -> X -> X;
    add_inv : X -> X;

    (* Additive abelian group *)
    associativity : forall (x y z : X), add (add x y) z = add x (add y z);
    left_inverse : forall (x : X), add x (add_inv x) = add_id;
    right_inverse : forall (x : X), add (add_inv x) x = add_id;
    left_identity : forall (x : X), x = add add_id x;
    right_identity : forall (x : X), x = add x add_id;
    commutativity : forall (x y : X), add x y = add y x;

    (* Multiplicative criteria *)
    mult_associativity : forall (x y z : X), mult (mult x y) z 
        = mult x (mult y z);
    mult_distributivity : forall (x y z : X), mult (add x y) z
        = add (mult x z) (mult y z);
}.
