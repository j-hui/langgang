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
