module NatAddAssoc

plus_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x + y) + z = x + (y + z)
plus_assoc Z y z = Refl
plus_assoc (S x') y z = let r = plus_assoc x' y z in
                        rewrite r in
                        Refl
