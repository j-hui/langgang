module MyNat

plus_commutes_Z : m = plus m 0
plus_commutes_Z {m = Z} = Refl
plus_commutes_Z {m = (S k)} = let r = plus_commutes_Z {m=k} in
                              rewrite sym r in
                              Refl

plus_commutes_S : (k : Nat) -> (m : Nat) -> (r : (k + m) = (m + k)) -> S (plus k m) = plus m (S k)
plus_commutes_S k Z r = rewrite r in Refl
plus_commutes_S k (S j) r = ?plus_commutes_S_rhs_2

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z m = plus_commutes_Z
plus_commutes (S k) m = let r = plus_commutes k m in
                            plus_commutes_S k m r

