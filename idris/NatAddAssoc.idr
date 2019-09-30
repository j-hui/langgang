module NatAddAssoc

data MyNat = MZ | MS MyNat

myplus : MyNat -> MyNat -> MyNat
myplus MZ     y = y
myplus (MS k) y = MS (myplus k y)

(+) : MyNat -> MyNat -> MyNat
(+) = myplus

natAddAssoc : (a:MyNat) -> (b:MyNat) -> (c:MyNat) -> (a + b) + c = a + (b + c)
