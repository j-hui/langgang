module SimpleTypes where

infix 10 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
