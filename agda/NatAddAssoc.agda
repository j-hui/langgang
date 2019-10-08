module NatAddAssoc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

assoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
assoc zero b c =
  begin
    (zero + b) + c
  ≡⟨⟩
    b + c
  ≡⟨⟩
    zero + (b + c)
  ∎
assoc (suc a) b c =
  begin
    (suc a + b) + c
  ≡⟨⟩
    suc (a + b) + c
  ≡⟨⟩
    suc ((a + b) + c)
  ≡⟨ cong suc (assoc a b c) ⟩
    suc (a + (b + c))
  ≡⟨⟩
    suc a + (b + c)
  ∎
