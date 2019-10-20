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
assoc zero b c = refl
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

rident : ∀ (m : ℕ) → m + zero ≡ m
rident zero = refl
rident (suc m) =
  begin
    suc m + zero ≡⟨⟩ suc (m + zero)
  ≡⟨ cong suc (rident m) ⟩
    suc m
  ∎

rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
rsuc zero n = refl
rsuc (suc m) n =
  begin
    suc m + suc n ≡⟨⟩ suc (m + suc n)
  ≡⟨ cong suc (rsuc m n) ⟩
    suc (suc m + n)
  ∎

comm : ∀ (m n : ℕ) → m + n ≡ n + m
comm zero n =
  begin
    zero + n ≡⟨⟩ n
  ≡⟨ sym (rident n) ⟩
    n + zero
  ∎
comm (suc m) n =
  begin
    suc m + n ≡⟨⟩ suc (m + n)
  ≡⟨ cong suc (comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (rsuc n m) ⟩
    n + suc m
  ∎
