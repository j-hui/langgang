

variable f : ℕ → ℕ 
variable h : ∀ x : ℕ, f x ≤ f (x + 1)

example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 0 ≤ f 2, from le_trans this (h 1),
    show f 0 ≤ f 3, from le_trans this (h 2)

#check le_trans (h 0) (h 1)

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
apply and.intro,
    exact hp,
apply and.intro,
    exact hq,
exact hp
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
    intros a b c ab ac,
    rewrite ← ac,
    exact ab
end


#check λ x y z, z + y + x

#print definition list.append
#print notation +
#print has_add
#print classes has_add

example : f 0 ≤ f 3 :=
calc
    f 0     ≤ f 1 : h 0
    ...     ≤ f 2 : le_trans (h 0) (h 1)
    ...     ≤ f 3 : le_trans (f 0 ≤ f 2) (h 3)


    have f 0 ≤ f 1, from h 0,
    have f 0 ≤ f 2, from le_trans this (h 1),
    show f 0 ≤ f 3, from le_trans this (h 2)

variables (α : Type) (p q : α → Prop)

example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
(λ w : α,
 λ hw : p w ∧ q w,
show (∃ x, q x ∧ p x), from ⟨w, hw.right, hw.left⟩)

#check exists.elim

example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
(assume w, assume hw : p w ∧ q w,
show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with
| ⟨ w, hw ⟩ := ⟨ w, hw.right, hw.left⟩ 
end


#check Prop
#check Sort
#check Sort 0
#check Type

/- α : Sort i
 - β : Sort j -- β depends on x : α
 - (Π x : α, β) : Type imax i j
 -/
 
universe i
universe j
constant α : Sort i
constant β : Sort j

definition imax (x y: nat) : nat :=
    if y = 0 then 0 else
    if x > y then x else
    y

#check (Π x : α, β)


namespace hidden

universe u

constant list   : Type u → Type u
constant cons   : Π α : Type u, α → list α → list α

#check list nat
#check @cons

end hidden