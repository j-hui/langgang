


inductive xnat 
| zero : xnat
| succ : xnat → xnat

#check xnat.zero -- implicit name space
open xnat
#check zero 
#check succ zero

definition one := succ zero
definition two := succ one
definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

notation a + b := add a b

theorem one_add_one_equals_two : one + one = two :=
begin  
unfold two,
unfold one,
unfold add,
end

theorem one_add_one_equals_two' : one + one = two :=
begin  
refl
end

theorem one_add_one_equals_two'' : one + one = two :=
begin  
dunfold two,
dunfold one,
dunfold add,
refl,
end

theorem add_zero' (n : xnat) : n + zero = n :=
begin
unfold add
end

theorem zero_add' (n : xnat) : zero + n = n :=
begin
induction n with t Ht,
  refl,
unfold add,
rewrite [Ht],
end

theorem add_assoc' (a b c : xnat) : (a + b) + c = a + (b + c) :=
begin
induction c with t Ht,
    refl,
unfold add,
rewrite [Ht],
end


theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add'],
rewrite [add_zero']
end


theorem add_one_eq_succ (n : xnat) : one + n = succ n :=
begin
unfold one,
induction n with t Ht,
    refl,
unfold add,
rewrite Ht,
end

theorem succ_eq_add_one (n : xnat) : succ n = one + n :=
begin
exact eq.symm (add_one_eq_succ n)
end

theorem add_comm' (a b : xnat) : a + b = b + a :=
begin
induction a with a Ha,
rewrite [zero_add_eq_add_zero],
unfold add,
rewrite [succ_eq_add_one a],
rewrite [add_assoc'],
rewrite Ha,
rewrite add_one_eq_succ
end

theorem add_comm'' (a b : xnat) : a + b = b + a :=
begin
induction a with a Ha,
  induction b with b Hb, -- 0 + b = b + 0 
    refl, -- 0 + 0 = 0 + 0
  unfold add, -- 0 + (1 + b) = (1 + b) + 0
  rewrite Hb,
  refl,
unfold add,  -- (1 + a) + b = b + (1 + a)
rewrite [ ← add_one_eq_succ a],
rewrite [add_assoc'],
rewrite Ha,
rewrite add_one_eq_succ
end


theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
begin
split,
  exact succ.inj,
assume H : a = b,
rw [H]
end


theorem add_cancel_right (a b t : xnat) :  a = b ↔ a+t = b+t :=
begin
split,
  assume H : a = b,
  rw [H],
induction t with t Ht,
  assume H, 
  unfold add at H,
  rewrite [H],
assume H,
unfold add at H,
rewrite [eq_iff_succ_eq_succ ] at H,
apply Ht,
exact H
end



definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := (mul n p) + n

notation a * b := mul a b

example : one * one = one := 
begin
refl
end

theorem mul_zero' (a : xnat) : a * zero = zero := 
begin 
unfold mul
end 


theorem zero_mul' (a : xnat) : zero * a = zero := 
begin
induction a with a Ha,
  refl,
unfold mul,
rw [Ha],
refl
end


theorem mul_one' (a : xnat) : a * one = a := 
begin 
unfold one,
unfold mul,
rw [add_comm'],
unfold add
end
theorem one_mul' (a : xnat) : one * a = a := 
begin 
unfold one,
induction a with a Ha,
  refl,
unfold mul,
rw [Ha,add_comm', succ_eq_add_one a],
refl
end

theorem right_distrib' (a b c : xnat) : a * (b + c) = a* b + a * c := 
egin 
induction c with c Hc,
  rw [mul_zero'], 
  rw [add_zero', add_zero'],
rw [succ_eq_add_one, add_comm', add_assoc' ,add_one_eq_succ],
unfold mul,
rw [add_comm' c b, Hc,add_one_eq_succ], 
unfold mul,
rw [add_assoc']
end

theorem left_distrib' (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
induction c with n Hn,
  unfold mul,
  refl,
rw [←add_one_eq_succ],
rw [right_distrib',Hn,right_distrib',right_distrib'],
rw [mul_one',mul_one',mul_one'],
rw [add_assoc',← add_assoc' b ,  ← add_comm' (a*n),←add_assoc',←add_assoc',←add_assoc'],
end

theorem mul_assoc' (a b c : xnat) : (a * b) * c = a * (b * c) := 
begin 
induction a with a Ha,
  rewrite [zero_mul', zero_mul', zero_mul'],
rw [succ_eq_add_one],
rw [left_distrib', left_distrib', left_distrib'], 
rw [one_mul', one_mul', Ha]
end


theorem mul_comm' (a b : xnat) : a * b = b * a := 
begin
induction a with a Ha,
  rw [zero_mul', mul_zero'],
rw [succ_eq_add_one,left_distrib', right_distrib', Ha, one_mul', mul_one']
end

definition lt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

notation a < b := lt a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t := 
begin
assume H,
induction t with t Ht,
  rw [add_zero', add_zero'],
  exact H,
unfold add,
unfold lt,
exact Ht
end

theorem lt_add_one (a :xnat): a < succ a :=
begin 
  induction a with a Ha,
    unfold lt,
  unfold lt,
  apply Ha
end

theorem gt_add_one (a b: xnat): succ b = a → b < a :=
begin
intro H,
rw [← H],
exact (lt_add_one b)
end

theorem lt_zero_false (a:xnat): a < zero = false :=
begin 
  cases a,
    trivial,
  trivial
end 

theorem lt_not_eq (a:xnat): a < a = false :=
begin
  induction a with a Ha,
  trivial,
  unfold lt,
  exact Ha,
end

theorem consec_lem : ∀ b : xnat , succ zero < b → zero < b :=
begin
  intro,
  induction b with b Hb,
    unfold lt,
    trivial,
  assume H, 
  unfold lt at *,
end

theorem consec (a b: xnat) : succ a < b → a < b := 
begin 
  revert b,
  induction a with a Ha,
    exact consec_lem,
  intro b, 
  specialize Ha (succ b),
  assume H,
  unfold lt at *,
  

end 

theorem add_one_lt (a b: xnat) : a < b → a < succ b :=
begin
assume H,
have h : succ a < succ b,
  unfold lt, exact H,
have j : a < succ a,
  exact lt_add_one a,

induction a with a Ha,
  induction b with b Hb,
    unfold lt,
  unfold lt,


-- a < b -> a + 1 < b + 1 /\ a < a + 1 -> a < b + 1
end

theorem redef (a b:xnat) : a < b ↔ 
begin 
split, intros H,
induction a with a Ha,
  
  

end


theorem ii (a b: xnat) : succ a < b → a < b :=
begin
assume H,
induction b with b Hb,
unfold lt at *,
trivial,
unfold lt at *, 

end

theorem gt_succ_then_gt_zero (b c: xnat): succ b < c → zero < c :=
begin
assume H, 
induction c with c Hc, 
unfold lt at H, trivial,
unfold lt at *
end 

theorem inequality_A2 (a b c : xnat) : a < b → b < c → a < c := 
begin

induction c with c Hc, 
  induction b with b Hb,
    induction a with a Ha,
      unfold lt, trivial,
    unfold lt, trivial,
  assume H1 H2, unfold lt at H2, trivial,
assume H1 H2,
induction b with b Hb,
  unfold lt at *, 
  rw (lt_zero_false a) at H1,
  trivial,
unfold lt at *,

have F: (succ a < b → a < b), 
  



end

theorem strict (a: xnat) : (a < a) = false :=
begin 
  induction a with a Ha,
    unfold lt, 
  unfold lt, exact Ha
end


theorem a_only_one (b : xnat) : ∀ a, (a < b ∨ a = b ∨ b < a) :=
begin 
induction b with b Hb,
  intro a,
  induction a with a Ha,
    simp,
  unfold lt, simp,
intro a,
induction a with a Ha,
  unfold lt, simp,
cases Ha, unfold lt at *, admit,
cases Ha, unfold lt at *, rw Ha, 
have S : b < succ b,
  exact lt_add_one b,
right,right,exact S,
unfold lt, 
specialize Hb a,
cases Hb,
  left, exact Hb,
cases Hb,
  right, left, simp, exact Hb,
right, right, exact Hb
end 
theorem lemma1 (a b : xnat) : (a < b ∨ a = b ∨ b < a) :=
begin 
admit,
end 
theorem lemma2 (a b : xnat) : (a < b → ¬ (a = b)):=
begin 
assume H,
revert a,
induction b with b Hb,
  intros, rw lt_zero_false at H, trivial,
intros a H, 
by_contradiction contra, 
specialize Hb a, 
rw contra at H, 
unfold lt at H,
rw strict at H,
trivial
end 

theorem lemma3(a b : xnat) : (a < b → ¬ (b < a)) :=
begin 
assume H,
revert a,
induction b with b Hb,
  intros, rw lt_zero_false at *, trivial,
intros a H,
assume contra,



end 

theorem inequality_A3 (a b : xnat) : (a < b ∨ a = b ∨ b < a) 
                                   ∧ (a < b → ¬ (a = b))
                                   ∧ (a < b → ¬ (b < a))
                                   ∧ (a = b → ¬ (b < a)) := 
begin 
split, 
  admit,
split, 
  exact lemma2 a b,
split,
  admit,
assume H,
rw H, 
rw (lt_not_eq b), 
trivial
end

theorem inequality_A4 (a b : xnat) : zero < a → zero < b → zero < a * b := 
begin
induction a with a Ha,
  induction b with b Hb,
    unfold mul, unfold lt, trivial,
  unfold lt, intro,
  trivial,
induction b with b Hb,
  unfold lt, 
  intros, trivial,
intros, unfold mul
end

#check 