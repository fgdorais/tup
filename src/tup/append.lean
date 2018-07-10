/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons fin.extra

namespace tup
variables {α : Type*} {m n : ℕ}

definition append : α ^ m → α ^ n → α ^ (m + n)
| xs ys ⟨i, h⟩ := 
  if hm : i < m then
    xs ⟨i, hm⟩
  else
    ys ⟨i - m, nat.sub_lt_of_lt_add_of_ge (le_of_not_gt hm) h⟩

infixl ` ⊔ `:65 := append

lemma ith_append_of_lt {xs : α ^ m} {ys : α ^ n} {i : ℕ} (h : i < m) : 
(xs ⊔ ys)[⟨i, nat.lt_add_right i m n h⟩] = xs[⟨i,h⟩] := dif_pos h

lemma ith_append_of_ge {xs : α ^ m} {ys : α ^ n} {i : ℕ} (h : i < m+n) (hm : i ≥ m) :
(xs ⊔ ys)[⟨i, h⟩] = ys[⟨i-m, nat.sub_lt_of_lt_add_of_ge hm h⟩] := dif_neg (not_lt_of_ge hm)

@[simp]
lemma append_lift {xs : α ^ m} {ys : α ^ n} :
∀ i, (xs ⊔ ys)[fin.lift n i] = xs[i]
| ⟨i, h⟩ := ith_append_of_lt h

@[simp]
lemma append_push {xs : α ^ m} {ys : α ^ n} :
∀ i : fin n, (xs ⊔ ys)[fin.push m i] = ys[i]
| ⟨i, h⟩ := 
  calc
  (xs ⊔ ys)[⟨m+i, nat.add_lt_add_left h m⟩] 
      = ys[⟨(m+i)-m, _⟩] : ith_append_of_ge (nat.add_lt_add_left h m) (nat.le_add_right m i)
  ... = ys[⟨i, h⟩]       : by simp [nat.add_sub_cancel']

@[simp]
lemma append_nil (xs : α ^ n) : xs ⊔ nil = xs :=
ext (λ ⟨i,hi⟩, ith_append_of_lt hi)

@[reducible] 
definition take (n : ℕ) (xs : α ^ (n + m)) : α ^ n 
:= λ i, xs[fin.lift _ i]

@[simp]
lemma take_val {xs : α ^ (n + m)} :
∀ i : fin n, (take n xs)[i] = xs[fin.lift m i]
| ⟨i, hi⟩ := rfl

lemma take_append {xs : α ^ m} {ys : α ^ n} : take m (xs ⊔ ys) = xs :=
tup.ext (λ i, by simp)

@[reducible] 
definition take_of_le {{m n : ℕ}} : n ≤ m → α ^ m → α ^ n
| h xs i := xs[fin.lift_to h i]

@[reducible] 
definition drop (n : ℕ) (xs : α ^ (n + m)) : α ^ m :=
λ i : fin m, xs[fin.push n i]

@[simp]
lemma drop_val {xs : α ^ (m + n)} :
∀ i : fin n, (drop m xs)[i] = xs[fin.push m i]
| ⟨i, hi⟩ := rfl

lemma drop_append {xs : α ^ m} {ys : α ^ n} : drop m (xs ⊔ ys) = ys :=
tup.ext (λ i, by simp)

@[reducible]
definition drop_of_le {{m n : ℕ}} : m ≤ n → α ^ n → α ^ m
| h xs i := xs[fin.push_to h i]

end tup

namespace ntup
variable {α : Type*}

@[reducible]
definition append : ntup α → ntup α → ntup α
| ⟨n, xs⟩ ⟨m, ys⟩ := ⟨n + m, xs ⊔ ys⟩ 

instance : has_emptyc (ntup α) := ⟨ntup.nil⟩
instance : has_append (ntup α) := ⟨append⟩

end ntup