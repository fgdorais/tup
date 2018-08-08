/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

theorem ge_of_eq {α : Type*} [preorder α] {a b : α} : a = b → a ≥ b := λ h, le_of_eq (eq.symm h)

namespace nat

lemma add_sub_cancel' (m n : ℕ) : (m + n) - m = n := 
by rw [nat.add_comm, nat.add_sub_cancel]

lemma sub_add_of_le {m n : ℕ} : m ≤ n → (n - m) + m = n :=
assume h : m ≤ n, by rw [add_comm, add_sub_of_le h]

lemma sub_lt_of_lt_add_of_ge {m n i : ℕ} : i ≥ m → i < m + n → i - m < n :=
assume (hm : m ≤ i) (h : i < m + n),
lt_of_add_lt_add_left $
show m + (i - m) < m + n, 
from calc m + (i - m) = i : add_sub_of_le hm
              ... < m + n : h

lemma le_sub_of_add_le_of_ge {m n i : ℕ} :
n ≤ i → n + m ≤ i → m ≤ i - n :=
assume hn h, 
le_of_add_le_add_left $
show n + m ≤ n + (i - n),
from calc n + m ≤ i : h
  ... = n + (i - n) : eq.symm $ add_sub_of_le hn

end nat

namespace option

lemma map_is_some {α : Type*} {β : Type*} (f : α → β) :
∀ x, is_some (option.map f x) = is_some x
| (some _) := rfl
| none := rfl

lemma map_is_none {α : Type*} {β : Type*} (f : α → β) :
∀ x, is_none (option.map f x) = is_none x
| (some _) := rfl
| none := rfl

end option



