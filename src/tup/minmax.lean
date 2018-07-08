
import .basic .cons .extra

variables {α : Type*} [dlo : decidable_linear_order α]
include dlo
open tup

definition tup.max : Π {n : ℕ}, α ^ (n+1) → α 
| 0 xs := xs.head
| (n+1) xs := max xs.head (tup.max xs.tail)

lemma tup.le_max : ∀ {n : ℕ} {xs : α ^ (n+1)} {i : fin (n+1)}, xs[i] ≤ xs.max
| 0 xs ⟨0,_⟩ := 
  le_refl xs.head
| 0 _ ⟨i+1,h⟩ := 
  absurd (nat.lt_of_succ_lt_succ h) (nat.not_lt_zero i)
| (n+1) xs ⟨0,_⟩ := 
  le_max_left xs.head xs.tail.max
| (n+1) xs ⟨i+1,h⟩ :=
  calc
  xs[⟨i+1, h⟩]
      = (xs.tail)[⟨i, nat.lt_of_succ_lt_succ h⟩] : rfl
  ... ≤ xs.tail.max : tup.le_max
  ... ≤ xs.max      : le_max_right xs.head xs.tail.max

definition tup.max' : Π {n : ℕ}, n ≠ 0 → α ^ n → α
| 0 h _ := absurd rfl h
| (n+1) _ xs := xs.max

lemma tup.le_max' : ∀ {n : ℕ} {xs : α ^ n} {i : fin n}, xs[i] ≤ tup.max' (fin.nonzero_of_fin i) xs
| 0 _ i := fin.elim0 i
| (n+1) _ _ := tup.le_max

definition tup.min : Π {n : ℕ}, α ^ (n+1) → α 
| 0 xs := xs.head
| (n+1) xs := min xs.head (tup.min xs.tail)

lemma tup.min_le : ∀ {n : ℕ} {xs : α ^ (n+1)} {i : fin (n+1)}, xs[i] ≥ xs.min
| 0 xs ⟨0,_⟩ := 
  le_refl xs.head
| 0 _ ⟨i+1,h⟩ := 
  absurd (nat.lt_of_succ_lt_succ h) (nat.not_lt_zero i)
| (n+1) xs ⟨0,_⟩ := 
  min_le_left xs.head xs.tail.min
| (n+1) xs ⟨i+1,h⟩ :=
  calc
  xs[⟨i+1, h⟩]
      = xs.tail[⟨i, nat.lt_of_succ_lt_succ h⟩] : rfl
  ... ≥ xs.tail.min : tup.min_le
  ... ≥ xs.min      : min_le_right xs.head xs.tail.min

definition tup.min' : Π {n : ℕ}, n ≠ 0 → α ^ n → α
| 0 h _ := absurd rfl h
| (n+1) _ xs := xs.min

lemma tup.min'_le : ∀ {n : ℕ} {xs : α ^ n} {i : fin n}, xs[i] ≥ tup.min' (fin.nonzero_of_fin i) xs
| 0 _ i := fin.elim0 i
| (n+1) _ _ := tup.min_le

