/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons fin.extra

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

lemma tup.max_le : ∀ {n : ℕ} {xs : α ^ (n+1)} {y : α}, (∀ i, xs[i] ≤ y) → xs.max ≤ y
| 0 xs y h := h 0
| (n+1) xs y h :=
  have ∀ i, xs.tail[i] ≤ y, from λ ⟨i,hi⟩, h ⟨i+1, nat.succ_lt_succ hi⟩,
  max_le (h 0) (tup.max_le this)

definition tup.max' : Π {n : ℕ}, n ≠ 0 → α ^ n → α
| 0 h _ := absurd rfl h
| (n+1) _ xs := xs.max

lemma tup.le_max' : ∀ {n : ℕ} {xs : α ^ n} {i : fin n}, xs[i] ≤ tup.max' (fin.ne_zero_of_fin i) xs
| 0 _ i := fin.elim0 i
| (n+1) _ _ := tup.le_max

lemma tup.max'_le : ∀ {n : ℕ} {xs : α ^ n} {y : α} {h : n ≠ 0}, (∀ i, xs[i] ≤ y) → tup.max' h xs ≤ y
| 0 _ _ h := absurd rfl h
| (n+1) xs y _ := tup.max_le

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

lemma tup.le_min : ∀ {n : ℕ} {xs : α ^ (n+1)} {y : α}, (∀ i, y ≤ xs[i]) → y ≤ xs.min
| 0 xs y h := h 0
| (n+1) xs y h := 
  have ∀ i, y ≤ xs.tail[i], from λ ⟨i,hi⟩, h ⟨i+1, nat.succ_lt_succ hi⟩,
  le_min (h 0) (tup.le_min this)

definition tup.min' : Π {n : ℕ}, n ≠ 0 → α ^ n → α
| 0 h _ := absurd rfl h
| (n+1) _ xs := xs.min

lemma tup.min'_le : ∀ {n : ℕ} {xs : α ^ n} {i : fin n}, xs[i] ≥ tup.min' (fin.ne_zero_of_fin i) xs
| 0 _ i := fin.elim0 i
| (n+1) _ _ := tup.min_le

lemma tup.le_min' : ∀ {n : ℕ} {xs : α ^ n} {y : α} {h : n ≠ 0}, (∀ i, y ≤ xs[i]) → y ≤ tup.min' h xs
| 0 _ _ h := absurd rfl h
| (n+1) xs y _ := tup.le_min

