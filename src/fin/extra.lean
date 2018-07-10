/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

end nat

namespace fin

definition zero (n : ℕ) : fin (n+1) := ⟨0, nat.succ_pos n⟩

definition last (n : ℕ) : fin (n+1) := ⟨n, nat.lt_succ_self n⟩

@[simp]
lemma eq_rec_val : 
∀ {m n : ℕ} {h : m = n} {i : fin m}, @fin.val n (eq.rec_on h i) = i.val
| m .(m) rfl ⟨i,hi⟩ := rfl

@[reducible] 
definition cast {m n : ℕ} : m = n → fin m → fin n := eq.rec_on

lemma cast_val {m n : ℕ} {h : m = n} (i : fin m) : (cast h i).val = i.val := by simp

lemma nonzero_of_fin : ∀ {n : ℕ}, fin n → n ≠ 0
| 0 i := fin.elim0 i
| (n+1) _ := nat.succ_ne_zero n

@[reducible]
definition lift {m : ℕ} (n : ℕ := 1) : fin m → fin (m+n)
| ⟨i,h⟩ := ⟨i, nat.lt_add_right i m n h⟩

@[reducible]
definition lift_to {m n : ℕ} : m ≤ n → fin m → fin n
| h i := eq.rec_on (nat.add_sub_of_le h) (lift (n-m) i)

@[simp]
lemma lift_val {m n : ℕ} : 
∀ {i : fin m}, (lift n i).val = i.val
| ⟨_,_⟩ := rfl

@[simp]
lemma lift_to_val {m n : ℕ} {h : m ≤ n} :
∀ {i : fin m}, (lift_to h i).val = i.val
| ⟨i,ih⟩ := by simp

@[reducible]
definition push {n : ℕ} (m : ℕ := 1) : fin n → fin (m+n)
| ⟨i,h⟩ := ⟨m+i, nat.add_lt_add_left h m⟩

@[reducible]
definition push_to {m n : ℕ} : m ≤ n → fin m → fin n
| h i := eq.rec_on (nat.sub_add_of_le h) (push (n-m) i)

@[simp]
lemma push_val {m n : ℕ} : 
∀ {i : fin m}, (push n i).val = n + i.val
| ⟨_,_⟩ := rfl

@[simp]
lemma push_to_val {m n : ℕ} {h : m ≤ n} :
∀ {i : fin m}, (push_to h i).val = (n - m) + i.val 
| ⟨i,ih⟩ := by simp

lemma lift_push_veq_push_lift {l m n : ℕ} : 
∀ {i : fin l}, (lift m (push n i)).val = (push n (lift m i)).val :=
λ ⟨i,_⟩, by simp

@[simp]
lemma lift_lift {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} : 
∀ {i : fin l}, lift_to hmn (lift_to hlm i) = lift_to (le_trans hlm hmn) i :=
λ i, eq_of_veq (by simp)

@[simp]
lemma push_push {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} : 
∀ {i : fin l}, push_to hmn (push_to hlm i) = push_to (le_trans hlm hmn) i :=
have m - l ≤ m, from nat.sub_le m l,
λ i, eq_of_veq $ by simp; rw [add_comm (m-l) (n-m), ←nat.add_sub_assoc hlm (n-m), nat.sub_add_of_le hmn]

end fin

