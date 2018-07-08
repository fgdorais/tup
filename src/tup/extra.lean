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
definition lift_by {m : ℕ} (n : ℕ) : fin m → fin (m+n)
| ⟨i,h⟩ := ⟨i, nat.lt_add_right i m n h⟩

definition lift {n : ℕ} : fin n → fin (n+1) := lift_by 1

@[reducible]
definition lift_of_le {m n : ℕ} : m ≤ n → fin m → fin n
| h i := eq.rec_on (nat.add_sub_of_le h) (lift_by (n-m) i)

@[simp]
lemma lift_by_val {m n : ℕ} : 
∀ {i : fin m}, (lift_by n i).val = i.val
| ⟨_,_⟩ := rfl

@[simp]
lemma lift_of_le_val {m n : ℕ} {h : m ≤ n} :
∀ {i : fin m}, (lift_of_le h i).val = i.val
| ⟨i,ih⟩ := by simp

@[reducible]
definition push_by {m : ℕ} (n : ℕ) : fin m → fin (n+m)
| ⟨i,h⟩ := ⟨n+i, nat.add_lt_add_left h n⟩

definition push {n : ℕ} : fin n → fin (1+n) := push_by 1

@[reducible]
definition push_of_le {m n : ℕ} : m ≤ n → fin m → fin n
| h i := eq.rec_on (nat.sub_add_of_le h) (push_by (n-m) i)

@[simp]
lemma push_by_val {m n : ℕ} : 
∀ {i : fin m}, (push_by n i).val = n + i.val
| ⟨_,_⟩ := rfl

@[simp]
lemma push_of_le_val {m n : ℕ} {h : m ≤ n} :
∀ {i : fin m}, (push_of_le h i).val = (n - m) + i.val 
| ⟨i,ih⟩ := by simp

lemma lift_push_eq_push_lift {n : ℕ} : 
∀ {i : fin n}, lift (push i) = push (lift i)
| ⟨_,_⟩ := rfl

end fin

