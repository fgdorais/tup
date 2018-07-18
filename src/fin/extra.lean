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

lemma le_sub_of_add_le_of_ge {m n i : ℕ} :
n ≤ i → n + m ≤ i → m ≤ i - n :=
assume hn h, 
le_of_add_le_add_left $
show n + m ≤ n + (i - n),
from calc n + m ≤ i : h
  ... = n + (i - n) : eq.symm $ add_sub_of_le hn

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

@[simp]
lemma cast_val {m n : ℕ} {h : m = n} (i : fin m) : (cast h i).val = i.val := by simp

lemma nonzero_of_fin : ∀ {n : ℕ}, fin n → n ≠ 0
| 0 i := fin.elim0 i
| (n+1) _ := nat.succ_ne_zero n

@[reducible]
definition lift_by {m : ℕ} (n : ℕ) : fin m → fin (m+n)
| ⟨i,hi⟩ := ⟨i, nat.lt_add_right i m n hi⟩

lemma lift_by_val {m n : ℕ} : 
∀ {i : fin m}, (lift_by n i).val = i.val
| ⟨_,_⟩ := rfl

@[reducible]
definition lift {m n : ℕ} : m ≤ n → fin m → fin n
| h ⟨i, hi⟩ := ⟨i, lt_of_lt_of_le hi h⟩ 

@[simp]
lemma lift_val {m n : ℕ} {h : m ≤ n} :
∀ {i : fin m}, (lift h i).val = i.val
| ⟨i,hi⟩ := rfl

@[simp]
lemma lift_lift {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} : 
∀ {i : fin l}, lift hmn (lift hlm i) = lift (le_trans hlm hmn) i :=
λ i, eq_of_veq (by simp)

@[reducible]
definition push_by {n : ℕ} (m : ℕ := 1) : fin n → fin (m+n)
| ⟨i,h⟩ := ⟨m+i, nat.add_lt_add_left h m⟩

@[simp]
lemma push_by_val {m n : ℕ} : 
∀ {i : fin m}, (push_by n i).val = n + i.val
| ⟨_,_⟩ := rfl

@[reducible]
definition push {m n : ℕ} : m ≤ n → fin m → fin n
| h ⟨i,hi⟩ := 
  have (n - m) + i < n, from calc
  (n - m) + i < (n - m) + m : nat.add_lt_add_left hi (n-m)
          ... = n : by rw nat.sub_add_cancel h,
  ⟨(n - m) + i, this⟩

@[simp]
lemma push_val {m n : ℕ} {h : m ≤ n} :
∀ {i : fin m}, (push h i).val = (n - m) + i.val 
| ⟨_,_⟩ := rfl

@[simp]
lemma push_push {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} : 
∀ {i : fin l}, push hmn (push hlm i) = push (le_trans hlm hmn) i :=
have m - l ≤ m, from nat.sub_le m l,
λ i, eq_of_veq $ by simp; rw [add_comm (m-l) (n-m), ←nat.add_sub_assoc hlm (n-m), nat.sub_add_of_le hmn]

lemma lift_by_push_by_veq_push_by_lift_by {l m n : ℕ} : 
∀ {i : fin l}, (lift_by m (push_by n i)).val = (push_by n (lift_by m i)).val :=
λ ⟨i,_⟩, by simp

end fin

