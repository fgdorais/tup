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

lemma nonzero_of_fin : ∀ {n : ℕ}, fin n → n ≠ 0
| 0 i := fin.elim0 i
| (n+1) _ := nat.succ_ne_zero n

definition zero (n : ℕ) : fin (n+1) := ⟨0, nat.succ_pos n⟩
definition last (n : ℕ) : fin (n+1) := ⟨n, nat.lt_succ_self n⟩

def skip {n : ℕ} : fin n → fin (n+1) := λ ⟨i, hi⟩, ⟨i, nat.lt_succ_of_lt hi⟩
def drop {n : ℕ} : Π (i : fin (n+1)), i ≠ last n → fin n := 
λ ⟨i, hi⟩ h, ⟨i, lt_of_le_of_ne (nat.le_of_lt_succ hi) (fin.vne_of_ne h)⟩

@[simp] lemma zero_val {n : ℕ} : (fin.zero n).val = 0 := rfl
@[simp] lemma last_val {n : ℕ} : (fin.last n).val = n := rfl

@[simp] lemma succ_val {n : ℕ} : ∀ (i : fin n), (fin.succ i).val = i.val + 1 := λ ⟨_,_⟩, rfl
@[simp] lemma pred_val {n : ℕ} : ∀ (i : fin (n+1)) {h : i ≠ fin.zero n}, (fin.pred i h).val = i.val - 1 := λ ⟨_,_⟩, rfl

@[simp] lemma skip_val {n : ℕ} : ∀ (i : fin n), (fin.skip i).val = i.val := λ ⟨_,_⟩, rfl
@[simp] lemma drop_val {n : ℕ} : ∀ (i : fin (n+1)) {h : i ≠ fin.zero n}, (fin.pred i h).val = i.val - 1 := λ ⟨_,_⟩, rfl

lemma succ_ne_zero {n : ℕ} : ∀ i, fin.succ i ≠ fin.zero n := λ ⟨i, hi⟩, fin.ne_of_vne (nat.succ_ne_zero i)
lemma skip_ne_last {n : ℕ} : ∀ i, fin.skip i ≠ fin.last n := λ ⟨i, hi⟩, fin.ne_of_vne (ne_of_lt hi)

lemma pred_succ {n : ℕ} : ∀ (i : fin n), fin.pred (fin.succ i) (fin.succ_ne_zero i) = i := λ ⟨_,_⟩, eq_of_veq $ rfl
lemma drop_skip {n : ℕ} : ∀ (i : fin n), fin.drop (fin.skip i) (fin.skip_ne_last i) = i := λ ⟨_,_⟩, eq_of_veq $ rfl
lemma succ_skip_eq_skip_succ {n : ℕ} : ∀ (i : fin n), fin.skip (fin.succ i) = fin.succ (fin.skip i) := λ ⟨_,_⟩, eq_of_veq $ rfl

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
lemma lift_zero {m n : ℕ} {h : m+1 ≤ n+1} :
lift h 0 = 0 := eq_of_veq $ by simp; reflexivity

@[simp]
lemma lift_succ {m n : ℕ} {h : m+1 ≤ n+1} (i : fin m) :
lift h (fin.succ i) = fin.succ (lift (nat.le_of_succ_le_succ h) i) :=
eq_of_veq $ by simp

@[simp]
lemma lift_lift {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} : 
∀ {i : fin l}, lift hmn (lift hlm i) = lift (le_trans hlm hmn) i :=
λ i, eq_of_veq $ by simp

@[reducible]
definition push_by {n : ℕ} (m : ℕ) : fin n → fin (m+n)
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

lemma cases_zero_succ {n : ℕ} {C : fin (n+1) → Sort*} :
C 0 → (Π i, C (fin.succ i)) → (Π i, C i)
| hz _ ⟨0,_⟩ := hz
| _ hs ⟨i+1,hi⟩ := hs ⟨i, nat.lt_of_succ_lt_succ hi⟩

lemma cases_zero_succ_on {n : ℕ} {C : fin (n+1) → Sort*} (i : fin (n+1)) :
C 0 → (Π i, C (fin.succ i)) → C i :=
λ hz hs, fin.cases_zero_succ hz hs i

lemma rec' {C : Π n, fin n → Sort*} :
(Π n, C (n+1) 0) → (Π n i, C n i → C (n+1) (fin.succ i)) → (Π n i, C n i) :=
λ hz hs n, nat.rec_on n (λ i, fin.elim0 i) $
λ n ih, cases_zero_succ (hz n) (λ i, hs n i (ih i))

lemma rec_on' {C : Π {n : ℕ}, fin n → Sort*} {n : ℕ} (i : fin n) :
(Π (n : ℕ), C (fin.zero n)) → (Π (n : ℕ) (i : fin n), C i → C (fin.succ i)) → C i :=
λ hz hs, rec' hz hs n i

end fin

