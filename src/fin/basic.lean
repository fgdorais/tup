/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .extra

namespace fin

lemma ne_zero_of_fin : ∀ {n : ℕ}, fin n → n ≠ 0
| 0 i := fin.elim0 i
| (n+1) _ := nat.succ_ne_zero n

lemma zero_ne_of_fin : ∀ {n : ℕ}, fin n → 0 ≠ n := 
λ _ i, ne.symm $ ne_zero_of_fin i

@[simp] lemma val_mk {n : ℕ} (i : ℕ) (hi : i < n) : (mk i hi).val = i := rfl
@[simp] lemma is_lt_mk {n : ℕ} (i : ℕ) (hi : i < n) : (mk i hi).is_lt = hi := rfl

definition zero (n : ℕ) : fin (n+1) := ⟨0, nat.succ_pos n⟩
definition last (n : ℕ) : fin (n+1) := ⟨n, nat.lt_succ_self n⟩

definition lift {n : ℕ} : fin n → fin (n+1) := λ ⟨i, hi⟩, ⟨i, nat.lt_succ_of_lt hi⟩
definition drop {n : ℕ} : Π (i : fin (n+1)), i ≠ last n → fin n := 
λ ⟨i, hi⟩ h, ⟨i, lt_of_le_of_ne (nat.le_of_lt_succ hi) (fin.vne_of_ne h)⟩

@[simp] lemma zero_val {n : ℕ} : (fin.zero n).val = 0 := rfl
@[simp] lemma last_val {n : ℕ} : (fin.last n).val = n := rfl

@[simp] lemma succ_val {n : ℕ} : ∀ (i : fin n), (fin.succ i).val = i.val + 1 := λ ⟨_,_⟩, rfl
@[simp] lemma pred_val {n : ℕ} : ∀ (i : fin (n+1)) {h : i ≠ fin.zero n}, (fin.pred i h).val = i.val - 1 := λ ⟨_,_⟩, rfl

@[simp] lemma lift_val {n : ℕ} : ∀ (i : fin n), (fin.lift i).val = i.val := λ ⟨_,_⟩, rfl
@[simp] lemma drop_val {n : ℕ} : ∀ (i : fin (n+1)) {h : i ≠ fin.zero n}, (fin.pred i h).val = i.val - 1 := λ ⟨_,_⟩, rfl

lemma succ_inj {n : ℕ} {i j : fin n} : fin.succ i = fin.succ j → i = j :=
begin
intro h, let h := veq_of_eq h, simp at h,
apply eq_of_veq,
exact nat.succ_inj h,
end

lemma lift_inj {n : ℕ} {i j : fin n} : fin.lift i = fin.lift j → i = j :=
begin
intro h, let h := veq_of_eq h, simp at h,
apply eq_of_veq,
exact h,
end

lemma succ_ne_zero {n : ℕ} : ∀ i, fin.succ i ≠ fin.zero n := λ ⟨i, hi⟩, fin.ne_of_vne (nat.succ_ne_zero i)
lemma lift_ne_last {n : ℕ} : ∀ i, fin.lift i ≠ fin.last n := λ ⟨i, hi⟩, fin.ne_of_vne (ne_of_lt hi)

lemma pred_succ {n : ℕ} : ∀ (i : fin n), fin.pred (fin.succ i) (fin.succ_ne_zero i) = i := λ ⟨_,_⟩, eq_of_veq $ rfl
lemma drop_lift {n : ℕ} : ∀ (i : fin n), fin.drop (fin.lift i) (fin.lift_ne_last i) = i := λ ⟨_,_⟩, eq_of_veq $ rfl

lemma lift_drop {n : ℕ} : ∀ (i : fin (n+1)) (h : i ≠ fin.last n), fin.lift (fin.drop i h) = i := λ ⟨_,_⟩ _, eq_of_veq $ rfl
lemma succ_pred {n : ℕ} : ∀ (i : fin (n+1)) (h : i ≠ fin.zero n), fin.succ (fin.pred i h) = i 
:= λ ⟨i,_⟩ h, have i ≠ 0, from fin.vne_of_ne h,
eq_of_veq $ nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero this)

lemma succ_lift_eq_lift_succ {n : ℕ} : ∀ (i : fin n), fin.lift (fin.succ i) = fin.succ (fin.lift i) := λ ⟨_,_⟩, eq_of_veq $ rfl

definition lift_by {m : ℕ} (n : ℕ) : fin m → fin (m+n) := λ ⟨i,hi⟩, ⟨i, nat.lt_add_right i m n hi⟩
definition push_by {n : ℕ} (m : ℕ) : fin n → fin (m+n) := λ ⟨i,h⟩, ⟨m+i, nat.add_lt_add_left h m⟩
definition succ_by {n : ℕ} (m : ℕ) : fin n → fin (m+n) := λ ⟨i,h⟩, ⟨i+m, eq.rec_on (add_comm m i) $ nat.add_lt_add_left h m⟩

@[simp] lemma lift_by_val {m n : ℕ} : ∀ {i : fin m}, (lift_by n i).val = i.val := λ ⟨_,_⟩, rfl
@[simp] lemma push_by_val {m n : ℕ} : ∀ {i : fin m}, (push_by n i).val = n + i.val := λ ⟨_,_⟩, rfl
@[simp] lemma succ_by_val {m n : ℕ} : ∀ {i : fin m}, (succ_by n i).val = i.val + n := λ ⟨_,_⟩, rfl

lemma lift_by_inj {m n : ℕ} {i j : fin m} : lift_by n i = lift_by n j → i = j :=
begin
intro h, let h := veq_of_eq h, simp at h,
apply eq_of_veq,
exact h,
end

lemma push_by_inj {m n : ℕ} {i j : fin m} : push_by n i = push_by n j → i = j :=
begin
intro h, let h := veq_of_eq h, simp at h,
apply eq_of_veq,
apply add_left_cancel h,
end

lemma succ_by_inj {m n : ℕ} {i j : fin m} : succ_by n i = succ_by n j → i = j :=
begin
intro h, let h := veq_of_eq h, simp at h,
apply eq_of_veq,
apply add_left_cancel h,
end

lemma push_by_eq_succ_by {m n : ℕ} (i : fin m) : push_by n i = succ_by n i :=
by apply eq_of_veq; simp

lemma lift_by_ne_push_by {m n : ℕ} (i : fin m) (j : fin n) : lift_by n i ≠ push_by m j :=
begin 
apply ne_of_vne, simp,
intro h,
have h' : ¬ (m > m + j.val), from not_lt_of_ge (nat.le_add_right m j.val),
rw ← h at h',
exact h' i.is_lt,
end

end fin
