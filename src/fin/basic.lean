/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .extra

namespace fin

lemma nonzero_of_fin : ∀ {n : ℕ}, fin n → n ≠ 0
| 0 i := fin.elim0 i
| (n+1) _ := nat.succ_ne_zero n

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

@[simp] lemma lift_by_val {m n : ℕ} : ∀ {i : fin m}, (lift_by n i).val = i.val := λ ⟨_,_⟩, rfl
@[simp] lemma push_by_val {m n : ℕ} : ∀ {i : fin m}, (push_by n i).val = n + i.val := λ ⟨_,_⟩, rfl

definition cases_zero_succ {n : ℕ} {C : fin (n+1) → Sort*} :
C (fin.zero n) → (Π i, C (fin.succ i)) → (Π i, C i)
| hz _ ⟨0,_⟩ := hz
| _ hs ⟨i+1,hi⟩ := hs ⟨i, nat.lt_of_succ_lt_succ hi⟩

@[simp] lemma cases_zero {n : ℕ} {C : fin (n+1) → Sort*} (h : C 0) (hs : Π i, C (fin.succ i)) :
cases_zero_succ h hs (fin.zero n) = h := rfl

@[simp] lemma cases_succ {n : ℕ} {C : fin (n+1) → Sort*} (h : C 0) (hs : Π i, C (fin.succ i)) :
∀ i, cases_zero_succ h hs (fin.succ i) = hs i | ⟨_,_⟩ := rfl

@[reducible] definition cases_zero_succ_on {n : ℕ} {C : fin (n+1) → Sort*} (i : fin (n+1)) :
C 0 → (Π i, C (fin.succ i)) → C i :=
λ hz hs, fin.cases_zero_succ hz hs i

definition rec_zero_succ {C : Π {n : ℕ}, fin n → Sort*} :
(Π n, C (fin.zero n)) → (Π {n : ℕ} (i : fin n), C i → C (fin.succ i)) → (Π {n : ℕ} (i : fin n), C i) :=
λ hz hs n, nat.rec_on n (λ i, fin.elim0 i) $
λ n ih, cases_zero_succ (hz n) (λ i, hs i (ih i))

@[simp] lemma rec_zero {C : Π {n : ℕ}, fin n → Sort*} (h : Π n, C (fin.zero n)) (hs : Π {n : ℕ} (i : fin n), C i → C (fin.succ i)) :
∀ (n : ℕ), rec_zero_succ h @hs (fin.zero n) = h n | _ := rfl

@[simp] lemma rec_succ {C : Π {n : ℕ}, fin n → Sort*} (h : Π n, C (fin.zero n)) (hs : Π {n : ℕ} (i : fin n), C i → C (fin.succ i)) :
∀ {n : ℕ} (i : fin n), rec_zero_succ h @hs (fin.succ i) = hs i (rec_zero_succ h @hs i) | _ ⟨_,_⟩ := rfl

@[reducible] definition rec_zero_succ_on {C : Π {n : ℕ}, fin n → Sort*} {n : ℕ} (i : fin n) :
(Π (n : ℕ), C (fin.zero n)) → (Π (n : ℕ) (i : fin n), C i → C (fin.succ i)) → C i :=
λ hz hs, rec_zero_succ hz hs i

end fin
