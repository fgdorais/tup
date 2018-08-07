/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons

namespace tup
variable {α : Type*}

@[reducible] definition del : Π {n : ℕ}, fin (n+1) → α ^ (n + 1) → α ^ n
| n ⟨0,_⟩ xs := tail xs
| 0 ⟨k+1,hk⟩ _ := absurd (nat.lt_of_succ_lt_succ hk) (nat.not_lt_zero k)
| (n+1) ⟨k+1,hk⟩ xs := xs.head :: del ⟨k, nat.lt_of_succ_lt_succ hk⟩ xs.tail

@[simp] lemma del_zero {n : ℕ} (xs : α ^ (n+1)) : del 0 xs = tail xs := 
by cases n; reflexivity

@[simp] lemma del_succ {n : ℕ} (xs : α ^ (n+2)) : 
∀ k, del (fin.succ k) xs = xs.head :: del k xs.tail :=
by cases n; intros k; cases k; simp [del, fin.succ]

@[simp] lemma del_zero_cons {n : ℕ} (x : α) (xs : α ^ n) : del 0 (x :: xs) = xs := by simp

@[simp] lemma del_succ_cons {n : ℕ} (x : α) (xs : α ^ (n+1)) (k : fin (n+1)) : 
del (fin.succ k) (x :: xs) = x :: (del k xs) := by simp

lemma ith_del_of_vlt : 
∀ {n : ℕ} {k : fin (n+1)} {i : fin n}, 
i.val < k.val → ∀ (xs : α ^ (n+1)), (del k xs)[i] = xs[fin.skip i]
| 0 _ _ := by intros; apply fin.elim0; assumption
| (n+1) ⟨0,_⟩ _ := by intros; exfalso; apply nat.not_lt_zero; assumption
| (n+1) ⟨k+1,hk⟩ ⟨0,_⟩ := by intros; unfold del; reflexivity
| (n+1) ⟨k+1,hk⟩ ⟨i+1,hi⟩ :=
  begin
  intros h xs,
  unfold del,
  apply ith_del_of_vlt,
  exact nat.lt_of_succ_lt_succ h
  end

lemma ith_del_of_vge :
∀ {n : ℕ} {k : fin (n+1)} {i : fin n},
i.val ≥ k.val → ∀ (xs : α ^ (n+1)), (del k xs)[i] = xs[fin.succ i]
| 0 _ _ := by intros; apply fin.elim0; assumption
| (n+1) ⟨0,_⟩ _ := by intros; simp [del]
| (n+1) ⟨k+1,hk⟩ ⟨0,_⟩ := by intros; exfalso; apply nat.not_succ_le_zero; assumption
| (n+1) ⟨k+1,hk⟩ ⟨i+1,hi⟩ := 
  begin
  intros h xs,
  unfold del,
  apply ith_del_of_vge,
  exact nat.le_of_succ_le_succ h
  end

definition ins : Π {n : ℕ}, fin (n+1) → α → α ^ n → α ^ (n + 1)
| n ⟨0,_⟩ x xs := x :: xs
| 0 ⟨i+1,hi⟩ _ _ := absurd (nat.lt_of_succ_lt_succ hi) (nat.not_lt_zero i)
| (n+1) ⟨i+1,hi⟩ x xs := xs.head :: ins ⟨i,nat.lt_of_succ_lt_succ hi⟩ x xs.tail

@[simp] lemma ins_zero {n : ℕ} (x : α) (xs : α ^ n) : ins 0 x xs = x :: xs :=
by cases n; reflexivity

@[simp] lemma ins_succ {n : ℕ} (x : α) (xs : α ^ (n+1)) :
∀ k, ins (fin.succ k) x xs = xs.head :: ins k x xs.tail :=
by cases n; intros k; cases k with k hk; simp [ins, fin.succ]

@[simp] lemma ins_succ_cons {n : ℕ} (x₀ x : α) (xs : α ^ n) (k : fin (n+1)) :
ins (fin.succ k) x₀ (x :: xs) = x :: ins k x₀ xs := by simp

@[simp] lemma ith_ins : ∀ {n : ℕ} (k : fin (n+1)) (x : α) (xs : α ^ n), (ins k x xs)[k] = x
| n ⟨0,_⟩ _ _ := by cases n; reflexivity
| 0 ⟨k+1,hk⟩ _ _ := absurd (nat.lt_of_succ_lt_succ hk) (nat.not_lt_zero k)
| (n+1) ⟨k+1,hk⟩ x xs := by simp [ins]; apply ith_ins

lemma ith_ins_of_vlt : 
∀ {n : ℕ} {k : fin (n+1)} {i : fin n},
i.val < k.val → ∀ (x : α) (xs : α ^ n), (ins k x xs)[fin.skip i] = xs[i]
| n ⟨0,_⟩ ⟨i,_⟩ := λ h, absurd h (nat.not_lt_zero i)
| 0 ⟨k+1,hk⟩ _ := absurd (nat.lt_of_succ_lt_succ hk) (nat.not_lt_zero k)
| (n+1) ⟨k+1,hk⟩ ⟨0,_⟩ := by intros; unfold ins; reflexivity
| (n+1) ⟨k+1,hk⟩ ⟨i+1,hi⟩ :=
  have fin.skip ⟨i, nat.lt_of_succ_lt_succ hi⟩ = ⟨i, nat.lt_of_succ_lt hi⟩, from rfl,
  begin
  intros h x xs,
  unfold ins,
  simp [fin.skip],
  rw [← this],
  apply ith_ins_of_vlt,
  exact nat.lt_of_succ_lt_succ h,
  end

lemma ith_ins_of_vge : 
∀ {n : ℕ} {k : fin (n+1)} {i : fin n},
i.val ≥ k.val → ∀ (x : α) (xs : α ^ n), (ins k x xs)[fin.succ i] = xs[i] 
| n ⟨0,_⟩ ⟨i,_⟩ := by intros; cases n; simp [ins]
| 0 ⟨k+1,hk⟩ _ := absurd (nat.lt_of_succ_lt_succ hk) (nat.not_lt_zero k)
| (n+1) ⟨k+1,hk⟩ ⟨0,_⟩ := λ h, absurd h (nat.not_succ_le_zero k)
| (n+1) ⟨k+1,hk⟩ ⟨i+1,hi⟩ :=
  have fin.succ ⟨i,nat.lt_of_succ_lt_succ hi⟩ = ⟨i+1,hi⟩, from rfl,
  begin
  intros h x xs,
  unfold ins,
  simp, 
  rw [← this],
  apply ith_ins_of_vge,
  exact nat.le_of_succ_le_succ h,
  end

lemma del_ins {n : ℕ} (k : fin (n+1)) (x : α) (xs : α ^ n) :
del k (ins k x xs) = xs := 
ext $ λ i,
if h : i.val < k.val then
by rw [ith_del_of_vlt h, ith_ins_of_vlt h]
else
have h : i.val ≥ k.val, from le_of_not_gt h,
by rw [ith_del_of_vge h, ith_ins_of_vge h]

lemma ins_del {n : ℕ} (k : fin (n+1)) (xs : α ^ (n+1)) :
ins k xs[k] (del k xs) = xs :=
ext $ λ i,
if h : i.val = k.val then
have heq : i = k, from fin.eq_of_veq h,
by rw [heq, ith_ins]
else if h' : i.val ≤ k.val then
have h' : i.val < k.val, from lt_of_le_of_ne h' h,
have i.val < n, from lt_of_lt_of_le h' (nat.le_of_lt_succ k.is_lt),
let i' := fin.mk i.val this in
have hlt : i'.val < k.val, from h',
have i = fin.skip i', from fin.eq_of_veq rfl,
begin
rw [this, ith_ins_of_vlt hlt, ith_del_of_vlt hlt]
end
else
have h' : k.val < i.val, from lt_of_not_ge h',
have 1 ≤ i.val, from nat.succ_le_of_lt (lt_of_le_of_lt (nat.zero_le k.val) h'),
have hi : i.val-1+1 = i.val, from nat.sub_add_cancel this,
have i.val-1 < n, from nat.lt_of_succ_lt_succ (show i.val-1+1 < n+1, from eq.substr hi i.is_lt),
let i' := fin.mk (i.val-1) this in 
have hge : i'.val ≥ k.val, from nat.le_of_lt_succ (show i'.val+1 > k.val, from eq.substr hi h'),
have i = fin.succ i', from fin.eq_of_veq $ eq.symm hi,
by rw [this, ith_ins_of_vge hge, ith_del_of_vge hge]

definition set : Π {n : ℕ}, fin n → α → α ^ n → α ^ n
| 0 k _ _ := fin.elim0 k
| (n+1) ⟨0,_⟩ x xs := x :: xs.tail
| (n+1) ⟨k+1,hk⟩ x xs := xs.head :: set ⟨k, nat.lt_of_succ_lt_succ hk⟩ x xs.tail

lemma set_zero {n : ℕ} (x : α) (xs : α ^ (n+1)) : set 0 x xs = x :: xs.tail := rfl

lemma set_succ {n : ℕ} (x : α) (xs : α ^ (n+1)) : ∀ i, set (fin.succ i) x xs = xs.head :: set i x xs.tail := λ ⟨_,_⟩, rfl

lemma ith_set : ∀ {n : ℕ} (k : fin n) (x : α) (xs : α ^ n), (set k x xs)[k] = x
| 0 k _ _ := fin.elim0 k
| (n+1) ⟨0,_⟩ x xs := by simp [set]
| (n+1) ⟨k+1,hk⟩ x xs := by simp [set]; apply ith_set

lemma ith_set_of_ne : ∀ {n : ℕ} (k i : fin n), i ≠ k → ∀ (x : α) (xs : α ^ n), (set k x xs)[i] = xs[i]
| 0 k _ _ := fin.elim0 k
| (n+1) ⟨0,_⟩ ⟨0,_⟩ h := absurd rfl h
| (n+1) ⟨0,_⟩ ⟨i+1,hi⟩ _ := by intros; simp [set]; reflexivity
| (n+1) ⟨k+1,hk⟩ ⟨0,_⟩ _ := by intros; simp [set]; reflexivity
| (n+1) ⟨k+1,hk⟩ ⟨i+1,hi⟩ h :=
  begin
  intros,
  simp [set],
  apply ith_set_of_ne,
  intros f,
  apply h,
  congr,
  exact fin.veq_of_eq f
  end

end tup
