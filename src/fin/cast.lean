/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

namespace fin
variables {l m n : ℕ}

@[reducible] definition cast : m ≤ n → fin m → fin n | h ⟨i,hi⟩ := ⟨i, lt_of_lt_of_le hi h⟩

@[simp] lemma cast_mk (h : m ≤ n) (i : ℕ) (hi : i < m) : cast h ⟨i,hi⟩ = ⟨i, lt_of_lt_of_le hi h⟩ := rfl

@[simp] lemma cast_val (h : m ≤ n) : ∀ i, (cast h i).val = i.val | ⟨_,_⟩ := rfl 

@[simp] lemma cast_refl : ∀ i, cast (le_refl n) i = i | ⟨_,_⟩ := rfl

@[simp] lemma cast_trans {l m n : ℕ} {{hlm : l ≤ m}} {{hmn : m ≤ n}} :
∀ i, cast hmn (cast hlm i) = cast (le_trans hlm hmn) i | ⟨_,_⟩ := rfl

lemma cast_inj {i j : fin m} {h : m ≤ n} : cast h i = cast h j → i = j :=
begin 
intro hc, 
apply eq_of_veq,
rw [← cast_val h, ← cast_val h],
apply veq_of_eq hc,
end

@[simp] lemma cast_irrel (i : fin m) (h h' : m ≤ n) : 
cast h i = cast h' i := by apply eq_of_veq; simp

@[simp] lemma cast_zero {m n : ℕ} {h : m + 1 ≤ n + 1} : cast h 0 = 0 := rfl

private lemma push_lem : m ≤ n → (∀ {i : ℕ}, i < m → n - m + i < n) :=
λ hmn i hi, 
calc n - m + i < n - m + m : nat.add_lt_add_left hi (n - m)
         ... = n : nat.sub_add_cancel hmn

@[reducible] definition push : m ≤ n → fin m → fin n :=
λ h ⟨i,hi⟩, ⟨n - m + i, push_lem h hi⟩

@[simp] lemma push_mk (h : m ≤ n) (i : ℕ) (hi : i < m) : push h ⟨i,hi⟩ = ⟨n - m + i, push_lem h hi⟩ := rfl

@[simp] lemma push_val (h : m ≤ n) : ∀ i, (push h i).val = (n - m) + i.val | ⟨_,_⟩ := rfl

@[simp] lemma push_refl : ∀ i, push (nat.le_refl n) i = i := 
λ ⟨i,hi⟩, eq_of_veq $
calc (n - n) + i
    = 0 + i : by rw nat.sub_self
... = i : by rw nat.zero_add

@[simp] lemma push_trans {l m n : ℕ} {{hlm : l ≤ m}} {{hmn : m ≤ n}} :
∀ i, push hmn (push hlm i) = push (le_trans hlm hmn) i :=
λ ⟨i,hi⟩, eq_of_veq $
have (n - m) + (m - l) = n - l, from 
calc (n - m) + (m - l)
    = (n + (m - l)) - m : by rw nat.sub_add_comm hmn
... = ((n + m) - l) - m : by rw nat.add_sub_assoc hlm
... = ((n + m) - (l + m)) : by rw nat.sub_sub
... = n - l : by rw nat.add_sub_add_right,
calc (n - m) + ((m - l) + i)
    = (n - m) + (m - l) + i : by rw add_assoc
... = (n - l) + i : by rw this

lemma push_inj {{h : m ≤ n}} : ∀ {i j : fin m}, push h i = push h j → i = j
| ⟨i,hi⟩ ⟨j,hj⟩ hp :=
  have (n - m) + i = (n - m) + j, from veq_of_eq hp,  
  eq_of_veq $ nat.add_left_cancel this

@[simp] lemma push_irrel (i : fin m) (h h' : m ≤ n) : 
push h i = push h' i := by apply eq_of_veq; simp

lemma push_zero (h : m+1 ≤ n+1) : push h 0 = ⟨n-m, lt_of_le_of_lt (nat.sub_le n m) (nat.lt_succ_self n)⟩ :=
eq_of_veq $ 
calc ((n+1) - (m+1)) + 0
    = (n - m) + 0 : by rw nat.succ_sub_succ
... = n - m : by rw nat.add_zero

@[simp] lemma eq_rec_eq_cast : 
Π {m n : ℕ} (h : m = n) (i : fin m), @eq.rec _ _ _ i _ h = cast (le_of_eq h) i
| _ ._ rfl i := by simp

end fin