/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace fin
variables {l m n : ℕ}

@[reducible] 
definition cast : m = n → fin m → fin n
| h ⟨i,hi⟩ := ⟨i, eq.rec_on h hi⟩

@[simp] lemma cast_rfl : 
∀ (i : fin n), cast rfl i = i
| ⟨_,_⟩ := rfl

@[simp] lemma cast_trans : 
∀ {l m n : ℕ} {hlm : l = m} {hmn : m = n} (i : fin l), cast hmn (cast hlm i) = cast (eq.trans hlm hmn) i
| _ ._ ._ rfl rfl ⟨_,_⟩ := rfl

lemma eq_cast_symm_of_cast_eq :
∀ {m n : ℕ} {i : fin m} {j : fin n} (h : m = n), 
cast h i = j → i = cast (eq.symm h) j
| _ ._ i j rfl := by simp; exact id

lemma cast_inj :
∀ {m n : ℕ} {i j : fin m} {h : m = n}, cast h i = cast h j → i = j 
| _ ._ i j rfl := by simp; exact id

@[simp] lemma cast_irrel :
∀ {m n : ℕ} (i : fin m) (h h' : m = n), cast h i = cast h' i
| _ ._ i rfl rfl := rfl

@[simp] lemma val_cast {m n : ℕ} :
∀ (i : fin m) (h : m = n), (cast h i).val = i.val
| ⟨_,_⟩ _ := rfl

@[simp] lemma cast_mk {m n : ℕ} (i : ℕ) (hi : i < m) (h : m = n) :
cast h (mk i hi) = mk i (eq.subst h hi) := rfl

@[simp] lemma cast_zero {m n : ℕ} {h : m + 1 = n + 1} : cast h 0 = 0 := rfl

@[simp] lemma eq_rec_eq_cast : 
Π {m n : ℕ} (h : m = n) (i : fin m), 
@eq.rec _ _ _ i _ h = cast h i
| _ ._ rfl i := by simp

@[simp] lemma eq_rec_fun_eq_fun_cast {α : ℕ → Sort*} {f : Π (n : ℕ), fin n → α n} :
∀ {m n : ℕ} (i : fin m) (h : m = n), @eq.rec ℕ m _ (f m i) n h = f n (cast h i)
| _ ._ i rfl := by simp

lemma cast_heq : ∀ {m n : ℕ} (i : fin m) (h : m = n), cast h i == i
| _ ._ i rfl := by simp; exact heq.refl i

end fin