/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

namespace tup
variables {α : Type*} {m n : ℕ}

@[reducible] definition cast (h : m = n) : α ^ m → α ^ n :=
λ xs i, xs[fin.cast (eq.symm h) i]

@[simp] lemma val_cast (h : m = n) (xs : α ^ m) :
∀ i, (tup.cast h xs)[i] = xs[fin.cast (eq.symm h) i] := λ i, rfl

@[simp] lemma val_mk_cast (h : m = n) (xs : α ^ m) (i : ℕ) (hi : i < n) : 
(tup.cast h xs)[⟨i,hi⟩] = xs[⟨i, eq.substr h hi⟩] := rfl

@[simp] lemma cast_refl {n : ℕ} (xs : α ^ n) : cast rfl xs = xs := by simp [cast]

@[simp] lemma cast_trans :
∀ {l m n : ℕ} (xs : α ^ l) (hlm : l = m) (hmn : m = n),
cast hmn (cast hlm xs) = cast (eq.trans hlm hmn) xs
| n .(n) .(n) xs rfl rfl := by simp

@[simp] lemma cast_rfl {n : ℕ} (xs : α ^ n) (h : n = n) : cast h xs = xs := by simp

lemma eq_cast_symm_of_cast_eq :
∀ {m n : ℕ} {xs : α ^ m} {ys : α ^ n} {h : m = n},
cast h xs = ys → xs = cast (eq.symm h) ys
| n .(n) xs ys rfl := by simp; exact id

lemma cast_symm_eq_of_eq_cast :
∀ {m n : ℕ} {xs : α ^ m} {ys : α ^ n} {h : n = m},
xs = cast h ys → cast (eq.symm h) xs = ys
| n .(n) xs ys rfl := by simp; exact id

lemma cast_inj :
∀ {m n} (xs₁ xs₂ : α ^ m) (h : m = n), cast h xs₁ = cast h xs₂ → xs₁ = xs₂
| n .(n) xs ys rfl := by simp; exact id

@[simp] lemma cast_irrel :
∀ {m n} (xs : α ^ m) (h₁ h₂ : m = n), cast h₁ xs = cast h₂ xs
| n .(n) xs rfl rfl := by simp

lemma cast_ext : ∀ {m n : ℕ} {xs : α ^ m} {ys : α ^ n} {h : n = m},
(∀ i, xs[fin.cast h i] = ys[i]) → xs = cast h ys 
| _ ._ xs ys rfl := by simp; exact ext

@[simp] lemma eq_rec_eq_cast : 
Π {m n : ℕ} (h : m = n) (xs : α ^ m), 
@eq.rec _ _ _ xs _ h = cast h xs
| _ ._ rfl xs := by simp

@[simp] lemma eq_rec_fun_eq_fun_cast {β : ℕ → Sort*} {f : Π (n : ℕ), α ^ n → β n} :
∀ {m n : ℕ} (xs : α ^ m) (h : m = n), @eq.rec ℕ m _ (f m xs) n h = f n (cast h xs)
| _ ._ i rfl := by simp

lemma cast_heq : ∀ {m n : ℕ} (xs : α ^ m) (h : m = n), cast h xs == xs
| _ ._ xs rfl := by simp; exact heq.refl xs

end tup