/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import fin

definition tup (α : Type*) (n : ℕ) := fin n → α

instance type_has_pow : has_pow Type* ℕ := {pow := tup}

definition ntup (α : Type*) := sigma (tup α)

namespace tup
variable {α : Type*}

@[reducible]
definition length {n : ℕ} (xs : α ^ n) : ℕ := n

@[reducible]
definition ith {n : ℕ} (xs : α ^ n) (i : fin n) : α := xs i

notation xs `[`:max_plus i `]`:0 := ith xs i

lemma ext {n : ℕ} {xs ys : α ^ n} : 
(∀ i, xs[i] = ys[i]) → xs = ys := funext

@[reducible]
definition cast {m n : ℕ} (h : m = n) : α ^ m → α ^ n :=
λ xs i, xs[fin.cast (eq.symm h) i]

@[simp]
lemma cast_val {m n : ℕ} (h : m = n) (xs : α ^ m) (i : fin n) :
(tup.cast h xs)[i] = xs[fin.cast (eq.symm h) i] := rfl

@[simp]
lemma cast_rfl {n : ℕ} (xs : α ^ n) : cast rfl xs = xs := rfl

@[simp]
lemma cast_trans :
∀ {l m n : ℕ} (xs : α ^ l) (hlm : l = m) (hmn : m = n),
cast hmn (cast hlm xs) = cast (eq.trans hlm hmn) xs
| n .(n) .(n) xs rfl rfl := rfl

lemma eq_cast_symm_of_cast_eq :
∀ {m n : ℕ} {xs : α ^ m} {ys : α ^ n} {h : m = n},
cast h xs = ys → xs = cast (eq.symm h) ys
| n .(n) xs ys rfl := id

lemma cast_symm_eq_of_eq_cast :
∀ {m n : ℕ} {xs : α ^ m} {ys : α ^ n} {h : n = m},
xs = cast h ys → cast (eq.symm h) xs = ys
| n .(n) xs ys rfl := id

lemma eq_rec_on_eq_cast : 
Π {m n : ℕ} (h : m = n) (xs : α ^ m), 
@eq.rec_on _ _ _ _ h xs = cast h xs
| m .(m) rfl xs := rfl

@[irreducible]
definition nil : α ^ 0 := fin.elim0

lemma eq_nil (xs : α ^ 0) : xs = nil :=
funext (λ i, fin.elim0 i)

@[reducible] 
definition const {n : ℕ} (x : α) : α ^ n := λ _, x

@[simp]
lemma const_val {n : ℕ} {x : α} {i : fin n} : (const x)[i] = x := rfl

@[reducible]
definition to_ntup {n : ℕ} (xs : α ^ n) : ntup α := ⟨n, xs⟩ 

end tup

namespace ntup
variable {α : Type*}

@[reducible]
definition length : ntup α → ℕ := sigma.fst

@[reducible]
definition to_tup : Π x : ntup α, α ^ (length x) := sigma.snd

@[simp]
lemma to_tup_mk {n : ℕ} (xs : α ^ n) : to_tup ⟨n,xs⟩ = xs := rfl

@[reducible] 
definition ith : Π (nxs : ntup α) (i : fin (length nxs)), α
| ⟨_,xs⟩ i := tup.ith xs i

definition nil : ntup α := ⟨0, tup.nil⟩

@[simp]
lemma nil_length : (@nil α).length = 0 := rfl

@[simp]
lemma nil_to_tup : (@nil α).to_tup = tup.nil := rfl

lemma eq {{nxs nys : ntup α}} (h : nxs.length = nys.length) : tup.cast h nxs.to_tup = nys.to_tup → nxs = nys :=
assume hc,
have @eq.rec_on _ _ _ _ h nxs.to_tup = nys.to_tup,
from eq.trans (tup.eq_rec_on_eq_cast h nxs.to_tup) hc,
sigma.eq h this

lemma eq_nil {{nxs : ntup α}} : nxs.length = 0 → nxs = nil :=
assume h, eq h (tup.ext $ λ i, fin.elim0 i)

end ntup

