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

@[reducible] 
definition ith : Π (nxs : ntup α) (i : fin (length nxs)), α
| ⟨_,xs⟩ i := tup.ith xs i

definition nil : ntup α := ⟨0, tup.nil⟩

lemma eq {{nxs nys : ntup α}} (h : nxs.length = nys.length) : tup.cast h nxs.to_tup = nys.to_tup → nxs = nys :=
assume hc,
have @eq.rec_on _ _ _ _ h nxs.to_tup = nys.to_tup,
from eq.trans (tup.eq_rec_on_eq_cast h nxs.to_tup) hc,
sigma.eq h this

lemma eq_nil {{nxs : ntup α}} : nxs.length = 0 → nxs = nil :=
assume h, eq h (tup.ext $ λ i, fin.elim0 i)

end ntup

