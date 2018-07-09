/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

end ntup

