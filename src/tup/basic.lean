/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

definition tup (α : Type*) (n : ℕ) := fin n → α

instance type_has_pow : has_pow Type* ℕ := {pow := tup}

namespace tup
variable {α : Type*}

@[reducible]
definition ith {n : ℕ} (xs : α ^ n) (i : fin n) : α := xs i

notation xs `[`:max_plus i `]`:0 := ith xs i

lemma ext {n : ℕ} {xs ys : α ^ n} : 
(∀ i, xs[i] = ys[i]) → xs = ys := funext

@[reducible] 
definition const {n : ℕ} (x : α) : α ^ n := λ _, x

@[simp]
lemma const_val {n : ℕ} {x : α} {i : fin n} : (const x)[i] = x := rfl

end tup

