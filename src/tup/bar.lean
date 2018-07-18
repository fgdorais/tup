/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons .append

namespace tup
variable {α : Type*}

@[reducible]
definition bar (f : ℕ → α) (n : ℕ) : fin n → α
| ⟨i,_⟩ := f i

@[simp]
lemma bar_val (f : ℕ → α) {n : ℕ} : 
∀ i, (bar f n)[i] = f i.val
| ⟨_,_⟩ := rfl

lemma take_bar (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
take h (bar f n) = bar f m :=
tup.ext (λ _, by simp)

definition extend {n : ℕ} (xs : α ^ n) (x : α) (i : ℕ) : α :=
if h : i < n then xs[⟨i,h⟩] else x

lemma extend_of_lt {n : ℕ} {xs : α ^ n} {x : α} {i : ℕ} (h : i < n) :
extend xs x i = xs[⟨i,h⟩] := dif_pos h

lemma extend_of_ge {n : ℕ} {xs : α ^ n} {x : α} {i : ℕ} (h : i ≥ n) :
extend xs x i = x := dif_neg (not_lt_of_ge h)

lemma bar_extend {n : ℕ} {xs : α ^ n} {x : α} :
bar (extend xs x) n = xs :=
ext (λ ⟨i,h⟩, extend_of_lt h)

end tup