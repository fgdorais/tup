/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons fin.choice

lemma tup.choice {α : Type*} {n : ℕ} {p : fin n → α → Prop} : 
(∀ i, ∃ x : α, p i x) → (∃ xs : α ^ n, ∀ i : fin n, p i xs[i]) :=
assume h,
have nonempty (Π i, { x : α // p i x }),
from fin.choice (λ i, exists.elim (h i) (λ x hx, nonempty.intro ⟨x, hx⟩)),
nonempty.elim this (λ z, ⟨λ i, (z i).val, λ i, (z i).property⟩)
