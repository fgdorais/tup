/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons

open tup

lemma tup.choice {α : Type*} : ∀ {n : ℕ} {p : fin n → α → Prop}, 
(∀ i, ∃ x : α, p i x) → (∃ xs : α ^ n, ∀ i : fin n, p i xs[i])
| 0 _ _ := ⟨nil, (λ i, fin.elim0 i)⟩
| (n+1) p h :=
  let p' := λ (i : fin n) (x : α), p (fin.succ i) x in
  have (∃ xs : α ^ n, ∀ i : fin n, p' i xs[i]),
  from tup.choice (λ i, h (fin.succ i)),
  exists.elim this (λ xs hxs, exists.elim (h 0) (λ x hx, 
    exists.intro (x :: xs) (λ i, match i with
    | ⟨0, _⟩ := hx
    | ⟨i+1, h⟩ := hxs ⟨i, nat.lt_of_succ_lt_succ h⟩
    end)))
