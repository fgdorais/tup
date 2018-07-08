/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

theorem fin.choice : Π {n : ℕ} {C : fin n → Sort*}, 
(∀ i, nonempty (C i)) → nonempty (Π i, C i)
| 0 _ _ := nonempty.intro (λ i, fin.elim0 i)
| (n+1) C h := 
  have h0 : nonempty (C 0), from h 0,
  have hs : nonempty (Π i, C (fin.succ i)), from fin.choice (λ i, h (fin.succ i)),
  nonempty.elim hs $ nonempty.elim h0 $ λ c0 cs, 
  nonempty.intro $ λ i, 
  match i with
  | ⟨0, _⟩ := c0
  | ⟨i+1, h⟩ := cs ⟨i, nat.lt_of_succ_lt_succ h⟩ 
  end
