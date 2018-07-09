/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons .append .sumprod .map

variable {α : Type*}

@[reducible]
definition tup.join :
Π {n : ℕ} (nxs : (ntup α) ^ n), α ^ (tup.sum (tup.map ntup.length nxs))
| 0 _ := tup.nil
| (n+1) nxs := ntup.to_tup (nxs.head) ++ tup.join nxs.tail

@[reducible]
definition ntup.join {n : ℕ} (nxs : (ntup α) ^ n) : ntup α :=
⟨tup.sum (tup.map ntup.length nxs), tup.join nxs⟩ 

@[simp]
lemma tup.join_nil : tup.join tup.nil = @tup.nil α := rfl
