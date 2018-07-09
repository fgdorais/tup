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

definition fin.step : 
Π {m : ℕ} (ns : ℕ ^ m) (i : fin m) (j : fin ns[i]), fin (tup.sum ns)
| 0 _ i _ := 
  fin.elim0 i
| (m+1) ns ⟨0,_⟩ j := 
  fin.lift_by (tup.sum ns.tail) j
| (m+1) ns ⟨i+1,ih⟩ j := 
  fin.push_by ns.head (fin.step ns.tail ⟨i, nat.lt_of_succ_lt_succ ih⟩ j)

lemma tup.join_val :
∀ {m : ℕ} (nxs : (ntup α) ^ m) (i : fin m) (j : fin nxs[i].length), 
(tup.join nxs)[fin.step (tup.map ntup.length nxs) i j] = nxs[i].to_tup[j]
| 0 _ i _ :=
  fin.elim0 i
| (m+1) ns ⟨0,_⟩ j :=
  by simp [tup.join, fin.step]; reflexivity
| (m+1) ns ⟨i+1,_⟩ j :=
  by simp [tup.join, fin.step, tup.join_val]; reflexivity
