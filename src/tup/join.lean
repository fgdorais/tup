/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons .append .sumprod .map

variable {α : Type*}

definition ntup.join {n : ℕ} : ntup α ^ n → ntup α := tup.join

definition ntup.join_length {n : ℕ} (ts : ntup α ^ n) : ℕ := (ntup.join ts).length

#exit

definition fin.step : 
Π {m : ℕ} (ns : ℕ ^ m) (i : fin m) (j : fin ns[i]), fin (tup.sum' ns)
| 0 _ i _ := 
  fin.elim0 i
| (m+1) ns ⟨0,_⟩ j := 
  fin.lift (tup.sum' ns.tail) j
| (m+1) ns ⟨i+1,ih⟩ j := 
  fin.push ns.head (fin.step ns.tail ⟨i, nat.lt_of_succ_lt_succ ih⟩ j)

lemma ntup.join_val :
∀ {m : ℕ} (nxs : (ntup α) ^ m) (i : fin m) (j : fin nxs[i].length), 
(ntup.join nxs).to_tup[fin.step (tup.map ntup.length nxs) i j] = nxs.to_tup[i].to_tup[j]
| 0 _ i _ :=
  fin.elim0 i
| (m+1) ns ⟨0,_⟩ j :=
  begin 
  simp [tup.join, fin.step]
  end
| (m+1) ns ⟨i+1,_⟩ j :=
  by simp [tup.join, fin.step, tup.join_val]; reflexivity
