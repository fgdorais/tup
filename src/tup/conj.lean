/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic fin.extra

namespace tup
variables {α : Type*} {n : ℕ}

definition conj : α ^ n → α → α ^ (n + 1) :=
λ xs x ⟨i,_⟩, if h : i < n then xs[⟨i,h⟩] else x

notation xs && x := conj xs x

lemma conj_val_of_lt {x : α} {xs : α ^ n} :
∀ {i : fin (n+1)} (h : i.val < n), (conj xs x)[i] = xs[⟨i.val,h⟩]
| ⟨i,hi⟩ h := dif_pos h

lemma conj_val_of_ge {x : α} {xs : α ^ n} :
∀ {i : fin (n+1)} (h : i.val ≥ n), (conj xs x)[i] = x
| ⟨i,hi⟩ h := dif_neg (not_lt_of_ge h)

@[simp] 
lemma conj_last {x : α} {xs : α ^ n} : 
(conj xs x)[fin.last n] = x := 
conj_val_of_ge (le_refl n)

@[simp] 
lemma conj_lift {x : α} {xs : α ^ n} : 
∀ {i : fin n}, (conj xs x)[fin.lift 1 i] = xs[i] := 
λ ⟨i, ih⟩, conj_val_of_lt ih

@[reducible] 
definition last : α ^ (n+1) → α := 
λ xs, xs[fin.last n]

@[reducible] 
definition left : α ^ (n+1) → α ^ n := 
λ xs i, xs[fin.lift 1 i]

definition last_of_nonzero (h : n ≠ 0) : α ^ n → α :=
match n, h with 
| 0, h := absurd rfl h
| (n+1), _ := last
end

definition left_of_nonzero (h : n ≠ 0) : α ^ n → α ^ (n-1) :=
match n, h with
| 0, h := absurd rfl h
| (n+1), _ := left
end

@[simp] 
lemma last_conj {x : α} {xs : α ^ n} : 
last (xs && x) = x := 
conj_last

@[simp] 
lemma left_conj {x : α} {xs : α ^ n} : 
left (xs && x) = xs := 
ext (λ _, conj_lift)

lemma conj_left_last (xs : α ^ (n + 1)) :
left xs && last xs = xs :=
ext $ λ ⟨i,hi⟩,
if h : i < n then
  conj_val_of_lt h
else
  have fin.last n = ⟨i,hi⟩, 
  from fin.eq_of_veq (le_antisymm (le_of_not_gt h) (nat.le_of_lt_succ hi)),
  by rw [← this, conj_last]

end tup

#exit

section rec
universe u
variables {α : Type u} {C : Π {n : ℕ}, α ^ n → Sort*}
open tup

@[recursor 6] 
definition tup.conj_rec :
C nil → (Π {n : ℕ} (xs : α ^ n) (x : α), C xs → C (xs && x)) → (Π {n : ℕ} (xs : tup.{u} α n), C xs) 
| h0 _ 0 xs := eq.rec_on (eq.symm (eq_nil xs)) h0
| h0 hs (n+1) xs := eq.rec_on (conj_left_last xs) (hs (left xs) (last xs) (tup.conj_rec h0 hs (left xs)))

@[elab_as_eliminator] 
definition tup.conj_rec_on {n : ℕ} (xs : α ^ n) :
C nil → (Π {n : ℕ} (xs : α ^ n) (x : α), C xs → C (xs && x)) → C xs :=
assume h0 hs, tup.conj_rec h0 hs xs

end rec
