/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

namespace fin

definition cases_lift_last {n : ℕ} {C : fin (n+1) → Sort*} :
(Π i, C (fin.lift i)) → C (fin.last n) → (Π i, C i) :=
λ hl h ⟨i,hi⟩,
if hin : i = n then 
have fin.mk i hi = fin.last n, from fin.eq_of_veq hin,
show C ⟨i,hi⟩, from eq.rec_on (eq.symm this) h 
else
let j := fin.mk i (lt_of_le_of_ne (nat.le_of_lt_succ hi) hin) in
have fin.mk i hi = fin.lift j, from fin.eq_of_veq rfl,
show C ⟨i,hi⟩, from eq.rec_on (eq.symm this) (hl j)

@[simp] lemma cases_lift {n : ℕ} {C : fin (n+1) → Sort*} (hl : Π i, C (fin.lift i)) (h : C (fin.last n)) :
∀ i, cases_lift_last hl h (fin.lift i) = hl i | ⟨i,hi⟩ := dif_neg (ne_of_lt hi)

@[simp] lemma cases_last {n : ℕ} {C : fin (n+1) → Sort*} (hl : Π i, C (fin.lift i)) (h : C (fin.last n)) :
cases_lift_last hl h (fin.last n) = h := dif_pos rfl

@[reducible] definition cases_lift_last_on {n : ℕ} {C : fin (n+1) → Sort*} (i : fin (n+1)) :
(Π i, C (fin.lift i)) → C (fin.last n) → C i :=
λ hl h, fin.cases_lift_last hl h i

definition rec_lift_last {C : Π {n : ℕ}, fin n → Sort*} :
(Π {n : ℕ} (i : fin n), C i → C (fin.lift i)) → (Π n, C (fin.last n)) → (Π {n : ℕ} (i : fin n), C i) :=
λ hnl hn n, nat.rec_on n (λ i, fin.elim0 i) $
λ n ih, cases_lift_last (λ i, hnl i (ih i)) (hn n)

@[simp] lemma rec_lift {C : Π {n : ℕ}, fin n → Sort*} {hl : Π {n : ℕ} (i : fin n), C i → C (fin.lift i)} {h : Π n, C (fin.last n)} :
∀ {n : ℕ} (i : fin n), rec_lift_last @hl h (fin.lift i) = hl i (rec_lift_last @hl h i) | _ ⟨i,hi⟩ := dif_neg (ne_of_lt hi)

@[simp] lemma rec_last {C : Π {n : ℕ}, fin n → Sort*} {hl : Π {n : ℕ} (i : fin n), C i → C (fin.lift i)} {h : Π n, C (fin.last n)} :
∀ (n : ℕ), rec_lift_last @hl h (fin.last n) = h n | _ := dif_pos rfl

@[reducible] definition rec_lift_last_on {C : Π {n : ℕ}, fin n → Sort*} {n : ℕ} (i : fin n) :
(Π (n : ℕ) (i : fin n), C i → C (fin.lift i)) → (Π (n : ℕ), C (fin.last n)) → C i :=
λ hl h, rec_lift_last hl h i

end fin
