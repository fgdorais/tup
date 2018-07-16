/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

namespace tup
variables {α : Type*} {n : ℕ}

definition cons : α → α ^ n → α ^ (n + 1)
| x _ ⟨0, _⟩ := x
| _ xs ⟨i+1, h⟩ := xs[⟨i, nat.lt_of_succ_lt_succ h⟩]

notation x :: xs := cons x xs

@[simp] 
lemma cons_val_zero {x : α} {xs : α ^ n} : 
(x :: xs)[0] = x := rfl

@[simp] 
lemma cons_val_succ {x : α} {xs : α ^ n} : 
∀ {i : fin n}, (x :: xs)[fin.succ i] = xs[i] := λ ⟨_, _⟩, rfl

@[reducible] 
definition head : α ^ (n+1) → α := λ xs, xs[0]

@[simp] 
lemma head_cons {x : α} {xs : α ^ n} : 
head (x :: xs) = x := rfl

definition head_of_nonzero (h : n ≠ 0) : α ^ n → α :=
match n, h with 
| 0, h := absurd rfl h
| (n+1), _ := head
end

@[reducible] 
definition tail {n : ℕ} : α ^ (n+1) → α ^ n := λ t i, t[fin.succ i]

@[simp] 
lemma tail_cons {n : ℕ} {x : α} {xs : α ^ n} : 
tail (x :: xs) = xs := ext (λ ⟨_,_⟩, rfl)

definition tail_of_nonzero (h : n ≠ 0) : α ^ n → α ^ (n-1) :=
match n, h with
| 0, h := absurd rfl h
| (n+1), _ := tail
end

@[simp]
lemma cons_head_tail (xs : α ^ (n+1)) :
head xs :: tail xs = xs := 
ext (λ i, match i with
| ⟨0,_⟩ := rfl
| ⟨i+1,_⟩ := rfl
end)

end tup

notation `⟪` l:(foldr `, ` (h t, tup.cons h t) tup.nil `⟫`) := l

section rec
universe u
variables {α : Type u} {C : Π {n : ℕ}, α ^ n → Sort*}
open tup

@[recursor 6] 
definition tup.cons_rec :
C nil → (Π (x : α) {n : ℕ} (xs : α ^ n), C xs → C (x :: xs)) → (Π {n : ℕ} (xs : tup.{u} α n), C xs) 
| h0 _ 0 xs := eq.rec_on (eq.symm (eq_nil xs)) h0
| h0 hs (n+1) xs := eq.rec_on (cons_head_tail xs) (hs (head xs) (tail xs) (tup.cons_rec h0 hs (tail xs)))

@[elab_as_eliminator] 
definition tup.cons_rec_on {n : ℕ} (xs : α ^ n) :
C nil → (Π (x : α) {n : ℕ} (xs : α ^ n), C xs → C (x :: xs)) → C xs :=
assume h0 hs, tup.cons_rec h0 hs xs

end rec
