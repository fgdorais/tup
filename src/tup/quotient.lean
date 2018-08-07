/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons .map

instance tup_setoid {α : Type*} [s : setoid α] {n : ℕ} : setoid (α ^ n) := 
let tr := λ (xs ys : α ^ n), ∀ (i : fin n), @setoid.r α s xs[i] ys[i] in
have trefl : ∀ (xs : α ^ n), tr xs xs, 
from (λ xs i, setoid.refl xs[i]),
have tsymm : ∀ {{xs ys : α ^ n}}, tr xs ys → tr ys xs, 
from (λ xs ys h i, setoid.symm (h i)),
have ttrans : ∀ {{xs ys zs : α ^ n}}, tr xs ys → tr ys zs → tr xs zs, 
from (λ xs ys ys hxy hyz i, setoid.trans (hxy i) (hyz i)),
⟨tr, trefl, tsymm, ttrans⟩

lemma tup.setoid_cons {α : Type*} [s : setoid α] {n : ℕ} {x y : α} {xs ys : α ^ n} :
x ≈ y → xs ≈ ys → x :: xs ≈ y :: ys :=
assume h hs, (λ i, match i with
| ⟨0, _⟩ := h
| ⟨i+1, _⟩ := hs ⟨i, _⟩
end)

namespace quotient
variables {α : Type*} [s : setoid α] {β : Sort*}
include s
open tup

definition tup_lift : Π {n : ℕ} (f : α ^ n → β),
(∀ xs ys : α ^ n, xs ≈ ys → f xs = f ys) → quotient s ^ n → β
| 0 f _ _ := f nil
| (n+1) f c qs := 
  let f' := (λ x xs, f (x :: xs)) in
  have c' : ∀ x y : α, x ≈ y → f' x = f' y, 
  from λ x y hxy, funext (λ zs, c (x :: zs) (y :: zs) (setoid_cons hxy (setoid.refl zs))),
  have ∀ (x y : α) (xs ys : α ^ n), x ≈ y → xs ≈ ys → quotient.lift f' c' (quotient.mk x) xs = quotient.lift f' c' (quotient.mk y) ys,
  from λ x y xs ys hxy hxys, c (x :: xs) (y :: ys) (setoid_cons hxy hxys),
  have ∀ (xs ys : α ^ n), xs ≈ ys → quotient.lift f' c' (head qs) xs = quotient.lift f' c' (head qs) ys,
  from quotient.induction_on (head qs) (λ z xs ys hxy, c (z :: xs) (z :: ys) (setoid_cons (setoid.refl z) hxy)),
  tup_lift (quotient.lift f' c' (head qs)) this (tail qs)

theorem lift_beta (f : α → β) (c : ∀ (x y : α), x ≈ y → f x = f y) (x : α) : 
quotient.lift f c (quotient.mk x) = f x := rfl

theorem tup_lift_beta : 
Π {n : ℕ} (f : α ^ n → β) (c : ∀ xs ys : α^n, xs ≈ ys → f xs = f ys) (zs : α ^ n),
tup_lift f c (map quotient.mk zs) = f zs
| 0 f c zs := by rw eq_nil zs; reflexivity
| (n+1) f c zs :=
  let f' := (λ x xs, f (x :: xs)) in 
  have c' : ∀ x y : α, x ≈ y → f' x = f' y, 
  from λ x y hxy, funext (λ zs, c (x :: zs) (y :: zs) (setoid_cons hxy (setoid.refl zs))),
  let qs := map quotient.mk zs in calc
  tup_lift f c qs 
      = tup_lift (quotient.lift f' c' (head qs)) _ (tail qs) : rfl
  ... = tup_lift (quotient.lift f' c' (head qs)) _ (map quotient.mk (tail zs)) : by rw map_tail
  ... = quotient.lift f' c' (head qs) (tail zs) : tup_lift_beta _ _ _
  ... = quotient.lift f' c' (quotient.mk (head zs)) (tail zs) : by rw map_head
  ... = f' (head zs) (tail zs) : rfl
  ... = f (head zs :: tail zs) : rfl
  ... = f zs : by rw cons_head_tail zs

end quotient
