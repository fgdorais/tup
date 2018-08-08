/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import fin

definition tup (α : Type*) (n : ℕ) := fin n → α

instance type_has_pow : has_pow (Type*) ℕ := {pow := tup}

definition ntup (α : Type*) := sigma (tup α)

namespace tup
variable {α : Type*}

abbreviation length {n : ℕ} (xs : α ^ n) : ℕ := n

abbreviation ith {n : ℕ} (xs : α ^ n) (i : fin n) : α := xs i

notation xs `[`:max_plus i `]`:0 := ith xs i

lemma ext {n : ℕ} {xs ys : α ^ n} : 
(∀ i, xs[i] = ys[i]) → xs = ys := funext

lemma ith_eq_of_veq {n : ℕ} {{i j : fin n}} : 
i.val = j.val → ∀ (xs : α ^ n), xs[i] = xs[j] :=
λ hv xs, eq.rec_on (show i = j, from fin.eq_of_veq hv) rfl

@[irreducible] definition nil : α ^ 0 := fin.elim0

@[simp] lemma eq_nil (xs : α ^ 0) : xs = nil := ext $ λ i, fin.elim0 i

@[reducible] definition const {n : ℕ} (x : α) : α ^ n := λ _, x

@[simp] lemma const_val {n : ℕ} {x : α} {i : fin n} : (const x)[i] = x := rfl

@[reducible] definition to_ntup {n : ℕ} (xs : α ^ n) : ntup α := ⟨n, xs⟩ 

end tup

namespace ntup
variable {α : Type*}

abbreviation length : ntup α → ℕ := sigma.fst

abbreviation to_tup : Π x : ntup α, α ^ (length x) := sigma.snd

@[simp] lemma to_tup_mk {n : ℕ} (xs : α ^ n) : to_tup ⟨n, xs⟩ = xs := rfl

@[reducible] definition ith : Π (nxs : ntup α) (i : fin (length nxs)), α
| ⟨_,xs⟩ i := tup.ith xs i

@[reducible] definition nil : ntup α := ⟨0, tup.nil⟩

@[simp] lemma nil_length : (@nil α).length = 0 := rfl

@[simp] lemma nil_to_tup : (@nil α).to_tup = tup.nil := rfl

lemma eq {{nxs nys : ntup α}} :
∀ (h : nxs.length = nys.length), @eq.rec _ _ _ nxs.to_tup _ h = nys.to_tup → nxs = nys := sigma.eq

lemma eq_nil {{nxs : ntup α}} : nxs.length = 0 → nxs = nil :=
λ h, eq h $ tup.eq_nil _

end ntup

