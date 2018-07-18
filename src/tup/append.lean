/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons fin.extra

namespace tup
variables {α : Type*} {l m n : ℕ}

definition append : α ^ m → α ^ n → α ^ (m + n)
| xs ys ⟨i, h⟩ := 
  if hm : i < m then
    xs ⟨i, hm⟩
  else
    ys ⟨i - m, nat.sub_lt_of_lt_add_of_ge (le_of_not_gt hm) h⟩

infixl ` ⊔ `:65 := append

lemma ith_append_of_lt {xs : α ^ m} {ys : α ^ n} {i : ℕ} (h : i < m) : 
(xs ⊔ ys)[⟨i, nat.lt_add_right i m n h⟩] = xs[⟨i,h⟩] := dif_pos h

lemma ith_append_of_ge {xs : α ^ m} {ys : α ^ n} {i : ℕ} (h : i < m+n) (hm : i ≥ m) :
(xs ⊔ ys)[⟨i, h⟩] = ys[⟨i-m, nat.sub_lt_of_lt_add_of_ge hm h⟩] := dif_neg (not_lt_of_ge hm)


@[simp]
lemma append_lift_by {xs : α ^ m} {ys : α ^ n} :
∀ i, (xs ⊔ ys)[fin.lift_by n i] = xs[i]
| ⟨i, h⟩ := ith_append_of_lt h

@[simp]
lemma append_push_by {xs : α ^ m} {ys : α ^ n} :
∀ i : fin n, (xs ⊔ ys)[fin.push_by m i] = ys[i]
| ⟨i, h⟩ := 
  calc
  (xs ⊔ ys)[⟨m+i, nat.add_lt_add_left h m⟩] 
      = ys[⟨(m+i)-m, _⟩] : ith_append_of_ge (nat.add_lt_add_left h m) (nat.le_add_right m i)
  ... = ys[⟨i, h⟩]       : by simp [nat.add_sub_cancel']

lemma append_nil (xs : α ^ n) : xs ⊔ nil = xs :=
ext (λ ⟨i,hi⟩, ith_append_of_lt hi)

lemma nil_append (xs : α ^ n) : tup.cast (nat.zero_add n) (nil ⊔ xs) = xs :=
have ∀ (i : fin n), fin.cast (eq.symm (nat.zero_add n)) i = fin.push_by 0 i, 
from λ ⟨i, hi⟩, fin.eq_of_veq $ by simp,
ext $ λ i, by simp [this]

lemma append_assoc (xs : α ^ l) (ys : α ^ m) (zs : α ^ n) :
cast (nat.add_assoc l m n) ((xs ⊔ ys) ⊔ zs) = xs ⊔ (ys ⊔ zs) :=
ext $ λ ⟨i, hi⟩,
if hil : i < l then
  have hc : fin.cast (eq.symm (nat.add_assoc l m n)) ⟨i,hi⟩ = fin.lift_by n (fin.lift_by m ⟨i,hil⟩), 
  from fin.eq_of_veq $ by simp,
  by simp [hc, ith_append_of_lt hil]
else if him : i < l + m then
  have hc : fin.cast (eq.symm (nat.add_assoc l m n)) ⟨i,hi⟩ = fin.lift_by n ⟨i,him⟩, 
  from fin.eq_of_veq $ by simp,
  have hilm : i - l < m, 
  from nat.sub_lt_of_lt_add_of_ge (le_of_not_gt hil) him,
  by simp [hc, ith_append_of_ge _ (le_of_not_gt hil), ith_append_of_lt hilm]
else
  have hc : fin.cast (eq.symm (nat.add_assoc l m n)) ⟨i,hi⟩ = ⟨i, eq.substr (nat.add_assoc l m n) hi⟩,
  from fin.eq_of_veq $ by simp,
  have hilm : i - l ≥ m, 
  from nat.le_sub_of_add_le_of_ge (le_of_not_gt hil) (le_of_not_gt him), 
  by simp [hc, ith_append_of_ge _ (le_of_not_gt hil), ith_append_of_ge _ (le_of_not_gt him), ith_append_of_ge _ hilm, nat.sub_sub]

@[reducible] 
definition take {{m n : ℕ}} : n ≤ m → α ^ m → α ^ n
| h xs i := xs[fin.lift h i]

@[simp]
lemma take_val {m n : ℕ} (h : m ≤ n) {xs : α ^ n} :
∀ (i : fin m), (take h xs)[i] = xs[fin.lift h i] := 
λ _, rfl

@[simp]
lemma take_take {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} {xs : α ^ n} :
take hlm (take hmn xs) = take (le_trans hlm hmn) xs :=
tup.ext $ λ i, by simp

@[simp]
lemma take_append {m n : ℕ} {xs : α ^ m} {ys : α ^ n} :
take (nat.le_add_right m n) (xs ⊔ ys) = xs :=
tup.ext $ λ ⟨i,hi⟩, by simp [ith_append_of_lt hi]

@[reducible]
definition drop {{m n : ℕ}} : m ≤ n → α ^ n → α ^ m
| h xs i := xs[fin.push h i]

@[simp]
lemma drop_val {m n : ℕ} (h : m ≤ n) {xs : α ^ n} :
∀ (i : fin m), (drop h xs)[i] = xs[fin.push h i] := 
λ _, rfl

@[simp]
lemma drop_drop {l m n : ℕ} {hlm : l ≤ m} {hmn : m ≤ n} {xs : α ^ n} :
drop hlm (drop hmn xs) = drop (le_trans hlm hmn) xs :=
tup.ext $ λ i, by simp

@[simp]
lemma drop_append {m n : ℕ} {xs : α ^ m} {ys : α ^ n} :
drop (nat.le_add_left n m) (xs ⊔ ys) = ys :=
tup.ext $ λ ⟨i,hi⟩,
have hlt : ((m + n) - n) + i < m + n,
from calc
((m + n) - n) + i 
    = m + i : by rw nat.add_sub_cancel
... < m + n : nat.add_lt_add_left hi m,
have hge : ((m + n) - n) + i ≥ m, 
from calc
((m + n) - n) + i 
    = m + i : by rw nat.add_sub_cancel
... ≥ m : nat.le_add_right m i,
have heq : (i + ((m + n) - n)) - m = i,
from calc
(i + ((m + n) - n)) - m 
    = (i + m) - m : by rw nat.add_sub_cancel
... = i : by rw nat.add_sub_cancel,
by simp [heq, ith_append_of_ge hlt hge]

@[simp]
lemma append_take_drop {m n : ℕ} {xs : α ^ (m + n)} :
(take (nat.le_add_right m n) xs) ⊔ (drop (nat.le_add_left n m) xs) = xs :=
tup.ext $ λ ⟨i, hi⟩,
if h : i < m then
  by simp [ith_append_of_lt h]
else
  have i - m + (m + n - n) = i,
  from calc
  (i - m) + (m + n - n)
      = (i - m) + m : by rw nat.add_sub_cancel
  ... = i : by rw nat.sub_add_cancel (le_of_not_gt h),
  by simp [ith_append_of_ge hi (le_of_not_gt h), fin.push, this]

end tup

namespace ntup
variable {α : Type*}

@[reducible]
definition append : ntup α → ntup α → ntup α
| ⟨n, xs⟩ ⟨m, ys⟩ := ⟨n + m, xs ⊔ ys⟩ 

instance : has_emptyc (ntup α) := ⟨ntup.nil⟩
instance : has_append (ntup α) := ⟨append⟩

@[simp]
lemma append_length : ∀ (nxs nys : ntup α), (nxs ++ nys).length = nxs.length + nys.length
| ⟨nx,xs⟩ ⟨ny,ys⟩ := rfl

@[simp]
lemma append_to_tup : ∀ (nxs nys : ntup α), 
tup.cast (append_length nxs nys) (nxs ++ nys).to_tup = nxs.to_tup ⊔ nys.to_tup
| ⟨nx,xs⟩ ⟨ny,ys⟩ := rfl

@[simp]
lemma append_nil :
∀ (nxs : ntup α), nxs ++ nil = nxs
| ⟨nx,xs⟩ := 
  have tup.cast rfl (xs ⊔ tup.nil) = xs,
  by simp [tup.append_nil xs],
  ntup.eq rfl this

@[simp]
lemma nil_append :
∀ (nxs : ntup α), nil ++ nxs = nxs
| ⟨nx,xs⟩ :=
  ntup.eq (zero_add nx) (tup.nil_append xs)

@[simp]
lemma append_assoc : 
∀ (nxs nys nzs : ntup α), (nxs ++ nys) ++ nzs = nxs ++ (nys ++ nzs)
| ⟨nx,xs⟩ ⟨ny,ys⟩ ⟨nz,zs⟩ :=
  ntup.eq (add_assoc nx ny nz) (tup.append_assoc xs ys zs)

end ntup