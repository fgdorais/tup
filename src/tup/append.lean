/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons .conj

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

definition fun_append (f : α → Sort*) {xs : α ^ m} {ys : α ^ n} :
(Π i, f xs[i]) → (Π i, f ys[i]) → (Π i, f (xs ⊔ ys)[i]) :=
λ fx fy ⟨i, hi⟩,
if him : i < m then
  by simp [ith_append_of_lt him]; apply fx
else
  have him : i ≥ m, from le_of_not_gt him,
  by simp [ith_append_of_ge hi him]; apply fy

lemma prop_append (p : α → Prop) {xs : α ^ m} {ys : α ^ n} :
(∀ i, p xs[i]) → (∀ i, p ys[i]) → (∀ i, p (xs ⊔ ys)[i]) := fun_append p

lemma append_nil (xs : α ^ n) : xs ⊔ nil = xs :=
ext $ λ ⟨i,hi⟩, ith_append_of_lt hi

lemma append_conj (xs : α ^ m) (ys : α ^ n) (y : α) :
xs ⊔ (conj ys y) = tup.cast (add_assoc m n 1) (conj (xs ⊔ ys) y) :=
ext $ λ ⟨i,hi⟩,
have hi' : i < m + n + 1, by rw [add_assoc]; exact hi,
if him : i < m then
  have i < m + n, from nat.lt_add_right i m n him,
  by simp 
  [ ith_append_of_lt him
  , ith_conj_of_lt this
  ]
else if himn : i < m + n then
  have him : i ≥ m, from le_of_not_gt him,
  have i - m < n, from nat.sub_lt_of_lt_add_of_ge him himn,
  by simp
  [ ith_append_of_ge hi him
  , ith_conj_of_lt this
  , ith_conj_of_lt himn
  , ith_append_of_ge himn him
  ]
else
  have him : i ≥ m, from le_of_not_gt him,
  have himn : i ≥ m + n, from le_of_not_gt himn,
  have i - m ≥ n, from nat.le_sub_of_add_le_of_ge him himn,
  by simp
  [ ith_conj_of_ge _ himn
  , ith_append_of_ge _ him
  , ith_conj_of_ge _ this
  ]

lemma nil_append' (xs : α ^ n) : tup.cast (nat.zero_add n) (nil ⊔ xs) = xs :=
have ∀ (i : fin n), fin.cast (ge_of_eq (nat.zero_add n)) i = fin.push_by 0 i, 
from λ ⟨_,_⟩, by simp [fin.push_by],
ext $ λ ⟨i,hi⟩, by simp [ith_append_of_ge _ (nat.zero_le i)]

lemma nil_append (xs : α ^ n) : nil ⊔ xs = tup.cast (eq.symm $ nat.zero_add n) xs :=
eq_cast_symm_of_cast_eq $ nil_append' xs

lemma cons_append' (x : α) (xs : α ^ m) (ys : α ^ n) :
tup.cast (add_right_comm m 1 n) ((x :: xs) ⊔ ys) = (x :: (xs ⊔ ys)) := 
ext $ λ i, 
match i with
| ⟨0,_⟩ := by simp [ith_append_of_lt (nat.zero_lt_succ m)]
| ⟨i+1,hi⟩ := 
  if him : i < m then
    by simp 
    [ ith_append_of_lt (nat.succ_lt_succ him)
    , ith_append_of_lt him
    ]
  else
    have hi' : i + 1 < m + 1 + n, by rw ← add_right_comm m n 1; exact hi,
    have him : i ≥ m, from le_of_not_gt him,
    by simp
    [ ith_append_of_ge (nat.lt_of_succ_lt_succ hi) him
    , ith_append_of_ge hi' (nat.succ_le_succ him)
    ]
end

lemma cons_append (x : α) (xs : α ^ m) (ys : α ^ n) :
(x :: xs) ⊔ ys = tup.cast (add_right_comm m n 1) (x :: (xs ⊔ ys)) := 
eq_cast_symm_of_cast_eq $ cons_append' x xs ys

lemma append_assoc (xs : α ^ l) (ys : α ^ m) (zs : α ^ n) :
cast (nat.add_assoc l m n) ((xs ⊔ ys) ⊔ zs) = xs ⊔ (ys ⊔ zs) :=
ext $ λ ⟨i, hi⟩,
if hil : i < l then
  have hilm : i < l + m, from nat.lt_add_right i l m hil,
  by simp
  [ ith_append_of_lt hil
  , ith_append_of_lt hilm
  ]
else if hilm : i < l + m then
  have hil : i ≥ l, from le_of_not_gt hil,
  have i - l < m, from nat.sub_lt_of_lt_add_of_ge hil hilm,
  by simp
  [ ith_append_of_lt hilm
  , ith_append_of_ge _ hil
  , ith_append_of_lt this
  ]
else 
  have hil : i ≥ l, from le_of_not_gt hil,
  have hilm : i ≥ l + m, from le_of_not_gt hilm,
  have i - l ≥ m, from nat.le_sub_of_add_le_of_ge hil hilm,
  by simp
  [ ith_append_of_ge _ hil
  , ith_append_of_ge _ this
  , ith_append_of_ge _ hilm
  , nat.sub_sub
  ]

@[reducible] 
definition take {{m n : ℕ}} : n ≤ m → α ^ m → α ^ n
| h xs i := xs[fin.cast h i]

@[simp]
lemma take_val {m n : ℕ} (h : m ≤ n) {xs : α ^ n} :
∀ (i : fin m), (take h xs)[i] = xs[fin.cast h i] := 
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
have heq : (((m + n) - n) + i) - m = i,
from calc
(((m + n) - n) + i) - m 
    = (m + i) - m : by rw nat.add_sub_cancel
... = i : by rw nat.add_sub_cancel_left,
begin
rw [drop_val, fin.push_mk, ith_append_of_ge hlt hge],
apply ith_eq_of_veq, 
exact heq
end

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
(nxs ++ nys).to_tup = tup.cast (eq.symm $ append_length nxs nys) (nxs.to_tup ⊔ nys.to_tup)
| ⟨nx,xs⟩ ⟨ny,ys⟩ := by simp [sigma.snd] 

@[simp]
lemma append_nil :
∀ (nxs : ntup α), nxs ++ nil = nxs
| ⟨nx,xs⟩ := by apply eq; simp; exact tup.append_nil xs

@[simp]
lemma nil_append :
∀ (nxs : ntup α), nil ++ nxs = nxs
| ⟨nx,xs⟩ := by apply eq; simp; exact tup.nil_append' xs

@[simp]
lemma append_assoc : 
∀ (nxs nys nzs : ntup α), (nxs ++ nys) ++ nzs = nxs ++ (nys ++ nzs)
| ⟨nx,xs⟩ ⟨ny,ys⟩ ⟨nz,zs⟩ := by apply eq; simp; exact tup.append_assoc xs ys zs

end ntup