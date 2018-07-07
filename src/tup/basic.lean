/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .extra

definition tup (α : Type*) (n : ℕ) := fin n → α

instance type_has_pow : has_pow Type* ℕ := {pow := tup}

namespace tup
variable {α : Type*}

@[inline] private
definition ith {n : ℕ} (xs : α ^ n) (i : fin n) : α := xs i

notation xs `[`:max_plus i `]`:0 := ith xs i

lemma ext {n : ℕ} {xs ys : α ^ n} : 
(∀ i, xs[i] = ys[i]) → xs = ys := funext

@[reducible] 
definition const {n : ℕ} (x : α) : α ^ n := λ _, x

section cons
variable {n : ℕ}

definition nil : α ^ 0 := fin.elim0

definition cons : α → α ^ n → α ^ (n + 1)
| x _ ⟨0, _⟩ := x
| _ xs ⟨i+1, h⟩ := xs[⟨i, nat.lt_of_succ_lt_succ h⟩]

notation x :: xs := cons x xs
notation `⟪` l:(foldr `, ` (h t, tup.cons h t) tup.nil `⟫`) := l

@[simp] 
lemma cons_zero {x : α} {xs : α ^ n} : 
(x :: xs)[0] = x := rfl

@[simp] 
lemma cons_succ {x : α} {xs : α ^ n} : 
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

@[simp] 
lemma eq_nil (xs : α ^ 0) : xs = nil :=
funext (λ i, fin.elim0 i)

end cons

section choice

lemma choice : ∀ {n : ℕ} {p : fin n → α → Prop}, 
(∀ i, ∃ x : α, p i x) → (∃ xs : α ^ n, ∀ i : fin n, p i xs[i])
| 0 _ _ := ⟨nil, (λ i, fin.elim0 i)⟩
| (n+1) p h :=
  let p' := λ (i : fin n) (x : α), p (fin.succ i) x in
  have (∃ xs : α ^ n, ∀ i : fin n, p' i xs[i]),
  from choice (λ i, h (fin.succ i)),
  exists.elim this (λ xs hxs, exists.elim (h 0) (λ x hx, 
    exists.intro (x :: xs) (λ i, match i with
    | ⟨0, _⟩ := hx
    | ⟨i+1, h⟩ := hxs ⟨i, nat.lt_of_succ_lt_succ h⟩
    end)))

end choice

section map
variables {β : Type*} {γ : Type*} {n : ℕ}

@[reducible] 
definition map : (α → β) → α ^ n → β ^ n := 
λ f xs i, f xs[i]

@[reducible] 
definition map₂ : (α → β → γ) → α ^ n → β ^ n → γ ^n :=
λ f xs ys i, f xs[i] ys[i]

@[simp] 
lemma map_nil (f : α → β) : map f nil = nil := eq_nil _

lemma map_cons (f : α → β) (x : α) (xs : α ^ n) : 
map f (x :: xs) = f x :: map f xs := 
ext (λ i, match i with
| ⟨0, _⟩ := rfl
| ⟨i+1, _⟩ := rfl
end)

lemma map_head (f : α → β) (xs : α ^ (n+1)) :
head (map f xs) = f (head xs) := 
calc
head (map f xs) 
    = head (map f (head xs :: tail xs))     : by rw cons_head_tail
... = head (f (head xs) :: map f (tail xs)) : by rw map_cons
... = f (head xs)                           : by rw head_cons

lemma map_tail (f : α → β) (xs : α ^ (n+1)) :
tail (map f xs) = map f (tail xs) := 
calc
tail (map f xs) 
    = tail (map f (head xs :: tail xs))     : by rw cons_head_tail
... = tail (f (head xs) :: map f (tail xs)) : by rw map_cons
... = map f (tail xs)                       : by rw tail_cons

@[simp]
lemma map_map (g : β → γ) (f : α → β) {n : ℕ} (xs : α ^ n) :
map g (map f xs) = map (g ∘ f) xs := rfl

@[simp] 
lemma map₂_nil (f : α → β → γ) : map₂ f nil nil = nil := eq_nil _

lemma map₂_cons (f : α → β → γ) (x : α) (xs : α ^ n) (y : β) (ys : β ^ n) : 
map₂ f (x :: xs) (y :: ys) = f x y :: map₂ f xs ys := 
ext (λ i, match i with
| ⟨0, _⟩ := rfl
| ⟨i+1, _⟩ := rfl
end)

lemma map₂_head (f : α → β → γ) (xs : α ^ (n+1)) (ys : β ^ (n+1)) :
head (map₂ f xs ys) = f (head xs) (head ys) := 
calc
head (map₂ f xs ys) 
    = head (map₂ f (head xs :: tail xs) (head ys :: tail ys))    : by rw [cons_head_tail, cons_head_tail]
... = head (f (head xs) (head ys) :: map₂ f (tail xs) (tail ys)) : by rw map₂_cons
... = f (head xs) (head ys)                                      : by rw head_cons

lemma map₂_tail (f : α → β → γ) (xs : α ^ (n+1)) (ys : β ^ (n+1)) :
tail (map₂ f xs ys) = map₂ f (tail xs) (tail ys) := 
calc
tail (map₂ f xs ys) 
    = tail (map₂ f (head xs :: tail xs) (head ys :: tail ys))    : by rw [cons_head_tail, cons_head_tail]
... = tail (f (head xs) (head ys) :: map₂ f (tail xs) (tail ys)) : by rw map₂_cons
... = map₂ f (tail xs) (tail ys)                                 : by rw tail_cons

end map

section append
variables {m n : ℕ}

definition append : α ^ m → α ^ n → α ^ (m + n)
| xs ys ⟨i, h⟩ := 
  if hm : i < m then
    xs ⟨i, hm⟩
  else
    ys ⟨i - m, nat.sub_lt_of_lt_add_of_ge (le_of_not_gt hm) h⟩

infix ++ := append

lemma ith_append_of_lt {xs : α ^ m} {ys : α ^ n} {i : ℕ} (h : i < m) : 
(xs ++ ys)[⟨i, nat.lt_add_right i m n h⟩] = xs[⟨i,h⟩] := dif_pos h

lemma ith_append_of_ge {xs : α ^ m} {ys : α ^ n} {i : ℕ} (h : i < m+n) (hm : i ≥ m) :
(xs ++ ys)[⟨i, h⟩] = ys[⟨i-m, nat.sub_lt_of_lt_add_of_ge hm h⟩] := dif_neg (not_lt_of_ge hm)

lemma append_lift {xs : α ^ m} {ys : α ^ n} :
∀ i, (xs ++ ys)[fin.lift_by n i] = xs[i]
| ⟨i, h⟩ := ith_append_of_lt h

lemma append_push {xs : α ^ m} {ys : α ^ n} :
∀ i : fin n, (xs ++ ys)[fin.push_by m i] = ys[i]
| ⟨i, h⟩ := 
  calc
  (xs ++ ys)[⟨m+i, nat.add_lt_add_left h m⟩] 
      = ys[⟨(m+i)-m, _⟩] : ith_append_of_ge (nat.add_lt_add_left h m) (nat.le_add_right m i)
  ... = ys[⟨i, h⟩]       : by simp [nat.add_sub_cancel']

lemma append_nil (xs : α ^ n) : xs ++ nil = xs :=
ext (λ ⟨i,hi⟩, ith_append_of_lt hi)

@[reducible] 
definition take (n : ℕ) (xs : α ^ (n + m)) : α ^ n 
:= λ i, xs[fin.lift_by _ i]

lemma take_val {xs : α ^ (n+m)} :
∀ i : fin n, (take n xs)[i] = xs[fin.lift_by m i]
| ⟨i, hi⟩ := rfl

lemma take_append {xs : α ^ m} {ys : α ^ n} : take m (xs ++ ys) = xs :=
tup.ext (λ i, by unfold tup.take; apply append_lift)

@[reducible] 
definition take_of_le {{m n : ℕ}} : n ≤ m → α ^ m → α ^ n :=
assume h : n ≤ m, 
eq.rec_on (nat.add_sub_of_le h) (take n)

@[reducible] 
definition drop (n : ℕ) (xs : α ^ (n + m)) : α ^ m :=
λ i : fin m, xs[fin.push_by _ i]

lemma drop_val {xs : α ^ (m+n)} :
∀ i : fin n, (drop m xs)[i] = xs[fin.push_by m i]
| ⟨i, hi⟩ := rfl

lemma drop_append {xs : α ^ m} {ys : α ^ n} : drop m (xs ++ ys) = ys :=
tup.ext (λ i, by unfold tup.drop; apply append_push)

@[reducible]
definition drop_of_le {{m n : ℕ}} : m ≤ n → α ^ n → α ^ m :=
assume h : m ≤ n,
eq.rec_on (nat.sub_add_of_le h) (drop (n - m))

end append

end tup

section rec
universe u
variables {α : Type u} {C : Π {n : ℕ}, α ^ n → Sort*}
open tup

@[recursor 6] 
definition rec :
C nil → (Π (x : α) {n : ℕ} (xs : α ^ n), C xs → C (x :: xs)) → (Π {n : ℕ} (xs : tup.{u} α n), C xs) 
| h0 _ 0 xs := eq.rec_on (eq.symm (eq_nil xs)) h0
| h0 hs (n+1) xs := eq.rec_on (cons_head_tail xs) (hs (head xs) (tail xs) (rec h0 hs (tail xs)))

@[elab_as_eliminator] 
definition rec_on {n : ℕ} (xs : α ^ n) :
C nil → (Π (x : α) {n : ℕ} (xs : α ^ n), C xs → C (x :: xs)) → C xs :=
assume h0 hs, rec h0 hs xs

end rec
