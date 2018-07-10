/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons .conj .append

namespace tup
variable {α : Type*}

section folds
variable {β : Sort*} 

definition foldr (y : β) (f : α → β → β) : Π {n : ℕ}, α ^ n → β
| 0 _ := y
| (n+1) xs := f xs.head (foldr xs.tail)

lemma foldr_nil {y : β} {f : α → β → β} : 
foldr y f nil = y := rfl

lemma foldr_cons {y : β} {f : α → β → β} {n : ℕ} {xs : α ^ n} {x : α} : 
foldr y f (x :: xs) = f x (foldr y f xs) := 
by simp [foldr]

definition foldl (y : β) (f : β → α → β) : Π {n : ℕ}, α ^ n → β
| 0 _ := y
| (n+1) xs := f (foldl xs.left) xs.last 

lemma foldl_nil {y : β} {f : β → α → β} : 
foldl y f nil = y := rfl

lemma foldl_conj {y : β} {f : β → α → β} {n : ℕ} {xs : α ^ n} {x : α} : 
foldl y f (xs && x) = f (foldl y f xs) x := 
by simp [foldl]

end folds

section sum
variables [hzero : has_zero α] [hadd : has_add α]
include hzero hadd

@[reducible]
definition sum {n : ℕ} : α ^ n → α := foldl (0:α) (+)

@[simp]
lemma sum_nil : sum (@nil α) = 0 := foldl_nil

@[simp]
lemma sum_conj {n : ℕ} {xs : α ^ n} {x : α} : 
sum (xs && x) = sum xs + x := foldl_conj

@[reducible]
definition sum' {n : ℕ} : α ^ n → α := foldr (0:α) (+)

@[simp]
lemma sum'_nil : sum' (@nil α) = 0 := foldr_nil

@[simp]
lemma sum'_cons {x : α} {n : ℕ} {xs : α ^ n} : 
sum' (x :: xs) = x + sum' xs := foldr_cons

end sum

section prod
variables [hone : has_one α] [hmul : has_mul α]
include hone hmul

@[reducible]
definition prod {n : ℕ} : α ^ n → α := foldl (1:α) (*)

@[simp]
lemma prod_nil : prod nil = 1 := foldl_nil

@[simp]
lemma prod_conj {x : α} {n : ℕ} {xs : α ^ n} : 
prod (xs && x) = prod xs * x := foldl_conj

@[reducible]
definition prod' {n : ℕ} : α ^ n → α := foldr (1:α) (*)

@[simp]
lemma prod'_nil : prod' nil = 1 := foldr_nil

@[simp]
lemma prod'_cons {x : α} {n : ℕ} {xs : α ^ n} : 
prod' (x :: xs) = x * prod' xs := foldr_cons

end prod

section join
variables [hnil : has_emptyc α] [happ : has_append α]
include hnil happ

@[reducible]
definition join {n : ℕ} : α ^ n → α := 
foldr hnil.emptyc has_append.append

@[simp]
lemma join_nil : join nil = hnil.emptyc := foldr_nil

@[simp]
lemma join_cons {x : α} {n : ℕ} {xs : α ^ n} : 
join (x :: xs) = has_append.append x (join xs) := foldr_cons

@[reducible]
definition join' {n : ℕ} : α ^ n → α := 
foldl hnil.emptyc has_append.append

@[simp]
lemma join'_nil : join' nil = hnil.emptyc := foldl_nil

@[simp]
lemma join'_conj {n : ℕ} {xs : α ^ n} {x : α} : 
join' (xs && x) = has_append.append (join' xs) x := foldl_conj

end join

end tup