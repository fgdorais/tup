/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons

namespace tup
variables {α : Type*} {β : Type*} {γ : Type*} {n : ℕ}

@[reducible] 
definition map : (α → β) → α ^ n → β ^ n := 
λ f xs i, f xs[i]

@[reducible] 
definition map₂ : (α → β → γ) → α ^ n → β ^ n → γ ^n :=
λ f xs ys i, f xs[i] ys[i]

@[simp] 
lemma map_nil (f : α → β) : map f nil = nil := eq_nil _

@[simp]
lemma map1 (f : α → β) (x : α) : map f ⟪x⟫ = ⟪f x⟫ := 
tup.ext $ λ i, match i with
| ⟨0,_⟩ := rfl
| ⟨k+1,hk⟩ := absurd (nat.le_add_left 1 k) (not_le_of_gt hk)
end

@[simp]
lemma map2 (f : α → β) (x y : α) : map f ⟪x, y⟫ = ⟪f x, f y⟫ := 
tup.ext $ λ i, match i with
| ⟨0,_⟩ := rfl
| ⟨1,_⟩ := rfl
| ⟨k+2,hk⟩ := absurd (nat.le_add_left 2 k) (not_le_of_gt hk)
end

@[simp]
lemma map3 (f : α → β) (x y z : α) : map f ⟪x, y, z⟫ = ⟪f x, f y, f z⟫ := 
tup.ext $ λ i, match i with
| ⟨0,_⟩ := rfl
| ⟨1,_⟩ := rfl
| ⟨2,_⟩ := rfl
| ⟨k+3,hk⟩ := absurd (nat.le_add_left 3 k) (not_le_of_gt hk)
end

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

end tup