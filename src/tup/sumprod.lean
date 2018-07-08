/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .cons

namespace tup
variable {α : Type*}

section sum
variables [hzero : has_zero α] [hadd : has_add α]
include hzero hadd

@[reducible]
definition sum : Π {n : ℕ}, α ^ n → α
| 0 _ := 0
| (n+1) xs := xs.head + sum xs.tail

@[simp]
lemma sum_nil : sum nil = 0 := rfl

@[simp]
lemma sum_cons {x : α} {n : ℕ} {xs : α ^ n} : 
sum (x :: xs) = x + sum xs := by simp [sum]

end sum

section prod
variables [hone : has_one α] [hmul : has_mul α]
include hone hmul

@[reducible]
definition prod : Π {n : ℕ}, α ^ n → α
| 0 _ := 1
| (n+1) xs := xs.head * prod xs.tail

@[simp]
lemma prod_nil : prod nil = 1 := rfl

@[simp]
lemma prod_cons {x : α} {n : ℕ} {xs : α ^ n} : 
prod (x :: xs) = x * prod xs := by simp [prod]

end prod

end tup