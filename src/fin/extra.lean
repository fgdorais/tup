/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import nat

theorem ge_of_eq {α : Type*} [preorder α] {a b : α} : a = b → a ≥ b := λ h, le_of_eq (eq.symm h)

namespace option

lemma map_is_some {α : Type*} {β : Type*} (f : α → β) :
∀ x, is_some (option.map f x) = is_some x
| (some _) := rfl
| none := rfl

lemma map_is_none {α : Type*} {β : Type*} (f : α → β) :
∀ x, is_none (option.map f x) = is_none x
| (some _) := rfl
| none := rfl

end option



