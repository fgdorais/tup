/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import fin.decidable
import .basic

namespace tup
variables {α : Type*} [da : decidable_eq α]
include da

lemma ext_iff_eq {n : ℕ} (xs ys : α ^ n) :
(∀ i, xs[i] = ys[i]) ↔ xs = ys :=
iff.intro tup.ext (λ h i, eq.rec_on h rfl)

instance decidable_eq {n : ℕ} : decidable_eq (α ^ n) := 
λ xs ys, decidable_of_decidable_of_iff (fin.forall_decidable (λ i, xs[i] = ys[i])) (ext_iff_eq xs ys)

end tup