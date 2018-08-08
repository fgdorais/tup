/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

namespace fin

lemma forall_iff_zero_and_succ {n} (p : fin (n+1) → Prop) :
p 0 ∧ (∀ i, p (fin.succ i)) ↔ (∀ i, p i) :=
iff.intro 
  (λ ⟨ho,hs⟩ i, 
  match i with
  | ⟨0,_⟩ := ho
  | ⟨i+1,hi⟩ := hs ⟨i, nat.lt_of_succ_lt_succ hi⟩ 
  end)
  (λ h, ⟨h 0, λ i, h (fin.succ i)⟩)

lemma forall_iff_lift_and_last {n} (p : fin (n+1) → Prop) :
(∀ i, p (fin.lift i)) ∧ p (fin.last n) ↔ (∀ i, p i) :=
iff.intro 
  (λ ⟨hl,h⟩ i,
  if hi : i = fin.last n then
  eq.substr hi h
  else
  have fin.lift (fin.drop i hi) = i, from lift_drop _ _,
  eq.subst this $ hl (fin.drop i hi))
  (λ h, ⟨λ i, h (fin.lift i), h (fin.last n)⟩)

lemma exists_iff_zero_or_succ {n} (p : fin (n+1) → Prop) :
p 0 ∨ (∃ i, p (fin.succ i)) ↔ (∃ i, p i) :=
iff.intro
  (λ h, or.elim h (λ ho, ⟨0, ho⟩) (λ ⟨i,hi⟩, ⟨fin.succ i, hi⟩))
  (λ ⟨i,hi⟩, 
  match i,hi with
  | ⟨0,_⟩,ho := or.inl ho
  | ⟨i+1,hi⟩,hs := or.inr (exists.intro ⟨i, nat.lt_of_succ_lt_succ hi⟩ hs)
  end)

lemma exists_iff_lift_or_last {n} (p : fin (n+1) → Prop) :
(∃ i, p (fin.lift i)) ∨ p (fin.last n) ↔ (∃ i, p i) :=
iff.intro
  (λ h, or.elim h (λ ⟨i,h⟩, ⟨fin.lift i, h⟩) (λ h, ⟨fin.last n, h⟩))
  (λ ⟨i,h⟩,
  if hi : i = fin.last n then
  or.inr (eq.subst hi h)
  else
  or.inl
    (have p (fin.lift (fin.drop i hi)), 
    from eq.substr (lift_drop i hi) h,
    ⟨fin.drop i hi, this⟩))

instance forall_decidable :
Π {n : ℕ} (p : fin n → Prop) [decidable_pred p], decidable (∀ i, p i)
| 0 p _ := decidable.is_true (λ (i : fin 0), fin.elim0 i)
| (n+1) p dp := 
  have d0: decidable (p (fin.zero n)), from dp (fin.zero n),
  have ds: decidable (∀ i, p (fin.succ i)),
  from @forall_decidable n (λ i, p (fin.succ i)) (λ i, dp (fin.succ i)),
  decidable_of_decidable_of_iff (@and.decidable _ _ d0 ds) (forall_iff_zero_and_succ p)

instance exists_decidable :
Π {n : ℕ} (p : fin n → Prop) [decidable_pred p], decidable (∃ i, p i)
| 0 p _ := decidable.is_false (λ ⟨i,_⟩, fin.elim0 i)
| (n+1) p dp := 
  have d0: decidable (p (fin.zero n)), from dp (fin.zero n),
  have ds: decidable (∃ i, p (fin.succ i)),
  from @exists_decidable n (λ i, p (fin.succ i)) (λ i, dp (fin.succ i)),
  decidable_of_decidable_of_iff (@or.decidable _ _ d0 ds) (exists_iff_zero_or_succ p)

end fin