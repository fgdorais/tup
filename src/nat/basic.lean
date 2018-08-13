/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace nat
variables {m n : ℕ}

abbreviation add_sub_cancel_right := nat.add_sub_cancel

lemma sub_add_of_le {m n : ℕ} : m ≤ n → (n - m) + m = n :=
assume h : m ≤ n, by rw [add_comm, add_sub_of_le h]

lemma sub_lt_of_lt_add_of_ge {m n i : ℕ} : i ≥ m → i < m + n → i - m < n :=
assume (hm : m ≤ i) (h : i < m + n),
lt_of_add_lt_add_left $
show m + (i - m) < m + n, 
from calc m + (i - m) = i : add_sub_of_le hm
              ... < m + n : h

lemma le_sub_of_add_le_of_ge {m n i : ℕ} :
n ≤ i → n + m ≤ i → m ≤ i - n :=
assume hn h, 
le_of_add_le_add_left $
show n + m ≤ n + (i - n),
from calc n + m ≤ i : h
  ... = n + (i - n) : eq.symm $ add_sub_of_le hn

inductive nonzero (n : ℕ) : Prop 
| ne_zero : n ≠ 0 → nonzero
| zero_ne : 0 ≠ n → nonzero

lemma ne_zero_of_nonzero : nonzero n → n ≠ 0
| (nonzero.ne_zero h) := h
| (nonzero.zero_ne h) := ne.symm h

lemma zero_ne_of_nonzero : nonzero n → 0 ≠ n
| (nonzero.ne_zero h) := ne.symm h
| (nonzero.zero_ne h) := h

lemma zero_lt_of_zero_ne : 0 ≠ n → 0 < n := lt_of_le_of_ne (zero_le n)
lemma zero_lt_of_ne_zero : n ≠ 0 → 0 < n := λ h, zero_lt_of_zero_ne (ne.symm h)

lemma zero_ne_of_zero_ne_mul_left : 0 ≠ m * n → 0 ≠ m :=
mt $ λ h, eq.rec_on h (eq.symm $ zero_mul n)
lemma ne_zero_of_mul_ne_zero_left : m * n ≠ 0 → m ≠ 0 :=
mt $ λ h, eq.rec_on (eq.symm h) (zero_mul n)
lemma zero_lt_of_zero_lt_mul_left : 0 < m * n → 0 < m :=
λ h, zero_lt_of_zero_ne (zero_ne_of_zero_ne_mul_left (ne_of_lt h))

lemma zero_ne_of_zero_ne_mul_right : 0 ≠ m * n → 0 ≠ n :=
mt $ λ h, eq.rec_on h (eq.symm $ mul_zero m)
lemma ne_zero_of_mul_ne_zero_right : m * n ≠ 0 → n ≠ 0 :=
mt $ λ h, eq.rec_on (eq.symm h) (mul_zero m)
lemma zero_lt_of_zero_lt_mul_right : 0 < m * n → 0 < n :=
λ h, zero_lt_of_zero_ne (zero_ne_of_zero_ne_mul_right (ne_of_lt h))

lemma div_alg {q r : ℕ} : r < m → (n = r + m * q ↔ q = n / m ∧ r = n % m) :=
begin
intro hr,
have hm : 0 < m, from lt_of_le_of_lt (zero_le r) hr,
split,
{ intro hn,
  split,
  rw [hn, nat.add_mul_div_left _ _ hm, nat.div_eq_of_lt hr, zero_add],
  rw [hn, nat.add_mul_mod_self_left, nat.mod_eq_of_lt hr],
},
{ intro h, destruct h, intros hq hr,
  rw [hq, hr, nat.mod_add_div], 
},
end

end nat