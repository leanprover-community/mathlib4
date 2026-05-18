/-
Copyright (c) 2026 Aleksander Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksander Kiezun
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# Binomial coefficients and consecutive products

This file contains results relating divisibility of binomial coefficients to divisibility of
consecutive products.
-/

public section

namespace Nat

namespace Prime

variable {p k n : ℕ}

lemma dvd_choose_add_sub_one_iff (hp : Prime p) (hpn : n < p) :
    p ∣ choose (k + n - 1) n ↔ ∃ i < n, p ∣ k + i := by
  rw [← hp.dvd_ascFactorial_iff, Nat.ascFactorial_eq_factorial_mul_choose']
  exact ⟨fun h => dvd_mul_of_dvd_right h (n !),
    fun h => (hp.coprime_factorial_of_lt hpn).dvd_of_dvd_mul_left h⟩

end Prime

end Nat
