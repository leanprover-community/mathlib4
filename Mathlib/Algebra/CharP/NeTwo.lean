/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.Algebra.CharP.Two

/-!
# Lemmas about rings of characteristic different from two
-/

namespace CharP

variable {R : Type*} [Ring R]

lemma orderOf_eq_two_iff [Nontrivial R] [NoZeroDivisors R] (p : ℕ)
    [p_ne_two : Fact (p ≠ 2)] [CharP R p] (x : R) : orderOf x = 2 ↔ x = -1 := by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h ↦ p_ne_two.out ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))


end CharP
