/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol

! This file was ported from Lean 3 source module number_theory.wilson
! leanprover-community/mathlib commit e985d48324225202b17a7f9eb50b29ba09b77b44
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Move `wilsons_lemma` into this file, and give it a descriptive name.
-/


open scoped Nat

namespace Nat

variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
theorem prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n ≠ 1) : Prime n := by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h 
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  refine' hm2.ne' (nat.dvd_one.mp ((Nat.dvd_add_right hm).mp (hm1.trans _)))
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd, cast_add, cast_one, h, add_left_neg]
#align nat.prime_of_fac_equiv_neg_one Nat.prime_of_fac_equiv_neg_one

/-- **Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. -/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Prime n ↔ ((n - 1)! : ZMod n) = -1 := by
  refine' ⟨fun h1 => _, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  haveI := Fact.mk h1
  exact ZMod.wilsons_lemma n
#align nat.prime_iff_fac_equiv_neg_one Nat.prime_iff_fac_equiv_neg_one

end Nat

