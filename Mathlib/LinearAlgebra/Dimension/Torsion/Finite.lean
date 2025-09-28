/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Results relating rank and torsion.

-/

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

lemma rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  rw [Module.IsTorsion, rank_eq_zero_iff]
  simp [mem_nonZeroDivisors_iff_ne_zero]

/-- The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`. -/
theorem Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  rw [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
  norm_cast
