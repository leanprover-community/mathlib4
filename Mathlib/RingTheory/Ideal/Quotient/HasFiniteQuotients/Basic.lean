/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Defs

/-! # Basic result for rings with finite quotients

This file provides the basic results for a ring with finite quotients.

## Main results
- `Ring.HasFiniteQuotients.instDimensionLEOne`: A ring with finite quotients has dimension `≤ 1`.
- `Ring.HasFiniteQuotients.instIsNoetherianRing`: A ring with finite quotients is noetherian.

-/

public section

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R] [HasFiniteQuotients R]

/-- A ring with finite quotients has dimension `≤ 1`. -/
instance : DimensionLEOne R where
  maximalOfPrime := fun h _ ↦ maximalOfPrime h

/-- A ring with finite quotients is noetherian. -/
instance : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I ↦ ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I := Ideal.span {x}) (by simp [hx₂])
    exact Submodule.FG.of_finite
  · rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hx₁)]
    exact Submodule.fg_span_singleton x

end Ring.HasFiniteQuotients
