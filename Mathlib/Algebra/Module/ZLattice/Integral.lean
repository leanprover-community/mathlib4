/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Integral lattices

A `ℤ`-submodule `L` of a real inner product space is *integral* if `⟪x, y⟫` is an integer for all
`x, y ∈ L`. Even lattices are integral, see `Mathlib/Algebra/Module/ZLattice/Even.lean`.

## Main definitions

* `ZLattice.IsIntegral L`: the predicate that `⟪x, y⟫` is an integer for all `x, y ∈ L`.

## Main results

* `ZLattice.IsIntegral.one_le_norm`: every nonzero vector of an integral lattice has norm at least
  `1`.
* `ZLattice.IsIntegral.discreteTopology`: an integral lattice is discrete.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

/-- A `ℤ`-submodule `L` of a real inner product space is *integral* if `⟪x, y⟫` is an integer for
all `x, y ∈ L`. -/
def IsIntegral (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, ⟪x, y⟫_ℝ = n

namespace IsIntegral

/-- Every nonzero vector of an integral lattice has norm at least `1`. -/
lemma one_le_norm (hL : IsIntegral L) {x : E} (hx : x ∈ L) (hx₀ : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨n, hn⟩ := hL x hx x hx
  rw [real_inner_self_eq_norm_sq] at hn
  rw [← one_le_sq_iff₀ (norm_nonneg x), hn]
  exact_mod_cast Int.cast_pos.1 (hn ▸ pow_pos (norm_pos_iff.2 hx₀) 2 : (0 : ℝ) < n)

/-- An integral lattice is discrete. -/
lemma discreteTopology (hL : IsIntegral L) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, one_pos, fun y hy ↦ by_contra fun hy₀ ↦ ?_⟩
  exact (hL.one_le_norm y.property (by simpa using hy₀)).not_gt (by simpa using hy)

end IsIntegral

end ZLattice
