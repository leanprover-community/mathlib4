/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.IntegralLattice

/-!
# Even lattices

A `ℤ`-submodule `L` of a real inner product space is *even* if `⟪x, x⟫` is an even integer for
every `x ∈ L`. An even lattice is automatically integral. Examples include the root lattices `Dₙ`
and `E₈`.

## Main definitions

* `Submodule.IsEven L`: the predicate that `⟪x, x⟫` is an even integer for every `x ∈ L`.

## Main results

* `Submodule.IsEven.isIntegral`: an even lattice is integral.
* `Submodule.IsEven.sqrt_two_le_norm`: every nonzero vector of an even lattice has norm at least
  `√2`.
* `Submodule.IsEven.discreteTopology`: an even lattice is discrete.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

/-- A `ℤ`-submodule `L` of a real inner product space is *even* if `⟪x, x⟫` is an even integer
for every `x ∈ L`. An even lattice is integral, see `Submodule.IsEven.isIntegral`. -/
def IsEven (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∃ n : ℤ, ⟪x, x⟫_ℝ = 2 * n

lemma isEven_iff_norm_sq : IsEven L ↔ ∀ x ∈ L, ∃ n : ℤ, ‖x‖ ^ 2 = 2 * n := by
  simp [IsEven]

namespace IsEven

/-- An even lattice is integral. -/
lemma isIntegral (hL : IsEven L) : L.IsIntegral := fun x hx y hy ↦ by
  obtain ⟨a, ha⟩ := hL _ (L.add_mem hx hy)
  obtain ⟨b, hb⟩ := hL x hx
  obtain ⟨c, hc⟩ := hL y hy
  rw [real_inner_add_add_self, hb, hc] at ha
  exact ⟨a - b - c, by push_cast; linarith⟩

/-- Every nonzero vector of an even lattice has norm at least `√2`. -/
lemma sqrt_two_le_norm (hL : IsEven L) {x : E} (hx : x ∈ L) (hx₀ : x ≠ 0) : √2 ≤ ‖x‖ := by
  obtain ⟨n, hn⟩ := isEven_iff_norm_sq.1 hL x hx
  have : (0 : ℤ) < n := by exact_mod_cast (by nlinarith [norm_pos_iff.2 hx₀] : (0 : ℝ) < n)
  exact Real.sqrt_le_iff.2 ⟨norm_nonneg x, hn ▸ by exact_mod_cast (by lia : 2 ≤ 2 * n)⟩

/-- An even lattice is discrete. -/
lemma discreteTopology (hL : IsEven L) : DiscreteTopology L :=
  hL.isIntegral.discreteTopology

end IsEven

end Submodule
