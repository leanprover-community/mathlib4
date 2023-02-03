/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.absolute_value
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Topology.UniformSpace.Basic

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/


open Set Function Filter UniformSpace

open Filter

namespace IsAbsoluteValue

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

variable {R : Type _} [CommRing R] (abv : R → 𝕜) [IsAbsoluteValue abv]

/-- The uniformity coming from an absolute value. -/
def uniformSpaceCore : UniformSpace.Core R
    where
  uniformity := ⨅ ε > 0, 𝓟 { p : R × R | abv (p.2 - p.1) < ε }
  refl :=
    le_infᵢ fun ε =>
      le_infᵢ fun ε_pos =>
        principal_mono.2 fun ⟨x, y⟩ h => by simpa [show x = y from h, abv_zero abv]
  symm :=
    tendsto_infᵢ.2 fun ε =>
      tendsto_infᵢ.2 fun h =>
        tendsto_infᵢ' ε <|
          tendsto_infᵢ' h <|
            tendsto_principal_principal.2 fun ⟨x, y⟩ h =>
              by
              have h : abv (y - x) < ε := by simpa [-sub_eq_add_neg] using h
              rwa [abv_sub abv] at h
  comp :=
    le_infᵢ fun ε =>
      le_infᵢ fun h =>
        lift'_le
            (mem_infᵢ_of_mem (ε / 2) <| mem_infᵢ_of_mem (div_pos h zero_lt_two) (Subset.refl _)) <|
          by
          have : ∀ a b c : R, abv (c - a) < ε / 2 → abv (b - c) < ε / 2 → abv (b - a) < ε :=
            fun a b c hac hcb =>
            calc
              abv (b - a) ≤ _ := abv_sub_le abv b c a
              _ = abv (c - a) + abv (b - c) := add_comm _ _
              _ < ε / 2 + ε / 2 := add_lt_add hac hcb
              _ = ε := by rw [div_add_div_same, add_self_div_two]
              
          simpa [compRel]
#align is_absolute_value.uniform_space_core IsAbsoluteValue.uniformSpaceCore

/-- The uniform structure coming from an absolute value. -/
def uniformSpace : UniformSpace R :=
  UniformSpace.ofCore (uniformSpaceCore abv)
#align is_absolute_value.uniform_space IsAbsoluteValue.uniformSpace

theorem mem_uniformity {s : Set (R × R)} :
    s ∈ (uniformSpaceCore abv).uniformity ↔ ∃ ε > 0, ∀ {a b : R}, abv (b - a) < ε → (a, b) ∈ s :=
  by
  suffices (s ∈ ⨅ ε : { ε : 𝕜 // ε > 0 }, 𝓟 { p : R × R | abv (p.2 - p.1) < ε.val }) ↔ _
    by
    rw [infᵢ_subtype] at this
    exact this
  rw [mem_infi_of_directed]
  · simp [subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    exact
      ⟨⟨min r p, lt_min hr hp⟩, by simp (config := { contextual := true }) [lt_min_iff, (· ≥ ·)]⟩
#align is_absolute_value.mem_uniformity IsAbsoluteValue.mem_uniformity

end IsAbsoluteValue

