/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.Real.NNReal
import Mathlib.RingTheory.Valuation.Basic

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `IsRankOne` : A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.

## Tags

valuation, rank one
-/

noncomputable section

open Function Multiplicative

open scoped NNReal

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`. -/
class IsRankOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom : Γ₀ →*₀ ℝ≥0
  strictMono' : StrictMono hom
  nontrivial' : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1

namespace IsRankOne

variable (v : Valuation R Γ₀) [IsRankOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := nontrivial'

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `is_rank_one.hom v`, then
  `x = 0`. -/
theorem zero_of_hom_zero {x : Γ₀} (hx : IsRankOne.hom v x = 0) : x = 0 := by
  have hx0 : 0 ≤ x := zero_le'
  cases' le_iff_lt_or_eq.mp hx0 with h_lt h_eq
  · have hs := IsRankOne.strictMono v h_lt
    rw [_root_.map_zero, hx] at hs
    exact absurd hs not_lt_zero'
  · exact h_eq.symm

/-- If `v` is a rank one valuation, then`x : Γ₀` has image `0` under `is_rank_one.hom v` if and
  only if `x = 0`. -/
theorem hom_eq_zero_iff {x : Γ₀} : IsRankOne.hom v x = 0 ↔ x = 0 :=
  ⟨fun h => zero_of_hom_zero v h, fun h => by rw [h, _root_.map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : valuation R Γ₀`. -/
def Unit : Γ₀ˣ :=
  Units.mk0 (v ((nontrivial v).choose )) ((nontrivial v).choose_spec).1

/-- A proof that `is_rank_one_unit v ≠ 1`. -/
theorem Unit_ne_one : Unit v ≠ 1 := by
  rw [Ne.def, ← Units.eq_iff, Units.val_one]
  exact ((nontrivial v).choose_spec ).2

end IsRankOne

end Valuation
