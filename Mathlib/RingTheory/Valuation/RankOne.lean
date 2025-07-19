/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Order.GroupWithZero.Range
import Mathlib.Data.NNReal.Defs
import Mathlib.RingTheory.Valuation.Basic

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation has rank one if it is nontrivial and its image (defined as
`MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`.
* `RankOne.restrict_RankOne` is the `RankOne` instance for the restriction of a valuation to its
image, as defined in

## Tags

valuation, rank one
-/

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
noncomputable section

open Function Multiplicative MonoidWithZeroHom

open scoped NNReal

variable {R : Type*} [Ring R]
namespace Valuation

/-- A valuation has rank one if it is nontrivial and its image (defined as
`MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`. -/
class RankOne (v : Valuation R Γ₀) extends Valuation.IsNontrivial v where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom (v) : valueGroup₀ v →*₀ ℝ≥0
  strictMono' : StrictMono hom
namespace RankOne

variable (v : Valuation R Γ₀) [RankOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := IsNontrivial.exists_val_nontrivial

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `RankOne.hom v`, then
  `x = 0`. -/
theorem zero_of_hom_zero {x : valueGroup₀ v} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero, hx] at hs
  exact hs.false

/-- If `v` is a rank one valuation, then`x : Γ₀` has image `0` under `RankOne.hom v` if and
  only if `x = 0`. -/
theorem hom_eq_zero_iff {x : valueGroup₀ v} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ₀`. -/
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

/-- A proof that `RankOne.unit v ≠ 1`. -/
theorem unit_ne_one : unit v ≠ 1 := by
  rw [Ne, ← Units.val_inj, Units.val_one]
  exact ((nontrivial v).choose_spec).2

instance [RankOne v] : IsNontrivial v where
  exists_val_nontrivial := RankOne.nontrivial v

section Restrict

instance restrict_Nontrivial [v.IsNontrivial] : (v.restrict).IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    use x
    constructor
    · simp [hx0]
    · rw [restrict_def]
      intro H
      rw [restrict₀_eq_one_iff] at H
      tauto

variable (K : Type*) [Field K] (v : Valuation K Γ₀) [RankOne v]

instance restrict_RankOne [RankOne v] : RankOne (v.restrict) where
  hom := (RankOne.hom v).comp <| MonoidWithZeroHom.restrict₀_valueGroup₀_MonoidWithZeroHom (f := v)
  strictMono' := by
    apply (strictMono v).comp
    sorry


end Restrict

end RankOne

end Valuation
