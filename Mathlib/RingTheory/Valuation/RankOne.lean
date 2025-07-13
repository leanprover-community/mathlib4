/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.Valuation.ValuativeRel

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation `v` has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class contains the data of the inclusion of the codomain of `v` into `ℝ≥0`.

## Tags

valuation, rank one
-/

noncomputable section

open Function Multiplicative

open scoped NNReal

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
class RankOne (v : Valuation R Γ₀) extends Valuation.IsNontrivial v where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom : Γ₀ →*₀ ℝ≥0
  strictMono' : StrictMono hom

namespace RankOne

variable (v : Valuation R Γ₀) [RankOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := IsNontrivial.exists_val_nontrivial

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `RankOne.hom v`, then
  `x = 0`. -/
theorem zero_of_hom_zero {x : Γ₀} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero, hx] at hs
  exact hs.false

/-- If `v` is a rank one valuation, then`x : Γ₀` has image `0` under `RankOne.hom v` if and
  only if `x = 0`. -/
theorem hom_eq_zero_iff {x : Γ₀} : RankOne.hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ₀`. -/
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

/-- A proof that `RankOne.unit v ≠ 1`. -/
theorem unit_ne_one : unit v ≠ 1 := by
  rw [Ne, ← Units.val_inj, Units.val_one]
  exact ((nontrivial v).choose_spec ).2

instance [RankOne v] : IsNontrivial v where
  exists_val_nontrivial := RankOne.nontrivial v

end RankOne

end Valuation

section ValuativeRel

open ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

/-- A valuative relation has a rank one valuation when it is both nontrivial
and the rank is at most one. -/
def Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e : RankLeOneStruct R) :
    Valuation.RankOne (valuation R) where
  __ : Valuation.IsNontrivial (valuation R) := isNontrivial_iff_isNontrivial.mp inferInstance
  hom := e.emb
  strictMono' := e.strictMono

instance [IsNontrivial R] [IsRankLeOne R] :
    Valuation.RankOne (valuation R) :=
  Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

/-- Convert between the rank one statement on valuative relation's induced valuation. -/
def Valuation.RankOne.rankLeOneStruct (e : Valuation.RankOne (valuation R)) :
    RankLeOneStruct R where
  emb := e.hom
  strictMono := e.strictMono

lemma ValuativeRel.isRankLeOne_of_rankOne [h : (valuation R).RankOne] :
    IsRankLeOne R :=
  ⟨⟨h.rankLeOneStruct⟩⟩

lemma ValuativeRel.isNontrivial_of_rankOne [h : (valuation R).RankOne] :
    ValuativeRel.IsNontrivial R :=
  isNontrivial_iff_isNontrivial.mpr h.toIsNontrivial

end ValuativeRel
