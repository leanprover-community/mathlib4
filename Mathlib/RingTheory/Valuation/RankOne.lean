/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.NNReal.Defs
import Mathlib.RingTheory.Valuation.Basic

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions

* `RankLeOne` : A valuation `v` has rank at most one it its image is contained in `ℝ≥0`
  Note that this class contains the data of the inclusion of the codomain of `v` into `ℝ≥0`.

* `RankOne` : A valuation `v` has rank one if it is nontrivial and of rank at most one.

## Tags

valuation, rank one
-/

noncomputable section

open Function Multiplicative

open scoped NNReal

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank at most one if its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
class RankLeOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom : Γ₀ →*₀ ℝ≥0
  strictMono' : StrictMono hom

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
class RankOne (v : Valuation R Γ₀) extends RankLeOne v where
  nontrivial' : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1

namespace RankLeOne

variable (v : Valuation R Γ₀) [RankLeOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

-- TODO : add division?
/-- The canonical map from `v.rangeGroup₀` to `ℝ≥0` -/
def hom_rangeGroup₀ : v.rangeGroup₀ →*₀ ℝ≥0 where
  toFun := (hom v ·.val)
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp only [map_eq_zero]; rfl

theorem strictMono_rangeGroup₀ : StrictMono (hom_rangeGroup₀ v) := by
  intro x y h
  simpa only [Units.val_lt_val, Subtype.coe_lt_coe, h] using (strictMono v h)

/-- The canonical inclusion map from `v.rangeGroup₀` to `Γ₀` -/
def coe_rangeGroup₀ : v.rangeGroup₀ →*₀ Γ₀ where
  toFun := (·.val)
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by simp only [Submonoid.coe_mul]

/-- If `v` is a valuation of rank at most one,
and if `x : Γ₀` has image `0` under `RankLeOne.hom v`, then `x = 0`. -/
theorem zero_of_hom_zero {x : Γ₀} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero, hx] at hs
  exact hs.false

/-- If `v` is a valuation of rank at most one,
then `x : Γ₀` has image `0` under `RankLeOne.hom v` if and only if `x = 0`. -/
theorem hom_eq_zero_iff {x : Γ₀} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, _root_.map_zero]⟩

/-- If a valuation `v` has rank at most one, then so has restriction `v.rangeGroup₀_restrict` -/
instance : RankLeOne (v.rangeGroup₀_restrict) where
  hom := hom_rangeGroup₀ v
  strictMono' := strictMono_rangeGroup₀ v

end RankLeOne

namespace RankOne

variable (v : Valuation R Γ₀) [RankOne v]

lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := nontrivial'

/-- If a valuation `v` has rank one, then so has restriction `v.rangeGroup₀_restrict` -/
instance : RankOne (v.rangeGroup₀_restrict) where
  nontrivial' := by
    obtain ⟨x, hx⟩ := nontrivial v
    use x
    simp only [ne_eq, ← Subtype.coe_inj]
    exact hx

lemma exists_mem_ne_zero_and_lt_one :
    ∃ u ∈ v.rangeGroup₀, u ≠ 0 ∧ u < 1 := by
  obtain ⟨r, h0, h1⟩ := nontrivial v
  rcases (lt_or_gt_of_ne h1) with (h | h)
  · use v r, mem_rangeGroup₀ v, h0, h
  · refine ⟨(v r)⁻¹,
      MonoidHomWithZero.inv_mem_range₀ v.mem_rangeGroup₀,
      by simp [h0, inv_lt_one_of_one_lt₀ h]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ₀`. -/
def unit : Γ₀ˣ :=
  Units.mk0 (exists_mem_ne_zero_and_lt_one v).choose
    (exists_mem_ne_zero_and_lt_one v).choose_spec.2.1

/-- `RankOne.unit v < 1`. -/
theorem unit_lt_one : unit v < 1 :=
  (exists_mem_ne_zero_and_lt_one v).choose_spec.2.2

/-- `RankOne.unit v ≠ 1`. -/
theorem unit_ne_one : unit v ≠ 1 :=
  ne_of_lt (unit_lt_one v)
--   exact ((nontrivial v).choose_spec ).2

/-- `(RankOne.univ v : Γ₀) ∈ v.rangeGroup₀` -/
theorem coe_unit_mem_rangeGroup₀ : (unit v : Γ₀) ∈ v.rangeGroup₀ :=
  (exists_mem_ne_zero_and_lt_one v).choose_spec.1

/-- `(RankOne.univ v : Γ₀) ∈ v.rangeGroup₀ˣ` -/
theorem coe_unit_mem_rangeGroup₀_units :
    IsUnit (⟨(unit v : Γ₀), coe_unit_mem_rangeGroup₀ v⟩ : v.rangeGroup₀):= by
  simp only [isUnit_iff_exists_inv, Subtype.exists, Submonoid.mk_mul_mk,
    Submonoid.mk_eq_one, exists_prop]
  refine ⟨(unit v)⁻¹,
    MonoidHomWithZero.inv_mem_range₀ (coe_unit_mem_rangeGroup₀ v),
    by simp⟩

/-- Nontriviality of `v.rangeGroup₀ˣ` for valuations of rank 1 -/
@[nontriviality]
instance nontrivial_range₀ : Nontrivial (v.rangeGroup₀ˣ) := by
  use (coe_unit_mem_rangeGroup₀_units v).unit, 1
  rw [ne_eq, Units.ext_iff, ← Subtype.coe_inj, IsUnit.unit_spec]
  simp [unit_ne_one v]

-- TODO : generalize to `ValuationRing K`
theorem exists_val_lt {K : Type*} [Field K] (v : Valuation K Γ₀) [RankOne v]
    {γ : ℝ≥0} (hγ : γ ≠ 0) :
    (∃ (x : K), x ≠ 0 ∧ RankLeOne.hom v (v x) < γ) := by
  have hγ_pos : 0 < γ := pos_iff_ne_zero.mpr hγ
  obtain ⟨x, h⟩ :=
    NNReal.exists_lt_of_strictMono (RankLeOne.strictMono v.rangeGroup₀_restrict) hγ_pos
  have hx := x.val.prop
  simp only [mem_rangeGroup₀_iff] at hx
  obtain ⟨a, b, ha, hx⟩ := hx
  use b / a
  suffices ha' : a ≠ 0 by
    constructor
    · simp only [ne_eq, div_eq_zero_iff, not_or]
      refine ⟨?_, ha'⟩
      intro hb'
      apply Units.ne_zero x
      rw [← Subtype.coe_inj]
      simp only [hb', _root_.map_zero, mul_eq_zero, map_eq_zero,
        Classical.or_iff_not_imp_left] at hx
      exact hx ha'
    · simp only [map_div₀, ← hx, _root_.map_mul]
      rw [mul_div_cancel_left₀ _ <| (map_ne_zero (RankLeOne.hom v)).mpr ha]
      exact h
  intro ha'; apply ha; rw [ha', map_zero]

-- TODO : generalize to `ValuationRing K`
theorem exists_val_lt' {K : Type*} [Field K] (v : Valuation K Γ₀) [RankOne v] (γ : Γ₀ˣ) :
    (∃ (x : K), x ≠ 0 ∧ v x < γ) := by
  have : RankLeOne.hom v γ ≠ 0 := by
    apply ne_of_gt
    rw [← (RankLeOne.hom v).map_zero]
    exact RankLeOne.strictMono _ γ.zero_lt
  obtain ⟨x, hx, h⟩ := RankOne.exists_val_lt v this
  use x, hx
  rwa [StrictMono.lt_iff_lt (RankLeOne.strictMono v)] at h

end RankOne

namespace RankLeOne

variable {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v]

def rankOne_of_exists (H : ∃ x ≠ 0, v x ≠ 1) : RankOne v where
  nontrivial' := by
    by_contra H'
    push_neg at H'
    obtain ⟨x, hx, hx'⟩ := H
    exact hx' (H' x ((ne_zero_iff v).mpr hx))

def rankOne_of_nontrivial (H : Nontrivial v.rangeGroup₀ˣ) : RankOne v where
  nontrivial' := by
    by_contra H'
    push_neg at H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨a, b, ha, hab⟩ := v.mem_rangeGroup₀_iff.mp (x : v.rangeGroup₀).prop
    rw [ne_eq, ← Units.val_eq_one, ← OneMemClass.coe_eq_one] at hx
    apply hx
    rw [eq_comm, ← inv_mul_eq_iff_eq_mul₀ ha, inv_mul_eq_div, ← map_div₀] at hab
    rw [← hab]
    apply H'
    simp only [map_div₀, ne_eq, div_eq_zero_iff, map_eq_zero, not_or]
    simp only [ne_eq, map_eq_zero] at ha
    refine ⟨fun h ↦ ?_, ha⟩
    apply x.ne_zero
    rw [← Subtype.coe_inj, MonoidHomWithZero.range₀_coe_zero, ← hab, h]
    simp

theorem exists_val_lt {K : Type*} [Field K] (v : Valuation K Γ₀) [RankLeOne v] :
    Subsingleton (v.rangeGroup₀ˣ) ∨
      ∀ {γ : ℝ≥0} (_ : γ ≠ 0), ∃ (x : K), x ≠ 0 ∧ (RankLeOne.hom v) (v x) < γ := by
  classical
  simp only [ne_eq, or_iff_not_imp_left, not_subsingleton_iff_nontrivial]
  intro H
  let hv : RankOne v := rankOne_of_nontrivial v H
  apply RankOne.exists_val_lt

end RankLeOne

end Valuation
