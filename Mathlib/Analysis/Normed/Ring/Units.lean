/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `Units.add` and `Units.ofNearby` (based on `Units.oneSub` defined elsewhere)
state, in varying forms, that perturbations of a unit are units. They are not stated
in their optimal form; more precise versions would use the spectral radius.

The first main result is `Units.isOpen`: the group of units of a normed ring with summable
geometric series is an open subset of the ring. Furthermore, the topology with which `Rˣ` is
equipped (induced by the map `Rˣ → R × R` given by `a ↦ (a, a⁻¹)`) coincides with the subspace
topology; together we provide this in the form of an `IsOpenUnits`-instance.

The function `Ring.inverse` (defined elsewhere), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is a
unit and `0` if not.  The other major results of this file (notably `NormedRing.inverse_add`,
`NormedRing.inverse_add_norm` and `NormedRing.inverse_add_norm_diff_nth_order`) cover the asymptotic
properties of `Ring.inverse (x + t)` as `t → 0`.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Ring

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

namespace Units

/-- In a normed ring with summable geometric series, a perturbation of a unit `x` by an
element `t` of distance less than `‖x⁻¹‖⁻¹` from `x` is a unit.
Here we construct its `Units` structure. -/
@[simps! val]
def add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  Units.copy -- to make `add_val` true definitionally, for convenience
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      nontriviality R using zero_lt_one
      have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
      calc
        ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
        _ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := norm_mul_le (x⁻¹).1 _
        _ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by nlinarith only [h, hpos]
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)))
    (x + t) (by simp [mul_add]) _ rfl

/-- In a normed ring with summable geometric series, an element `y` of distance less
than `‖x⁻¹‖⁻¹` from `x` is a unit. Here we construct its `Units` structure. -/
@[simps! val]
def ofNearby (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  (x.add (y - x : R) h).copy y (by simp) _ rfl

end Units

namespace nonunits

/-- The `nonunits` in a normed ring with summable geometric series are contained in the
complement of the ball of radius `1` centered at `1 : R`. -/
theorem subset_compl_ball : nonunits R ⊆ (Metric.ball (1 : R) 1)ᶜ := fun x hx h₁ ↦ hx <|
  sub_sub_self 1 x ▸ (Units.oneSub (1 - x) (by rwa [mem_ball_iff_norm'] at h₁)).isUnit

end nonunits

namespace NormedRing

open Asymptotics Filter Metric Finset Ring

theorem inverse_one_sub (t : R) (h : ‖t‖ < 1) : inverse (1 - t) = ↑(Units.oneSub t h)⁻¹ := by
  rw [← inverse_unit (Units.oneSub t h), Units.val_oneSub]

/-- The formula `Ring.inverse (x + t) = Ring.inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently
small. -/
theorem inverse_add (x : Rˣ) :
    ∀ᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ = (1 + ↑x⁻¹ * t)⁻¹ʳ * ↑x⁻¹ := by
  nontriviality R
  rw [Metric.eventually_nhds_iff]
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, by cancel_denoms, fun t ht ↦ ?_⟩
  rw [dist_zero_right] at ht
  rw [← x.val_add t ht, inverse_unit, Units.add, Units.copy_eq, mul_inv_rev, Units.val_mul,
    ← inverse_unit, Units.val_oneSub, sub_neg_eq_add]

theorem inverse_one_sub_nth_order' (n : ℕ) {t : R} (ht : ‖t‖ < 1) :
    inverse ((1 : R) - t) = (∑ i ∈ range n, t ^ i) + t ^ n * inverse (1 - t) :=
  have := _root_.summable_geometric_of_norm_lt_one ht
  calc inverse (1 - t) = ∑' i : ℕ, t ^ i := inverse_one_sub t ht
    _ = ∑ i ∈ range n, t ^ i + ∑' i : ℕ, t ^ (i + n) := (this.sum_add_tsum_nat_add _).symm
    _ = (∑ i ∈ range n, t ^ i) + t ^ n * inverse (1 - t) := by
      simp only [inverse_one_sub t ht, add_comm _ n, pow_add, this.tsum_mul_left]; rfl

theorem inverse_one_sub_nth_order (n : ℕ) :
    ∀ᶠ t in 𝓝 0, inverse ((1 : R) - t) = (∑ i ∈ range n, t ^ i) + t ^ n * inverse (1 - t) :=
  Metric.eventually_nhds_iff.2 ⟨1, one_pos, fun t ht ↦ inverse_one_sub_nth_order' n <| by
    rwa [← dist_zero_right]⟩


/-- The formula
`Ring.inverse (x + t) =
  (∑ i ∈ Finset.range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * Ring.inverse (x + t)`
holds for `t` sufficiently small. -/
theorem inverse_add_nth_order (x : Rˣ) (n : ℕ) :
    ∀ᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ =
      (∑ i ∈ range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (-↑x⁻¹ * t) ^ n * (x + t)⁻¹ʳ := by
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
    (mulLeft_continuous _).tendsto' _ _ <| mul_zero _
  filter_upwards [inverse_add x, hzero.eventually (inverse_one_sub_nth_order n)] with t ht ht'
  rw [neg_mul, sub_neg_eq_add] at ht'
  conv_lhs => rw [ht, ht', add_mul, ← neg_mul, mul_assoc]
  rw [ht]

theorem inverse_one_sub_norm : (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun _t => 1 : R → ℝ) := by
  simp only [IsBigO, IsBigOWith, Metric.eventually_nhds_iff]
  refine ⟨‖(1 : R)‖ + 1, (2 : ℝ)⁻¹, by simp, fun t ht ↦ ?_⟩
  rw [dist_zero_right] at ht
  have ht' : ‖t‖ < 1 := by linarith
  simp only [inverse_one_sub t ht', norm_one, mul_one]
  change ‖∑' n : ℕ, t ^ n‖ ≤ _
  have := tsum_geometric_le_of_norm_lt_one t ht'
  have : (1 - ‖t‖)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by simp) (by linarith)
  linarith

/-- The function `fun t ↦ inverse (x + t)` is O(1) as `t → 0`. -/
theorem inverse_add_norm (x : Rˣ) : (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun _t => (1 : ℝ) := by
  refine EventuallyEq.trans_isBigO (inverse_add x) (one_mul (1 : ℝ) ▸ ?_)
  simp only [← sub_neg_eq_add, ← neg_mul]
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
    (mulLeft_continuous _).tendsto' _ _ <| mul_zero _
  exact (inverse_one_sub_norm.comp_tendsto hzero).mul (isBigO_const_const _ one_ne_zero _)

/-- The function
`fun t ↦ Ring.inverse (x + t) - (∑ i ∈ Finset.range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
theorem inverse_add_norm_diff_nth_order (x : Rˣ) (n : ℕ) :
    (fun t : R => (↑x + t)⁻¹ʳ - (∑ i ∈ range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)]
      fun t => ‖t‖ ^ n := by
  refine EventuallyEq.trans_isBigO (.fun_sub (inverse_add_nth_order x n) (.refl _ _)) ?_
  simp only [add_sub_cancel_left]
  refine ((isBigO_refl _ _).norm_right.mul (inverse_add_norm x)).trans ?_
  simp only [mul_one, isBigO_norm_left]
  exact ((isBigO_refl _ _).norm_right.const_mul_left _).pow _

/-- The function `fun t ↦ Ring.inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
theorem inverse_add_norm_diff_first_order (x : Rˣ) :
    (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ := by
  simpa using inverse_add_norm_diff_nth_order x 1

/-- The function `fun t ↦ Ring.inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹` is `O(t ^ 2)` as `t → 0`. -/
theorem inverse_add_norm_diff_second_order (x : Rˣ) :
    (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ ^ 2 := by
  convert! inverse_add_norm_diff_nth_order x 2 using 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, add_mul, one_mul,
    ← sub_sub, neg_mul, sub_neg_eq_add]

@[deprecated (since := "2026-06-19")] alias inverse_continuousAt := Ring.inverse_continuousAt

/-- In a normed ring with summable geometric series, the coercion from `Rˣ` (equipped with the
induced topology from the embedding in `R × R`) to `R` is an open embedding.

You can use this fact using the lemma `Units.isOpenEmbedding_val` that is part of the
`IsOpenUnits` API. -/
instance instIsOpenUnits : IsOpenUnits R where
  isOpenEmbedding_unitsVal := {
    toIsEmbedding := by
      refine Units.isEmbedding_val_mk' (fun _ ⟨x, hx⟩ ↦ hx ▸ ContinuousAt.continuousWithinAt ?_)
        Ring.inverse_unit
      have h_is_o : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R → ℝ) :=
        (inverse_add_norm_diff_first_order x).trans_isLittleO
          (isLittleO_id_const one_ne_zero).norm_left
      have h_lim : Tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
        refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
        exact tendsto_iff_norm_sub_tendsto_zero.mp tendsto_id
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero, inverse_unit]
      simpa [Function.comp_def] using h_is_o.norm_left.tendsto_div_nhds_zero.comp h_lim
    isOpen_range := by
      nontriviality R
      rw [Metric.isOpen_iff]
      rintro _ ⟨x, rfl⟩
      refine ⟨‖(↑x⁻¹ : R)‖⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), fun y hy ↦ ?_⟩
      rw [mem_ball_iff_norm] at hy
      exact (x.ofNearby y hy).isUnit }

end NormedRing

namespace Ideal

/-- An ideal which contains an element within `1` of `1 : R` is the unit ideal. -/
theorem eq_top_of_norm_lt_one (I : Ideal R) {x : R} (hxI : x ∈ I) (hx : ‖1 - x‖ < 1) : I = ⊤ :=
  let u := Units.oneSub (1 - x) hx
  I.eq_top_iff_one.mpr <| by
    simpa only [show u.inv * x = 1 by simp [u]] using I.mul_mem_left u.inv hxI

end Ideal
