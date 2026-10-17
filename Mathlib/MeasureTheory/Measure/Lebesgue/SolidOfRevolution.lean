/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volume of solids of revolution and of cones

We compute the volume of the solid obtained by rotating the region below the graph of a function
around an axis, in `ℝ × EuclideanSpace ℝ (Fin 2)`, and the volume of a cone over an arbitrary
measurable base in `ℝ × F`, for `F` a finite-dimensional real normed space.

## Main statements

* `MeasureTheory.Measure.prod_setOf_mem_closedBall`: Cavalieri's principle for a region of a
  product whose slices are closed balls.
* `EuclideanSpace.volume_solidOfRevolution`: the solid obtained by rotating the region below the
  graph of a nonnegative continuous function `f` on `[a, b]` has volume `π ∫ₐᵇ f(x)² dx`.
* `MeasureTheory.Measure.volume_prod_convexJoin_singleton_prod`: in dimension `n`, the cone
  `convexJoin ℝ {a} ({c} ×ˢ B)` with apex `a` over a base `B` lying in the hyperplane `{c} × F`
  has measure `μ B * |c - a.1| / n`.
* `EuclideanSpace.volume_cone`: a cone of radius `R` and height `H` has volume `π R² H / 3`,
  deduced from the previous statement.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace MeasureTheory.Measure

variable {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure α} {ν : Measure E} [SFinite ν]

/-- **Cavalieri's principle** for a region whose slices are balls: the measure of
`{(x, y) | x ∈ s, y ∈ closedBall c (r x)}` is the integral over `s` of the measures of the
balls. -/
theorem prod_setOf_mem_closedBall {s : Set α} (hs : MeasurableSet s) {r : α → ℝ}
    (hr : Measurable r) (c : E) :
    μ.prod ν {p : α × E | p.1 ∈ s ∧ p.2 ∈ closedBall c (r p.1)} =
      ∫⁻ x in s, ν (closedBall c (r x)) ∂μ := by
  have hm : MeasurableSet {p : α × E | p.1 ∈ s ∧ p.2 ∈ closedBall c (r p.1)} :=
    (measurable_fst hs).inter <| measurableSet_le
      ((continuous_id.dist continuous_const).measurable.comp measurable_snd)
      (hr.comp measurable_fst)
  rw [prod_apply hm, ← lintegral_indicator hs]
  exact lintegral_congr fun x ↦ by by_cases hx : x ∈ s <;> simp [hx, Set.preimage, closedBall]

section Cone

open scoped Pointwise

private lemma image_convexJoin_singleton {E E' : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup E'] [Module ℝ E'] (f : E →ᵃ[ℝ] E') (x : E) (s : Set E) :
    f '' convexJoin ℝ {x} s = convexJoin ℝ {f x} (f '' s) := by
  simp [convexJoin_singleton_left, image_iUnion₂, image_segment]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma convexJoin_zero_prod {h : ℝ} (hh : 0 < h) (B : Set F) :
    convexJoin ℝ {0} ({h} ×ˢ B) = {p : ℝ × F | p.1 ∈ Icc 0 h ∧ p.2 ∈ (p.1 / h) • B} := by
  ext ⟨t, y⟩
  simp only [convexJoin_singleton_left, mem_iUnion, segment_eq_image, smul_zero, zero_add,
    mem_image, mem_prod, mem_singleton_iff, mem_ofPred_eq, mem_smul_set, Prod.ext_iff,
    Prod.smul_mk, smul_eq_mul, exists_prop, Prod.exists]
  constructor
  · rintro ⟨_, y, ⟨rfl, hy⟩, θ, hθ, rfl, rfl⟩
    exact ⟨⟨mul_nonneg hθ.1 hh.le, mul_le_of_le_one_left hh.le hθ.2⟩, y, hy, by field_simp⟩
  · rintro ⟨ht, y, hy, rfl⟩
    exact ⟨h, y, ⟨rfl, hy⟩, t / h, ⟨div_nonneg ht.1 hh.le, (div_le_one hh).2 ht.2⟩, by field_simp,
      rfl⟩

variable [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] (μ : Measure F)
  [μ.IsAddHaarMeasure]

private lemma volume_prod_convexJoin_zero_prod {B : Set F} (hB : MeasurableSet B) {h : ℝ}
    (hh : 0 < h) :
    (volume.prod μ) (convexJoin ℝ {0} ({h} ×ˢ B)) =
      μ B * ENNReal.ofReal (h / (Module.finrank ℝ F + 1)) := by
  rw [convexJoin_zero_prod hh]
  set C := {p : ℝ × F | p.1 ∈ Icc 0 h ∧ p.2 ∈ (p.1 / h) • B}
  have hC : MeasurableSet C := by
    have : C = {p : ℝ × F | p.1 ∈ Ioc 0 h ∧ (h / p.1) • p.2 ∈ B} ∪ {0} ×ˢ ((0 : ℝ) • B) := by
      ext ⟨t, y⟩
      rcases eq_or_ne t 0 with rfl | ht
      · simp [C, hh.le]
      · simp [C, ht, mem_smul_set_iff_inv_smul_mem₀ (div_ne_zero ht hh.ne'), le_iff_lt_or_eq,
          eq_comm (a := (0 : ℝ))]
    rw [this]
    exact ((measurable_fst measurableSet_Ioc).inter (hB.preimage (by fun_prop))).union
      ((measurableSet_singleton 0).prod
        (subsingleton_singleton.anti (zero_smul_set_subset B)).measurableSet)
  have hslice (t : ℝ) : μ (Prod.mk t ⁻¹' C) =
      (Icc 0 h).indicator (fun t ↦ ENNReal.ofReal ((t / h) ^ Module.finrank ℝ F) * μ B) t := by
    by_cases ht : t ∈ Icc 0 h
    · simp [C, ht.1, ht.2, Set.preimage, addHaar_smul, abs_of_nonneg (div_nonneg ht.1 hh.le)]
    · rw [indicator_of_notMem ht]
      exact measure_mono_null (fun y hy ↦ ht hy.1) measure_empty
  rw [prod_apply hC, lintegral_congr hslice, lintegral_indicator measurableSet_Icc,
    lintegral_mul_const _ (by fun_prop), mul_comm,
    ← ofReal_integral_eq_lintegral_ofReal, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh.le]
  · congr 2
    simp only [div_pow, intervalIntegral.integral_div, integral_pow]
    field
  · exact (by fun_prop : Continuous fun t : ℝ ↦ (t / h) ^ Module.finrank ℝ F).integrableOn_Icc
  · exact (ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ by have := ht.1; positivity

/-- **Volume of a cone**: in `ℝ × F`, the cone with apex `a` over the base `{c} × B` has
measure `μ B * |c - a.1| / n`, where `n = finrank ℝ F + 1` is the dimension of `ℝ × F`. -/
theorem volume_prod_convexJoin_singleton_prod {B : Set F} (hB : MeasurableSet B) (a : ℝ × F)
    (c : ℝ) :
    (volume.prod μ) (convexJoin ℝ {a} ({c} ×ˢ B)) =
      μ B * ENNReal.ofReal (|c - a.1| / (Module.finrank ℝ F + 1)) := by
  set L : ℝ × F →ₗ[ℝ] ℝ × F := ((c - a.1) • LinearMap.id).prodMap LinearMap.id
  have hK : convexJoin ℝ {a} ({c} ×ˢ B) =
      a +ᵥ L '' convexJoin ℝ {0} ({1} ×ˢ (-a.2 +ᵥ B)) := by
    let f := (AffineEquiv.constVAdd ℝ (ℝ × F) a).toAffineMap.comp L.toAffineMap
    have hf : a +ᵥ L '' convexJoin ℝ {0} ({1} ×ˢ (-a.2 +ᵥ B)) =
        f '' convexJoin ℝ {0} ({1} ×ˢ (-a.2 +ᵥ B)) := by
      rw [← image_vadd, image_image]
      rfl
    rw [hf, image_convexJoin_singleton]
    congr
    · simp [f]
    · ext ⟨t, y⟩
      simp [f, L, mem_vadd_set, Prod.ext_iff, eq_comm, and_comm]
  have hL : LinearMap.det L = c - a.1 := by simp [L, LinearMap.det_prodMap]
  rw [hK, measure_vadd, addHaar_image_linearMap, hL,
    volume_prod_convexJoin_zero_prod μ (hB.const_vadd _) one_pos, measure_vadd, mul_left_comm,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_one_div]

end Cone

end MeasureTheory.Measure

namespace EuclideanSpace

theorem volume_setOf_mem_norm_le {s : Set ℝ} (hs : MeasurableSet s) {r : ℝ → ℝ}
    (hr : Measurable r) :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ s ∧ ‖p.2‖ ≤ r p.1} =
      ∫⁻ x in s, ENNReal.ofReal (r x) ^ 2 * ENNReal.ofReal π := by
  simp_rw [← mem_closedBall_zero_iff]
  rw [Measure.volume_eq_prod, Measure.prod_setOf_mem_closedBall hs hr]
  simp

/-- **Volume of a solid of revolution**: rotating the region below the graph of a nonnegative
continuous function `f` on `[a, b]` around the first axis gives a solid of volume
`π ∫ₐᵇ f(x)² dx`. -/
theorem volume_solidOfRevolution {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc a b ∧ ‖p.2‖ ≤ f p.1} =
      ENNReal.ofReal (π * ∫ x in a..b, f x ^ 2) := by
  -- only the values of `f` on `[a, b]` matter, so we may replace it by a measurable function
  set g : ℝ → ℝ := (Icc a b).piecewise f 0
  have hset : {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc a b ∧ ‖p.2‖ ≤ f p.1} =
      {p | p.1 ∈ Icc a b ∧ ‖p.2‖ ≤ g p.1} := by
    ext p
    simp +contextual [g]
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  rw [hset, volume_setOf_mem_norm_le measurableSet_Icc hg, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal]
  · refine setLIntegral_congr_fun measurableSet_Icc fun x hx ↦ ?_
    simp only [g, Set.piecewise_eq_of_mem _ _ _ hx]
    rw [← ENNReal.ofReal_pow (hf₀ x hx), ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  · exact ((hf.pow 2).const_mul π).integrableOn_compact isCompact_Icc
  · exact .of_forall fun x ↦ by positivity

/-- **Volume of a cone** of radius `R` and height `H`: one third of the cylinder with the same
base and height. -/
theorem volume_cone {R H : ℝ} (hR : 0 ≤ R) (hH : 0 < H) :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc 0 H ∧ ‖p.2‖ ≤ R * p.1 / H} =
      ENNReal.ofReal (π * R ^ 2 * H / 3) := by
  have hC : {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc 0 H ∧ ‖p.2‖ ≤ R * p.1 / H} =
      convexJoin ℝ {0} ({H} ×ˢ closedBall 0 R) := by
    rw [Measure.convexJoin_zero_prod hH]
    ext ⟨t, y⟩
    exact and_congr_right fun ht ↦ by
      rw [smul_closedBall _ _ hR, smul_zero, mem_closedBall_zero_iff, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ht.1 hH.le), div_mul_eq_mul_div, mul_comm]
  rw [hC, Measure.volume_eq_prod,
    Measure.volume_prod_convexJoin_singleton_prod _ measurableSet_closedBall]
  rw [volume_closedBall_fin_two, finrank_euclideanSpace_fin, Prod.fst_zero, sub_zero,
    abs_of_pos hH, ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

end EuclideanSpace
