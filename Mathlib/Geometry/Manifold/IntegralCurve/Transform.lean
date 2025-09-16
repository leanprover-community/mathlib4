/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

This file mirrors `Mathlib/Analysis/ODE/Transform`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

open Function Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

/-! ### Translation lemmas -/

section Translation

lemma IsMIntegralCurveOn.comp_add (hγ : IsMIntegralCurveOn γ v s) (dt : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  intro t ht
  rw [comp_apply, ← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivWithinAt.comp t (hγ (t + dt) ht) _ subset_rfl
  refine ⟨(continuous_add_right _).continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  exact (hasFDerivWithinAt_id _ _).add_const _

@[deprecated (since := "2025-08-12")] alias IsIntegralCurveOn.comp_add :=
  IsMIntegralCurveOn.comp_add

lemma isMIntegralCurveOn_comp_add {dt : ℝ} :
    IsMIntegralCurveOn γ v s ↔ IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp
  · simp

@[deprecated (since := "2025-08-12")] alias isIntegralCurveOn_comp_add :=
  isMIntegralCurveOn_comp_add

lemma isMIntegralCurveOn_comp_sub {dt : ℝ} :
    IsMIntegralCurveOn γ v s ↔ IsMIntegralCurveOn (γ ∘ (· - dt)) v { t | t - dt ∈ s } := by
  simpa using isMIntegralCurveOn_comp_add (dt := -dt)

@[deprecated (since := "2025-08-12")] alias isIntegralCurveOn_comp_sub :=
  isMIntegralCurveOn_comp_sub

lemma IsMIntegralCurveAt.comp_add (hγ : IsMIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert h.comp_add dt
  rw [Metric.ball]
  simp_rw [Metric.mem_ball, Real.dist_eq, ← sub_add, add_sub_right_comm]

@[deprecated (since := "2025-08-12")] alias IsIntegralCurveAt.comp_add :=
  IsMIntegralCurveAt.comp_add

lemma isMIntegralCurveAt_comp_add {dt : ℝ} :
    IsMIntegralCurveAt γ v t₀ ↔ IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

@[deprecated (since := "2025-08-12")] alias isIntegralCurveAt_comp_add :=
  isMIntegralCurveAt_comp_add

lemma isMIntegralCurveAt_comp_sub {dt : ℝ} :
    IsMIntegralCurveAt γ v t₀ ↔ IsMIntegralCurveAt (γ ∘ (· - dt)) v (t₀ + dt) := by
  simpa using isMIntegralCurveAt_comp_add (dt := -dt)

@[deprecated (since := "2025-08-12")] alias isIntegralCurveAt_comp_sub :=
  isMIntegralCurveAt_comp_sub

lemma IsMIntegralCurve.comp_add (hγ : IsMIntegralCurve γ v) (dt : ℝ) :
    IsMIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  simpa using hγ.comp_add dt

@[deprecated (since := "2025-08-12")] alias IsIntegralCurve.comp_add := IsMIntegralCurve.comp_add

lemma isMIntegralCurve_comp_add {dt : ℝ} :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve (γ ∘ (· + dt)) v := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

@[deprecated (since := "2025-08-12")] alias isIntegralCurve_comp_add := isMIntegralCurve_comp_add

lemma isMIntegralCurve_comp_sub {dt : ℝ} :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve (γ ∘ (· - dt)) v := by
  simpa using isMIntegralCurve_comp_add (dt := -dt)

@[deprecated (since := "2025-08-12")] alias isIntegralCurve_comp_sub := isMIntegralCurve_comp_sub

end Translation

/-! ### Scaling lemmas -/

section Scaling

lemma IsMIntegralCurveOn.comp_mul (hγ : IsMIntegralCurveOn γ v s) (a : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  intro t ht
  rw [comp_apply, Pi.smul_apply, ← ContinuousLinearMap.smulRight_comp]
  refine HasMFDerivWithinAt.comp t (hγ (t * a) ht)
    ⟨(continuous_mul_right _).continuousWithinAt, ?_⟩ subset_rfl
  simp only [mfld_simps]
  exact HasFDerivWithinAt.mul_const' (hasFDerivWithinAt_id _ _) _

@[deprecated (since := "2025-08-12")] alias IsIntegralCurveOn.comp_mul :=
  IsMIntegralCurveOn.comp_mul

lemma isMIntegralCurveOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveOn γ v s ↔ IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  refine ⟨fun hγ ↦ hγ.comp_mul a, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_setOf_eq, mul_assoc, inv_mul_eq_div, div_self ha, mul_one, setOf_mem_eq]

@[deprecated (since := "2025-08-12")] alias isIntegralCurveOn_comp_mul_ne_zero :=
  isMIntegralCurveOn_comp_mul_ne_zero

lemma IsMIntegralCurveAt.comp_mul_ne_zero (hγ : IsMIntegralCurveAt γ v t₀) {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert h.comp_mul a
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq,
    lt_div_iff₀ (abs_pos.mpr ha), ← abs_mul, sub_mul, div_mul_cancel₀ _ ha]

@[deprecated (since := "2025-08-12")] alias IsIntegralCurveAt.comp_mul_ne_zero :=
  IsMIntegralCurveAt.comp_mul_ne_zero

lemma isMIntegralCurveAt_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveAt γ v t₀ ↔ IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  refine ⟨fun hγ ↦ hγ.comp_mul_ne_zero ha, fun hγ ↦ ?_⟩
  convert hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]

@[deprecated (since := "2025-08-12")] alias isIntegralCurveAt_comp_mul_ne_zero :=
  isMIntegralCurveAt_comp_mul_ne_zero

lemma IsMIntegralCurve.comp_mul (hγ : IsMIntegralCurve γ v) (a : ℝ) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _

@[deprecated (since := "2025-08-12")] alias IsIntegralCurve.comp_mul := IsMIntegralCurve.comp_mul

lemma isMIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  refine ⟨fun hγ ↦ hγ.comp_mul _, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

@[deprecated (since := "2025-08-12")] alias isIntegralCurve_comp_mul_ne_zero :=
  isMIntegralCurve_comp_mul_ne_zero

/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
is a global integral curve of `v`. -/
lemma isMIntegralCurve_const {x : M} (h : v x = 0) : IsMIntegralCurve (fun _ ↦ x) v := by
  intro t
  rw [h, ← ContinuousLinearMap.zero_apply (R₁ := ℝ) (R₂ := ℝ) (1 : ℝ),
    ContinuousLinearMap.smulRight_one_one]
  exact hasMFDerivAt_const ..

@[deprecated (since := "2025-08-12")] alias isIntegralCurve_const := isMIntegralCurve_const

end Scaling
