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

open Function Set Pointwise

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

/-! ### Translation lemmas -/

section Translation

lemma IsMIntegralCurveOn.comp_add (hγ : IsMIntegralCurveOn γ v s) (dt : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v (-dt +ᵥ s) := by
  intros t ht
  rw [comp_apply, ← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  rw [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm,
    ← mem_setOf (p := fun t ↦ t + dt ∈ s)] at ht
  have : -dt +ᵥ s ⊆ (fun x ↦ x + dt) ⁻¹' s := by
    intro t' ht'
    rw [Set.mem_vadd_set] at ht'
    obtain ⟨t'', ht'', heq⟩ := ht'
    rw [vadd_eq_add, neg_add_eq_iff_eq_add, add_comm] at heq
    rwa [Set.mem_preimage, ← heq]
  apply HasMFDerivWithinAt.comp t (hγ (t + dt) ht) _ this
  refine ⟨(continuous_add_right _).continuousWithinAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact (hasFDerivWithinAt_id _ _).add_const _

lemma isMIntegralCurveOn_comp_add {dt : ℝ} :
    IsMIntegralCurveOn γ v s ↔ IsMIntegralCurveOn (γ ∘ (· + dt)) v (-dt +ᵥ s) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]

lemma isMIntegralCurveOn_comp_sub {dt : ℝ} :
    IsMIntegralCurveOn γ v s ↔ IsMIntegralCurveOn (γ ∘ (· - dt)) v (dt +ᵥ s) := by
  simpa using isMIntegralCurveOn_comp_add (dt := -dt)

lemma IsMIntegralCurveAt.comp_add (hγ : IsMIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert h.comp_add dt
  rw [Metric.vadd_ball, vadd_eq_add, neg_add_eq_sub]

lemma isMIntegralCurveAt_comp_add {dt : ℝ} :
    IsMIntegralCurveAt γ v t₀ ↔ IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

lemma isMIntegralCurveAt_comp_sub {dt : ℝ} :
    IsMIntegralCurveAt γ v t₀ ↔ IsMIntegralCurveAt (γ ∘ (· - dt)) v (t₀ + dt) := by
  simpa using isMIntegralCurveAt_comp_add (dt := -dt)

lemma IsMIntegralCurve.comp_add (hγ : IsMIntegralCurve γ v) (dt : ℝ) :
    IsMIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  simpa using hγ.comp_add dt

lemma isMIntegralCurve_comp_add {dt : ℝ} :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve (γ ∘ (· + dt)) v := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma isMIntegralCurve_comp_sub {dt : ℝ} :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve (γ ∘ (· - dt)) v := by
  simpa using isMIntegralCurve_comp_add (dt := -dt)

end Translation

/-! ### Scaling lemmas -/

section Scaling

lemma IsMIntegralCurveOn.comp_mul (hγ : IsMIntegralCurveOn γ v s) (a : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  intros t ht
  rw [comp_apply, Pi.smul_apply, ← ContinuousLinearMap.smulRight_comp]
  have : {t | t * a ∈ s} ⊆ (fun x ↦ x * a) ⁻¹' s := by
    intro t' ht'
    rw [Set.mem_setOf] at ht'
    rw [Set.mem_preimage]
    exact ht'
  refine HasMFDerivWithinAt.comp t (hγ (t * a) ht)
    ⟨(continuous_mul_right _).continuousWithinAt, ?_⟩ this
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact HasFDerivWithinAt.mul_const' (hasFDerivWithinAt_id _ _) _

lemma isMIntegralCurveOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveOn γ v s ↔ IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  refine ⟨fun hγ ↦ hγ.comp_mul a, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_setOf_eq, mul_assoc, inv_mul_eq_div, div_self ha, mul_one, setOf_mem_eq]

lemma IsMIntegralCurveAt.comp_mul_ne_zero (hγ : IsMIntegralCurveAt γ v t₀) {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert h.comp_mul a
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq,
    lt_div_iff₀ (abs_pos.mpr ha), ← abs_mul, sub_mul, div_mul_cancel₀ _ ha]

lemma isMIntegralCurveAt_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveAt γ v t₀ ↔ IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  refine ⟨fun hγ ↦ hγ.comp_mul_ne_zero ha, fun hγ ↦ ?_⟩
  convert hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]

lemma IsMIntegralCurve.comp_mul (hγ : IsMIntegralCurve γ v) (a : ℝ) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _

lemma isMIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  refine ⟨fun hγ ↦ hγ.comp_mul _, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
is a global integral curve of `v`. -/
lemma isMIntegralCurve_const {x : M} (h : v x = 0) : IsMIntegralCurve (fun _ ↦ x) v := by
  intro t
  rw [h, ← ContinuousLinearMap.zero_apply (R₁ := ℝ) (R₂ := ℝ) (1 : ℝ),
    ContinuousLinearMap.smulRight_one_one]
  exact hasMFDerivAt_const ..

end Scaling
