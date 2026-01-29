/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

## Tags

integral curve, vector field
-/

@[expose] public section

open Function Set Pointwise

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {γ γ' : ℝ → E} {v : E → E} {s s' : Set ℝ} {t₀ : ℝ}

/-! ### Translation lemmas -/

section Translation

lemma IsIntegralCurveOn.comp_add (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· + dt)) v (-dt +ᵥ s) := by
  intros t ht
  rw [comp_apply, hasDerivWithinAt_iff_hasFDerivWithinAt, Function.comp_def,
    hasFDerivWithinAt_comp_add_right, ← hasDerivWithinAt_iff_hasFDerivWithinAt, vadd_neg_vadd]
  apply hγ (t + dt)
  rwa [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm] at ht

lemma isIntegralCurveOn_comp_add {dt : ℝ} :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· + dt)) v (-dt +ᵥ s) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]

lemma isIntegralCurveOn_comp_sub {dt : ℝ} :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· - dt)) v (dt +ᵥ s) := by
  simpa using isIntegralCurveOn_comp_add (dt := -dt)

lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isIntegralCurveAt_iff_exists_pos] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert h.comp_add dt
  rw [Metric.vadd_ball, vadd_eq_add, neg_add_eq_sub]

lemma isIntegralCurveAt_comp_add {dt : ℝ} :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

lemma isIntegralCurveAt_comp_sub {dt : ℝ} :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· - dt)) v (t₀ + dt) := by
  simpa using isIntegralCurveAt_comp_add (dt := -dt)

lemma IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· + dt)) v := by
  rw [← isIntegralCurveOn_univ] at *
  simpa using hγ.comp_add dt

lemma isIntegralCurve_comp_add {dt : ℝ} :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· + dt)) v := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma isIntegralCurve_comp_sub {dt : ℝ} :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· - dt)) v := by
  simpa using isIntegralCurve_comp_add (dt := -dt)

end Translation

/-! ### Scaling lemmas -/

section Scaling

lemma IsIntegralCurveOn.comp_mul (hγ : IsIntegralCurveOn γ v s) (a : ℝ) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  intros t ht
  rw [comp_apply, Pi.smul_apply, hasDerivWithinAt_iff_hasFDerivWithinAt,
    ← ContinuousLinearMap.toSpanSingleton_comp_toSpanSingleton]
  refine (hγ (t * a) ht |>.hasFDerivWithinAt).comp (t := s) _ ?_ (fun _ ht' ↦ ht')
  apply HasFDerivAt.hasFDerivWithinAt
  rw [← hasDerivAt_iff_hasFDerivAt]
  exact hasDerivAt_mul_const _

lemma isIntegralCurveOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· * a)) (a • v) (a⁻¹ • s) := by
  have heq : a⁻¹ • s = { t | t * a ∈ s } := by
    ext t
    rw [mem_inv_smul_set_iff₀ ha, smul_eq_mul, mul_comm]
    rfl
  refine ⟨heq ▸ fun hγ ↦ hγ.comp_mul a, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mul_comm _ a⁻¹, ← smul_eq_mul, mem_inv_smul_set_iff₀ ha, smul_inv_smul₀ ha,
      setOf_mem_eq]

lemma IsIntegralCurveAt.comp_mul_ne_zero (hγ : IsIntegralCurveAt γ v t₀) {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  rw [isIntegralCurveAt_iff_exists_pos] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert h.comp_mul a
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq,
    lt_div_iff₀ (abs_pos.mpr ha), ← abs_mul, sub_mul, div_mul_cancel₀ _ ha]

lemma isIntegralCurveAt_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  refine ⟨fun hγ ↦ hγ.comp_mul_ne_zero ha, fun hγ ↦ ?_⟩
  convert hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]

lemma IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : ℝ) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [← isIntegralCurveOn_univ] at *
  exact hγ.comp_mul _

lemma isIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  refine ⟨fun hγ ↦ hγ.comp_mul _, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
is a global integral curve of `v`. -/
lemma isIntegralCurve_const {x : E} (h : v x = 0) : IsIntegralCurve (fun _ ↦ x) v :=
  fun _ ↦ h ▸ hasDerivAt_const _ _

end Scaling
