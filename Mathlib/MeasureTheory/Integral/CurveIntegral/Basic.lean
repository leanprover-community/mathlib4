/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Field.Pointwise
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral of a 1-form along a path

In this file we define the integral of a 1-form along a path indexed by `[0, 1]`
and prove basic properties of this operation.

The integral `∫ᶜ x in γ, ω x` is defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.
More precisely, we use

- `Path.extend γ t` instead of `γ t`, because both derivatives and `intervalIntegral`
  expect globally defined functions;
- `derivWithin γ.extend (Set.Icc 0 1) t`, not `deriv γ.extend t`, for the derivative,
  so that it takes meaningful values at `t = 0` and `t = 1`,
  even though this does not affect the integral.

The argument `ω : E → E →L[𝕜] F` is a `𝕜`-linear 1-form on `E` taking values in `F`,
where `𝕜` is `ℝ` or `ℂ`.
The definition does not depend on `𝕜`, see `curveIntegral_restrictScalars` and nearby lemmas.
However, the fact that `𝕜 = ℝ` is not hardcoded
allows us to avoid inserting `ContinuousLinearMap.restrictScalars` here and there.

## Main definitions

- `curveIntegral ω γ`, notation `∫ᶜ x in γ, ω x`, is the integral of a 1-form `ω` along a path `γ`.
- `CurveIntegrable ω γ` is the predicate saying that the above integral makes sense.

## Main results

We prove that `curveIntegral` well behaves with respect to

- operations on `Path`s, see `curveIntegral_refl`, `curveIntegral_symm`, `curveIntegral_trans` etc;
- algebraic operations on 1-forms, see `curveIntegral_add` etc.

We also show that the derivative of `fun b ↦ ∫ᶜ x in Path.segment a b, ω x`
has derivative `ω a` at `b = a`.
We provide 2 versions of this result: one for derivative (`HasFDerivWithinAt`) within a convex set
and one for `HasFDerivAt`.

## Implementation notes

### Naming

In literature, the integral of a function or a 1-form along a path
is called “line integral”, “path integral”, “curve integral”, or “curvelinear integral”.

We use the name “curve integral” instead of other names for the following reasons:

- for many people whose mother tongue is not English,
  “line integral” sounds like an integral along a straight line;

- we reserve the name "path integral" for Feynmann-style integrals over the space of paths.

### Usage of `ContinuousLinearMap`s for 1-forms

Similarly to the way `fderiv` uses continuous linear maps
while higher order derivatives use continuous multilinear maps,
this file uses `E → E →L[𝕜] F` instead of continuous alternating maps for 1-forms.

### Differentiability assumptions

The definitions in this file make sense if the path is a piecewise $C^1$ curve.
Poincaré lemma (formalization WIP, see #24019) implies that for a closed 1-form on an open set `U`,
the integral depends on the homotopy class of the path only,
thus we can define the integral along a continuous path
or an element of the fundamental groupoid of `U`.

### Usage of an extra field

The definitions in this file deal with `𝕜`-linear 1-forms.
This allows us to avoid using `ContinuousLinearMap.restrictScalars`
in `HasFDerivWithinAt.curveIntegral_segment_source`
and a future formalization of Poincaré lemma.
-/

open Metric MeasureTheory Topology Set Interval AffineMap Convex Filter
open scoped Pointwise unitInterval

section Defs

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}

/-- The function `t ↦ ω (γ t) (γ' t)` which appears in the definition of a curve integral.

This definition is used to factor out common parts of lemmas
about `CurveIntegrable` and `curveIntegral`. -/
noncomputable irreducible_def curveIntegralFun (lemma := curveIntegralFun_def')
    (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) : F :=
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  ω (γ.extend t) (derivWithin γ.extend I t)

/-- A 1-form `ω` is *curve integrable* along a path `γ`,
if the function `curveIntegralFun ω γ t = ω (γ t) (γ' t)` is integrable on `[0, 1]`.

The actual definition uses `Path.extend γ`,
because both interval integrals and derivatives expect globally defined functions.
-/
def CurveIntegrable (ω : E → E →L[𝕜] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (curveIntegralFun ω γ) volume 0 1

/-- Integral of a 1-form `ω : E → E →L[𝕜] F` along a path `γ`,
defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.

The actual definition uses `curveIntegralFun` which uses `Path.extend γ`
and `derivWithin (Path.extend γ) (Set.Icc 0 1) t`,
because calculus-related definitions in Mathlib expect globally defined functions as arguments. -/
noncomputable irreducible_def curveIntegral (lemma := curveIntegral_def')
    (ω : E → E →L[𝕜] F) (γ : Path a b) : F :=
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  ∫ t in 0..1, curveIntegralFun ω γ t

@[inherit_doc curveIntegral]
notation3 "∫ᶜ "(...)" in " γ ", "r:67:(scoped ω => curveIntegral ω γ) => r

/-- curve integral is defined using Bochner integral,
thus it is defined as zero whenever the codomain is not a complete space. -/
theorem curveIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E → E →L[𝕜] F)
    (γ : Path a b) : ∫ᶜ x in γ, ω x = 0 := by
  simp [curveIntegral, intervalIntegral, integral, h]

theorem curveIntegralFun_def [NormedSpace ℝ E] (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) :
    curveIntegralFun ω γ t = ω (γ.extend t) (derivWithin γ.extend I t) := by
  simp only [curveIntegralFun, NormedSpace.restrictScalars_eq]

theorem curveIntegral_def [NormedSpace ℝ F] (ω : E → E →L[𝕜] F) (γ : Path a b) :
    curveIntegral ω γ = ∫ t in 0..1, curveIntegralFun ω γ t := by
  simp only [curveIntegral, NormedSpace.restrictScalars_eq]

theorem curveIntegral_eq_intervalIntegral_deriv [NormedSpace ℝ E] [NormedSpace ℝ F]
    (ω : E → E →L[𝕜] F) (γ : Path a b) :
    ∫ᶜ x in γ, ω x = ∫ t in 0..1, ω (γ.extend t) (deriv γ.extend t) := by
  simp only [curveIntegral_def, curveIntegralFun_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem (by measurability)] with x hx
  rw [derivWithin_of_mem_nhds (by simpa)]

end Defs

/-!
### Operations on paths
-/

section PathOperations

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b c d : E} {ω : E → E →L[𝕜] F}
  {γ γab : Path a b} {γbc : Path b c} {t : ℝ}

@[simp]
theorem curveIntegralFun_refl (ω : E → E →L[𝕜] F) (a : E) : curveIntegralFun ω (.refl a) = 0 := by
  ext
  simp [curveIntegralFun, ← Function.const_def]

@[simp]
theorem curveIntegral_refl (ω : E → E →L[𝕜] F) (a : E) : ∫ᶜ x in .refl a, ω x = 0 := by
  simp [curveIntegral]

@[simp]
theorem CurveIntegrable.refl (ω : E → E →L[𝕜] F) (a : E) : CurveIntegrable ω (.refl a) := by
  simp [CurveIntegrable, Pi.zero_def]

@[simp]
theorem curveIntegralFun_cast (ω : E → E →L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    curveIntegralFun ω (γ.cast hc hd) = curveIntegralFun ω γ := by
  ext t
  simp only [curveIntegralFun_def', Path.extend_cast]

@[simp]
theorem curveIntegral_cast (ω : E → E →L[𝕜] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    ∫ᶜ x in γ.cast hc hd, ω x = ∫ᶜ x in γ, ω x := by
  simp [curveIntegral]

@[simp]
theorem curveIntegrable_cast_iff (hc : c = a) (hd : d = b) :
    CurveIntegrable ω (γ.cast hc hd) ↔ CurveIntegrable ω γ := by
  simp [CurveIntegrable]

protected alias ⟨_, CurveIntegrable.cast⟩ := curveIntegrable_cast_iff

theorem curveIntegralFun_symm_apply (ω : E → E →L[𝕜] F) (γ : Path a b) (t : ℝ) :
    curveIntegralFun ω γ.symm t = -curveIntegralFun ω γ (1 - t) := by
  simp [curveIntegralFun, γ.extend_symm, derivWithin_comp_const_sub]

@[simp]
theorem curveIntegralFun_symm (ω : E → E →L[𝕜] F) (γ : Path a b) :
    curveIntegralFun ω γ.symm = (-curveIntegralFun ω γ <| 1 - ·) :=
  funext <| curveIntegralFun_symm_apply ω γ

protected theorem CurveIntegrable.symm (h : CurveIntegrable ω γ) : CurveIntegrable ω γ.symm := by
  simpa [CurveIntegrable] using (h.comp_sub_left 1).neg.symm

@[simp]
theorem curveIntegrable_symm : CurveIntegrable ω γ.symm ↔ CurveIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
theorem curveIntegral_symm (ω : E → E →L[𝕜] F) (γ : Path a b) :
    ∫ᶜ x in γ.symm, ω x = -∫ᶜ x in γ, ω x := by
  simp [curveIntegral, curveIntegralFun_symm]

theorem curveIntegralFun_trans_of_lt_half (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c)
    (ht : t < 1 / 2) :
    curveIntegralFun ω (γab.trans γbc) t = (2 : ℕ) • curveIntegralFun ω γab (2 * t) := by
  let instE := NormedSpace.restrictScalars ℝ 𝕜 E
  have H₁ : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s ↦ γab.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ ↦ Path.extend_trans_of_le_half _ _
  have H₂ : (2 : ℝ) • I =ᶠ[𝓝 (2 * t)] I := by
    rw [LinearOrderedField.smul_Icc two_pos, mul_zero, mul_one, ← nhdsWithin_eq_iff_eventuallyEq]
    rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp, notMem_closure_iff_nhdsWithin_eq_bot.mp] <;>
        simp_intro h <;> linarith
    · simp
    · rw [nhdsWithin_eq_nhds.2, nhdsWithin_eq_nhds.2] <;> simp [*] <;> linarith
  rw [curveIntegralFun_def, H₁.self_of_nhds, H₁.derivWithin_eq_of_nhds, curveIntegralFun_def,
    derivWithin_comp_mul_left, ofNat_smul_eq_nsmul, map_nsmul, derivWithin_congr_set H₂]

theorem curveIntegralFun_trans_aeeq_left (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c) :
    curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (0 : ℝ) (1 / 2))]
      fun t ↦ (2 : ℕ) • curveIntegralFun ω γab (2 * t) := by
  rw [uIoc_of_le (by positivity), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact curveIntegralFun_trans_of_lt_half ω γab γbc ht

theorem curveIntegralFun_trans_of_half_lt (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c)
    (ht₀ : 1 / 2 < t) :
    curveIntegralFun ω (γab.trans γbc) t = (2 : ℕ) • curveIntegralFun ω γbc (2 * t - 1) := by
  rw [← (γab.trans γbc).symm_symm, curveIntegralFun_symm_apply, Path.trans_symm,
    curveIntegralFun_trans_of_lt_half (ht := by linarith), curveIntegralFun_symm_apply, smul_neg,
    neg_neg]
  congr 2
  ring

theorem curveIntegralFun_trans_aeeq_right (ω : E → E →L[𝕜] F) (γab : Path a b) (γbc : Path b c) :
    curveIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (1 / 2 : ℝ) 1)]
      fun t ↦ (2 : ℕ) • curveIntegralFun ω γbc (2 * t - 1) := by
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact curveIntegralFun_trans_of_half_lt ω γab γbc ht₁

theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_left
    (h : CurveIntegrable ω γab) (γbc : Path b c) :
    IntervalIntegrable (curveIntegralFun ω (γab.trans γbc)) volume 0 (1 / 2) := by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_left _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using h.comp_mul_left.smul (2 : 𝕜)

theorem CurveIntegrable.intervalIntegrable_curveIntegralFun_trans_right
    (γab : Path a b) (h : CurveIntegrable ω γbc) :
    IntervalIntegrable (curveIntegralFun ω (γab.trans γbc)) volume (1 / 2) 1 := by
  refine .congr_ae ?_ (curveIntegralFun_trans_aeeq_right _ _ _).symm
  simpa [ofNat_smul_eq_nsmul] using h.comp_sub_right 1 |>.comp_mul_left (c := 2) |>.smul (2 : 𝕜)

protected theorem CurveIntegrable.trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
    CurveIntegrable ω (γab.trans γbc) :=
  (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc).trans
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab)

theorem curveIntegral_trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
    ∫ᶜ x in γab.trans γbc, ω x = (∫ᶜ x in γab, ω x) + ∫ᶜ x in γbc, ω x := by
  let instF := NormedSpace.restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def, ← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_curveIntegralFun_trans_left γbc)
    (h₂.intervalIntegrable_curveIntegralFun_trans_right γab),
    intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_left _ _ _),
    intervalIntegral.integral_congr_ae_restrict (curveIntegralFun_trans_aeeq_right _ _ _)]
  simp only [← ofNat_smul_eq_nsmul (R := ℝ)]
  rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left,
    intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_mul_left (f := (curveIntegralFun ω γbc <| · - 1)),
    intervalIntegral.integral_comp_sub_right]
  simp only [curveIntegral_def]
  norm_num

theorem curveIntegralFun_segment [NormedSpace ℝ E] (ω : E → E →L[𝕜] F) (a b : E)
    {t : ℝ} (ht : t ∈ I) : curveIntegralFun ω (.segment a b) t = ω (lineMap a b t) (b - a) := by
  have := Path.eqOn_extend_segment a b
  simp only [curveIntegralFun_def, this ht, derivWithin_congr this (this ht),
    (hasDerivWithinAt_lineMap ..).derivWithin (uniqueDiffOn_Icc_zero_one t ht)]

theorem curveIntegrable_segment [NormedSpace ℝ E] :
    CurveIntegrable ω (.segment a b) ↔
      IntervalIntegrable (fun t ↦ ω (lineMap a b t) (b - a)) volume 0 1 := by
  rw [CurveIntegrable, intervalIntegrable_congr]
  rw [uIoc_of_le zero_le_one]
  exact .mono Ioc_subset_Icc_self fun _t ↦ curveIntegralFun_segment ω a b

theorem curveIntegral_segment [NormedSpace ℝ E] [NormedSpace ℝ F] (ω : E → E →L[𝕜] F) (a b : E) :
    ∫ᶜ x in .segment a b, ω x = ∫ t in 0..1, ω (lineMap a b t) (b - a) := by
  rw [curveIntegral_def]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact curveIntegralFun_segment ω a b ht

@[simp]
theorem curveIntegral_segment_const [NormedSpace ℝ E] [CompleteSpace F] (ω : E →L[𝕜] F) (a b : E) :
    ∫ᶜ _ in .segment a b, ω = ω (b - a) := by
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [curveIntegral_segment]

/-- If `‖ω z‖ ≤ C` at all points of the segment `[a -[ℝ] b]`,
then the curve integral `∫ᶜ x in .segment a b, ω x` has norm at most `C * ‖b - a‖`. -/
theorem norm_curveIntegral_segment_le [NormedSpace ℝ E] {C : ℝ} (h : ∀ z ∈ [a -[ℝ] b], ‖ω z‖ ≤ C) :
    ‖∫ᶜ x in .segment a b, ω x‖ ≤ C * ‖b - a‖ := calc
  ‖∫ᶜ x in .segment a b, ω x‖ ≤ C * ‖b - a‖ * |1 - 0| := by
    letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    rw [curveIntegral_segment]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [segment_eq_image_lineMap] at h
    rw [uIoc_of_le zero_le_one] at ht
    apply_rules [(ω _).le_of_opNorm_le, mem_image_of_mem, Ioc_subset_Icc_self]
  _ = C * ‖b - a‖ := by simp

/-- If a 1-form `ω` is continuous on a set `s`,
then it is curve integrable along any $C^1$ path in this set. -/
theorem ContinuousOn.curveIntegrable_of_contDiffOn [NormedSpace ℝ E] {s : Set E}
    (hω : ContinuousOn ω s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    CurveIntegrable ω γ := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  simp only [funext (curveIntegralFun_def ω γ)]
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ ↦ hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

end PathOperations

/-!
### Algebraic operations on the 1-form
-/

section Algebra

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {a b : E}
  {ω ω₁ ω₂ : E → E →L[𝕜] F} {γ : Path a b} {t : ℝ}

@[simp]
theorem curveIntegralFun_add :
    curveIntegralFun (ω₁ + ω₂) γ = curveIntegralFun ω₁ γ + curveIntegralFun ω₂ γ := by
  ext; simp [curveIntegralFun]

protected theorem CurveIntegrable.add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    CurveIntegrable (ω₁ + ω₂) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.add h₁ h₂

theorem curveIntegral_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ + ω₂) γ = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x := by
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp only [curveIntegral, curveIntegralFun_add]
  exact intervalIntegral.integral_add h₁ h₂

theorem curveIntegral_fun_add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    ∫ᶜ x in γ, (ω₁ x + ω₂ x) = ∫ᶜ x in γ, ω₁ x + ∫ᶜ x in γ, ω₂ x :=
  curveIntegral_add h₁ h₂

@[simp]
theorem curveIntegralFun_zero : curveIntegralFun (0 : E → E →L[𝕜] F) γ = 0 := by
  ext; simp [curveIntegralFun]

@[simp]
theorem curveIntegralFun_fun_zero : curveIntegralFun (fun _ ↦ 0 : E → E →L[𝕜] F) γ = 0 :=
  curveIntegralFun_zero

theorem CurveIntegrable.zero : CurveIntegrable (0 : E → E →L[𝕜] F) γ := by
  simp [CurveIntegrable, IntervalIntegrable.zero]

theorem CurveIntegrable.fun_zero : CurveIntegrable (fun _ ↦ 0 : E → E →L[𝕜] F) γ := .zero

@[simp]
theorem curveIntegral_zero : curveIntegral (0 : E → E →L[𝕜] F) γ = 0 := by simp [curveIntegral]

@[simp]
theorem curveIntegral_fun_zero : ∫ᶜ _ in γ, (0 : E →L[𝕜] F) = 0 := curveIntegral_zero

@[simp]
theorem curveIntegralFun_neg : curveIntegralFun (-ω) γ = -curveIntegralFun ω γ := by
  ext; simp [curveIntegralFun]

theorem CurveIntegrable.neg (h : CurveIntegrable ω γ) : CurveIntegrable (-ω) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.neg h

theorem CurveIntegrable.fun_neg (h : CurveIntegrable ω γ) : CurveIntegrable (-ω ·) γ :=
  h.neg

@[simp]
theorem curveIntegrable_neg_iff : CurveIntegrable (-ω) γ ↔ CurveIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.neg, .neg⟩

@[simp]
theorem curveIntegrable_fun_neg_iff : CurveIntegrable (-ω ·) γ ↔ CurveIntegrable ω γ :=
  curveIntegrable_neg_iff

@[simp]
theorem curveIntegral_neg : curveIntegral (-ω) γ = -∫ᶜ x in γ, ω x := by
  simp [curveIntegral]

@[simp]
theorem curveIntegral_fun_neg : ∫ᶜ x in γ, -ω x = -∫ᶜ x in γ, ω x := curveIntegral_neg

@[simp]
theorem curveIntegralFun_sub :
    curveIntegralFun (ω₁ - ω₂) γ = curveIntegralFun ω₁ γ - curveIntegralFun ω₂ γ := by
  simp [sub_eq_add_neg]

protected theorem CurveIntegrable.sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    CurveIntegrable (ω₁ - ω₂) γ :=
  sub_eq_add_neg ω₁ ω₂ ▸ h₁.add h₂.neg

theorem curveIntegral_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ - ω₂) γ = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, curveIntegral_add h₁ h₂.neg, curveIntegral_neg]

theorem curveIntegral_fun_sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
    ∫ᶜ x in γ, (ω₁ x - ω₂ x) = ∫ᶜ x in γ, ω₁ x - ∫ᶜ x in γ, ω₂ x :=
  curveIntegral_sub h₁ h₂


section RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [NormedSpace 𝕝 E]
  [LinearMap.CompatibleSMul E F 𝕝 𝕜]

@[simp]
theorem curveIntegralFun_restrictScalars :
    curveIntegralFun (fun t ↦ (ω t).restrictScalars 𝕝) γ = curveIntegralFun ω γ := by
  ext
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  simp [curveIntegralFun_def]

@[simp]
theorem curveIntegrable_restrictScalars_iff :
    CurveIntegrable (fun t ↦ (ω t).restrictScalars 𝕝) γ ↔ CurveIntegrable ω γ := by
  simp [CurveIntegrable]

@[simp]
theorem curveIntegral_restrictScalars :
    ∫ᶜ x in γ, (ω x).restrictScalars 𝕝 = ∫ᶜ x in γ, ω x := by
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [curveIntegral_def]

end RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [SMulCommClass 𝕜 𝕝 F] {c : 𝕝}

@[simp]
theorem curveIntegralFun_smul : curveIntegralFun (c • ω) γ = c • curveIntegralFun ω γ := by
  ext
  simp [curveIntegralFun]

theorem CurveIntegrable.smul (h : CurveIntegrable ω γ) :
    CurveIntegrable (c • ω) γ := by
  simpa [CurveIntegrable] using IntervalIntegrable.smul h c

@[simp]
theorem curveIntegrable_smul_iff : CurveIntegrable (c • ω) γ ↔ c = 0 ∨ CurveIntegrable ω γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [CurveIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h ↦ ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]
theorem curveIntegral_smul : curveIntegral (c • ω) γ = c • curveIntegral ω γ := by
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [curveIntegral_def, intervalIntegral.integral_smul]

@[simp]
theorem curveIntegral_fun_smul : ∫ᶜ x in γ, c • ω x = c • ∫ᶜ x in γ, ω x := curveIntegral_smul

end Algebra

section FDeriv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {s : Set E} {ω : E → E →L[𝕜] F}

/-!
### Derivative of the curve integral w.r.t. the right endpoint

In this section we prove that the integral of `ω` along `[a -[ℝ] b]`, as a function of `b`,
has derivative `ω a` at `b = a`.
We provide several versions of this theorem, for `HasFDerivWithinAt` and `HasFDerivAt`,
as well as for continuity near a point and for continuity on the whole set or space.

Note that we take the derivative at the left endpoint of the segment.
Similar facts about the derivative at a different point are true
provided that `ω` is a closed 1-form (formalization WIP, see #24019).
-/

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `ω` is continuous within a convex set `s`
in a neighborhood of `a` within `s`. -/
theorem HasFDerivWithinAt.curveIntegral_segment_source' (hs : Convex ℝ s)
    (hω : ∀ᶠ x in 𝓝[s] a, ContinuousWithinAt ω s x) (ha : a ∈ s) :
    HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω a) s a := by
  /- Given `ε > 0`, take a number `δ > 0` such that `ω` is continuous on `ball a δ ∩ s`
  and `‖ω z - ω a‖ ≤ ε` on this set.
  Then for `b ∈ ball a δ ∩ s`, we have
  `‖(∫ᶜ x in .segment a b, ω x) - ω a (b - a)‖
    = ‖(∫ᶜ x in .segment a b, ω x) - ∫ᶜ x in .segment a b, ω a‖
    ≤ ∫ x in 0..1, ‖ω x - ω a‖ * ‖b - a‖
    ≤ ε * ‖b - a‖`
  -/
  simp only [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO, Path.segment_same,
    curveIntegral_refl, sub_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0,
      ball a δ ∩ s ⊆ {z | ContinuousWithinAt ω s z ∧ dist (ω z) (ω a) ≤ ε} := by
    rw [← Metric.mem_nhdsWithin_iff, setOf_and, inter_mem_iff]
    exact ⟨hω, (hω.self_of_nhdsWithin ha).eventually <| closedBall_mem_nhds _ hε⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have hsub : [a -[ℝ] b] ⊆ ball a δ ∩ s :=
    ((convex_ball _ _).inter hs).segment_subset (by simp [*]) (by simp [*])
  rw [← curveIntegral_segment_const, ← curveIntegral_fun_sub]
  · refine norm_curveIntegral_segment_le fun z hz ↦ (hδ (hsub hz)).2
  · rw [curveIntegrable_segment]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht ↦ ?_
    refine ((hδ ?_).1.eval_const _).comp AffineMap.lineMap_continuous.continuousWithinAt ?_
    · refine hsub <| segment_eq_image_lineMap ℝ a b ▸ mem_image_of_mem _ ht
    · rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      exact hs.segment_subset ha hbs
  · rw [curveIntegrable_segment]
    exact intervalIntegrable_const

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `ω` is continuous on `s`. -/
theorem HasFDerivWithinAt.curveIntegral_segment_source (hs : Convex ℝ s) (hω : ContinuousOn ω s)
    (ha : a ∈ s) : HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω a) s a :=
  .curveIntegral_segment_source' hs (mem_of_superset self_mem_nhdsWithin hω) ha

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivAt` version assuming that `ω` is continuous in a neighborhood of `a`. -/
theorem HasFDerivAt.curveIntegral_segment_source' (hω : ∀ᶠ z in 𝓝 a, ContinuousAt ω z) :
    HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a :=
  HasFDerivWithinAt.curveIntegral_segment_source' convex_univ
    (by simpa only [nhdsWithin_univ, continuousWithinAt_univ]) (mem_univ _) |>.hasFDerivAt_of_univ

/-- The integral of `ω` along `[a -[ℝ] b]`, as a function of `b`, has derivative `ω a` at `b = a`.
This is a `HasFDerivAt` version assuming that `ω` is continuous on the whole space. -/
theorem HasFDerivAt.curveIntegral_segment_source (hω : Continuous ω) :
    HasFDerivAt (∫ᶜ x in .segment a ·, ω x) (ω a) a :=
  .curveIntegral_segment_source' <| .of_forall fun _ ↦ hω.continuousAt

end FDeriv
