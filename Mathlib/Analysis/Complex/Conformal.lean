/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Data.Complex.Module

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `isConformalMap_complex_linear`: a nonzero complex linear map into an arbitrary complex
                                   normed space is conformal.
* `isConformalMap_complex_linear_conj`: the composition of a nonzero complex linear map with
                                        `conj` is complex linear.
* `isConformalMap_iff_is_complex_or_conj_linear`: a real linear map between the complex
                                                  plane is conformal iff it's complex
                                                  linear or the composition of
                                                  some complex linear map and `conj`.

* `DifferentiableAt.conformalAt` states that a real-differentiable function with a nonvanishing
  differential from the complex plane into an arbitrary complex-normed space is conformal at a point
  if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

* `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proves that a real-differential
  function with a nonvanishing differential between the complex plane is conformal at a point if and
  only if it's holomorphic or antiholomorphic at that point.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.

## TODO

* On a connected open set `u`, a function which is `ConformalAt` each point is either holomorphic
  throughout or antiholomorphic throughout.
-/


noncomputable section

open Complex ContinuousLinearMap ComplexConjugate

theorem isConformalMap_conj : IsConformalMap (conjLIE : ℂ →L[ℝ] ℂ) :=
  conjLIE.toLinearIsometry.isConformalMap

section ConformalIntoComplexNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem isConformalMap_complex_linear {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap (map.restrictScalars ℝ) := by
  have minor₁ : ‖map 1‖ ≠ 0 := by
    simpa only [ContinuousLinearMap.ext_ring_iff, Ne, norm_eq_zero] using nonzero
  refine ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • ((map : ℂ →ₗ[ℂ] E) : ℂ →ₗ[ℝ] E), ?_⟩, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply]
    have : x = x • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    nth_rw 1 [this]
    rw [LinearMap.coe_restrictScalars]
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    field_simp only [one_mul]
  · ext1
    simp [minor₁]

theorem isConformalMap_complex_linear_conj {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap ((map.restrictScalars ℝ).comp (conjCLE : ℂ →L[ℝ] ℂ)) :=
  (isConformalMap_complex_linear nonzero).comp isConformalMap_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {g : ℂ →L[ℝ] ℂ}

theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
    (∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
      ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCLE := by
  rcases h with ⟨c, -, li, rfl⟩
  obtain ⟨li, rfl⟩ : ∃ li' : ℂ ≃ₗᵢ[ℝ] ℂ, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine Or.inl ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext1
    simp
  · refine Or.inr ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext1
    simp

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
theorem isConformalMap_iff_is_complex_or_conj_linear :
    IsConformalMap g ↔
      ((∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
          ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCLE) ∧
        g ≠ 0 := by
  constructor
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.ne_zero⟩
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    · refine isConformalMap_complex_linear ?_
      contrapose! h₂ with w
      simp only [w, restrictScalars_zero]
    · have minor₁ : g = map.restrictScalars ℝ ∘L ↑conjCLE := by
        ext1
        simp only [hmap, coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          conjCLE_apply, starRingEnd_self_apply]
      rw [minor₁] at h₂ ⊢
      refine isConformalMap_complex_linear_conj ?_
      contrapose! h₂ with w
      simp only [w, restrictScalars_zero, zero_comp]

end ConformalIntoComplexPlane

/-! ### Conformality of real-differentiable complex maps -/

section Conformality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : ℂ} {f : ℂ → E}

/-- A real differentiable function of the complex plane into some complex normed space `E` is
conformal at a point `z` if it is holomorphic at that point with a nonvanishing differential.
This is a version of the Cauchy-Riemann equations. -/
theorem DifferentiableAt.conformalAt (h : DifferentiableAt ℂ f z) (hf' : deriv f z ≠ 0) :
    ConformalAt f z := by
  rw [conformalAt_iff_isConformalMap_fderiv, (h.hasFDerivAt.restrictScalars ℝ).fderiv]
  apply isConformalMap_complex_linear
  simpa only [Ne, ContinuousLinearMap.ext_ring_iff]

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
with a nonvanishing differential. -/
theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj {f : ℂ → ℂ} {z : ℂ} :
    ConformalAt f z ↔
      (DifferentiableAt ℂ f z ∨ DifferentiableAt ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 := by
  rw [conformalAt_iff_isConformalMap_fderiv]
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  apply or_congr
  · rw [differentiableAt_iff_restrictScalars ℝ h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiableAt_iff_restrictScalars ℝ (h_diff.comp _ conjCLE.differentiableAt)]
  refine exists_congr fun g => rfl.congr ?_
  have : fderiv ℝ conj (conj z) = _ := conjCLE.fderiv
  simp [fderiv_comp _ h_diff conjCLE.differentiableAt, this]

end Conformality

/-!
### The Cauchy-Riemann Equation for Complex-Differentiable Functions
-/

/--
Helper lemma for `differentiableAt_complex_iff_differentiableAt_real`: A real linear map
`ℓ : ℂ →ₗ[ℝ] ℂ` respects complex scalar multiplication if it maps `I` to `I • ℓ 1`.
-/
theorem real_linearMap_map_smul_complex {ℓ : ℂ →ₗ[ℝ] ℂ} (h : ℓ I = I • ℓ 1) :
    ∀ (a b : ℂ), ℓ (a • b) = a • ℓ b := by
  intro a b
  rw [(by simp only [real_smul, re_add_im] : a = a.re + a.im • I), (by simp : b = b.re + b.im • I)]
  repeat rw [add_smul]
  repeat rw [smul_add]
  repeat rw [ℓ.map_add]
  have t₀ : (a.im • I) • ↑b.re = (a.im * b.re) • I := by
    simp
    ring
  have t₁ : (a.im • I) • b.im • I = -(a.im * b.im) • (1 : ℂ) := by
    simp [(by ring : ↑a.im * I * (↑b.im * I) = (↑a.im * ↑b.im) * (I * I))]
  rw [t₀, t₁, (by simp : b.re = b.re • (1 : ℂ))]
  repeat rw [Complex.coe_smul]
  repeat rw [ℓ.map_smul]
  repeat rw [← Complex.coe_smul]
  repeat rw [h]
  simp only [smul_eq_mul, ofReal_mul, ofReal_neg, neg_mul]
  ring_nf
  rw [I_sq]
  ring

/--
The Cauchy-Riemann Equation: A real-differentiable function `f : ℂ → ℂ` is complex differentiable if
the derivative `fderiv ℝ f x` maps `I` to I • (fderiv ℝ f x) 1`.
-/
theorem differentiableAt_complex_iff_differentiableAt_real {f : ℂ → ℂ} {x : ℂ} :
    (DifferentiableAt ℂ f x) ↔ (DifferentiableAt ℝ f x) ∧
      (fderiv ℝ f x I = I • fderiv ℝ f x 1) := by
  constructor
  · exact fun h ↦ by simp [h.restrictScalars ℝ, h.fderiv_restrictScalars ℝ]
  · intro ⟨h₁, h₂⟩
    apply (differentiableAt_iff_restrictScalars ℝ h₁).2
    use {
      toFun := fderiv ℝ f x
      map_add' := (fderiv ℝ f x).map_add'
      map_smul' := real_linearMap_map_smul_complex h₂
    }
    rfl
