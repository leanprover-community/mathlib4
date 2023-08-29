/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.NormedSpace.ConformalLinearMap
import Mathlib.Analysis.NormedSpace.FiniteDimension

#align_import analysis.complex.conformal from "leanprover-community/mathlib"@"468b141b14016d54b479eb7a0fff1e360b7e3cf6"

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

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/


noncomputable section

open Complex ContinuousLinearMap ComplexConjugate

theorem isConformalMap_conj : IsConformalMap (conjLie : ℂ →L[ℝ] ℂ) :=
  conjLie.toLinearIsometry.isConformalMap
#align is_conformal_map_conj isConformalMap_conj

section ConformalIntoComplexNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] {z : ℂ}
  {g : ℂ →L[ℝ] E} {f : ℂ → E}

theorem isConformalMap_complex_linear {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap (map.restrictScalars ℝ) := by
  have minor₁ : ‖map 1‖ ≠ 0 := by simpa only [ext_ring_iff, Ne.def, norm_eq_zero] using nonzero
  -- ⊢ IsConformalMap (restrictScalars ℝ map)
  refine' ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • ((map : ℂ →ₗ[ℂ] E) : ℂ →ₗ[ℝ] E), _⟩, _⟩
  -- ⊢ ∀ (x : ℂ), ‖↑(‖↑map 1‖⁻¹ • ↑ℝ ↑map) x‖ = ‖x‖
  · intro x
    -- ⊢ ‖↑(‖↑map 1‖⁻¹ • ↑ℝ ↑map) x‖ = ‖x‖
    simp only [LinearMap.smul_apply]
    -- ⊢ ‖‖↑map 1‖⁻¹ • ↑(↑ℝ ↑map) x‖ = ‖x‖
    have : x = x • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    -- ⊢ ‖‖↑map 1‖⁻¹ • ↑(↑ℝ ↑map) x‖ = ‖x‖
    nth_rw 1 [this]
    -- ⊢ ‖‖↑map 1‖⁻¹ • ↑(↑ℝ ↑map) (x • 1)‖ = ‖x‖
    rw [LinearMap.coe_restrictScalars]
    -- ⊢ ‖‖↑map 1‖⁻¹ • ↑↑map (x • 1)‖ = ‖x‖
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    -- ⊢ ‖↑map 1‖⁻¹ * (‖x‖ * ‖↑map 1‖) = ‖x‖
    field_simp only [one_mul]
    -- 🎉 no goals
  · ext1
    -- ⊢ ↑(restrictScalars ℝ map) x✝ = ↑(‖↑map 1‖ • LinearIsometry.toContinuousLinear …
    -- Porting note: was simp
    rw [coe_restrictScalars', coe_smul', LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.coe_mk, Pi.smul_apply, LinearMap.smul_apply, LinearMap.coe_restrictScalars,
      coe_coe, smul_inv_smul₀ minor₁]
#align is_conformal_map_complex_linear isConformalMap_complex_linear

theorem isConformalMap_complex_linear_conj {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap ((map.restrictScalars ℝ).comp (conjCle : ℂ →L[ℝ] ℂ)) :=
  (isConformalMap_complex_linear nonzero).comp isConformalMap_conj
#align is_conformal_map_complex_linear_conj isConformalMap_complex_linear_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
    (∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
      ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCle := by
  rcases h with ⟨c, -, li, rfl⟩
  -- ⊢ (∃ map, restrictScalars ℝ map = c • LinearIsometry.toContinuousLinearMap li) …
  obtain ⟨li, rfl⟩ : ∃ li' : ℂ ≃ₗᵢ[ℝ] ℂ, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- ⊢ (∃ map, restrictScalars ℝ map = c • LinearIsometry.toContinuousLinearMap (Li …
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine' Or.inl ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, _⟩
    -- ⊢ restrictScalars ℝ (c • ↑a • ContinuousLinearMap.id ℂ ℂ) = c • LinearIsometry …
    ext1
    -- ⊢ ↑(restrictScalars ℝ (c • ↑a • ContinuousLinearMap.id ℂ ℂ)) x✝ = ↑(c • Linear …
    -- Porting note: was simp
    rw [coe_restrictScalars', smul_apply, smul_apply, smul_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, rotation_apply, id_apply, smul_eq_mul]
  · refine' Or.inr ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, _⟩
    -- ⊢ restrictScalars ℝ (c • ↑a • ContinuousLinearMap.id ℂ ℂ) = ContinuousLinearMa …
    ext1
    -- ⊢ ↑(restrictScalars ℝ (c • ↑a • ContinuousLinearMap.id ℂ ℂ)) x✝ = ↑(Continuous …
    -- Porting note: was simp
    rw [coe_restrictScalars', smul_apply, smul_apply, comp_apply, smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.trans_apply, rotation_apply, id_apply, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe, conjCle_apply, conjLie_apply, conj_conj]
#align is_conformal_map.is_complex_or_conj_linear IsConformalMap.is_complex_or_conj_linear

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
theorem isConformalMap_iff_is_complex_or_conj_linear :
    IsConformalMap g ↔
      ((∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
          ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCle) ∧
        g ≠ 0 := by
  constructor
  -- ⊢ IsConformalMap g → ((∃ map, restrictScalars ℝ map = g) ∨ ∃ map, restrictScal …
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.ne_zero⟩
    -- 🎉 no goals
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    -- ⊢ IsConformalMap (restrictScalars ℝ map)
    · refine' isConformalMap_complex_linear _
      -- ⊢ map ≠ 0
      contrapose! h₂ with w
      -- ⊢ restrictScalars ℝ map = 0
      simp only [w, restrictScalars_zero]
      -- 🎉 no goals
    · have minor₁ : g = map.restrictScalars ℝ ∘L ↑conjCle := by
        ext1
        simp only [hmap, coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          conjCle_apply, starRingEnd_self_apply]
      rw [minor₁] at h₂ ⊢
      -- ⊢ IsConformalMap (comp (restrictScalars ℝ map) ↑conjCle)
      refine' isConformalMap_complex_linear_conj _
      -- ⊢ map ≠ 0
      contrapose! h₂ with w
      -- ⊢ comp (restrictScalars ℝ map) ↑conjCle = 0
      simp only [w, restrictScalars_zero, zero_comp]
      -- 🎉 no goals
#align is_conformal_map_iff_is_complex_or_conj_linear isConformalMap_iff_is_complex_or_conj_linear

end ConformalIntoComplexPlane
