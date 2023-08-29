/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.NormedSpace.ConformalLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic

#align_import analysis.inner_product_space.conformal_linear_map from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Conformal maps between inner product spaces

In an inner product space, a map is conformal iff it preserves inner products up to a scalar factor.
-/


variable {E F : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open LinearIsometry ContinuousLinearMap

open RealInnerProductSpace

/-- A map between two inner product spaces is a conformal map if and only if it preserves inner
products up to a scalar factor, i.e., there exists a positive `c : ℝ` such that
`⟪f u, f v⟫ = c * ⟪u, v⟫` for all `u`, `v`. -/
theorem isConformalMap_iff (f : E →L[ℝ] F) :
    IsConformalMap f ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪f u, f v⟫ = c * ⟪u, v⟫ := by
  constructor
  -- ⊢ IsConformalMap f → ∃ c, 0 < c ∧ ∀ (u v : E), inner (↑f u) (↑f v) = c * inner …
  · rintro ⟨c₁, hc₁, li, rfl⟩
    -- ⊢ ∃ c, 0 < c ∧ ∀ (u v : E), inner (↑(c₁ • toContinuousLinearMap li) u) (↑(c₁ • …
    refine' ⟨c₁ * c₁, mul_self_pos.2 hc₁, fun u v => _⟩
    -- ⊢ inner (↑(c₁ • toContinuousLinearMap li) u) (↑(c₁ • toContinuousLinearMap li) …
    simp only [real_inner_smul_left, real_inner_smul_right, mul_assoc, coe_smul',
      coe_toContinuousLinearMap, Pi.smul_apply, inner_map_map]
  · rintro ⟨c₁, hc₁, huv⟩
    -- ⊢ IsConformalMap f
    obtain ⟨c, hc, rfl⟩ : ∃ c : ℝ, 0 < c ∧ c₁ = c * c
    -- ⊢ ∃ c, 0 < c ∧ c₁ = c * c
    exact ⟨Real.sqrt c₁, Real.sqrt_pos.2 hc₁, (Real.mul_self_sqrt hc₁.le).symm⟩
    -- ⊢ IsConformalMap f
    refine' ⟨c, hc.ne', (c⁻¹ • f : E →ₗ[ℝ] F).isometryOfInner fun u v => _, _⟩
    -- ⊢ inner (↑↑(c⁻¹ • f) u) (↑↑(c⁻¹ • f) v) = inner u v
    · simp only [real_inner_smul_left, real_inner_smul_right, huv, mul_assoc, coe_smul,
        inv_mul_cancel_left₀ hc.ne', LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
    · ext1 x
      -- ⊢ ↑f x = ↑(c • toContinuousLinearMap (LinearMap.isometryOfInner ↑(c⁻¹ • f) (_  …
      exact (smul_inv_smul₀ hc.ne' (f x)).symm
      -- 🎉 no goals
#align is_conformal_map_iff isConformalMap_iff
