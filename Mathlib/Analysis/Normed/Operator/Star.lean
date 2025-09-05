/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! `star` as a linear isometry -/

section starₗᵢ

variable {𝕜 E : Type*}
variable [CommSemiring 𝕜] [StarRing 𝕜]
variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
variable [Module 𝕜 E] [StarModule 𝕜 E]

variable (𝕜) in
/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }

@[simp]
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star :=
  rfl

theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl

@[simp]
theorem starₗᵢ_toContinuousLinearEquiv :
    (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toContinuousLinearEquiv = (starL 𝕜 : E ≃L⋆[𝕜] E) :=
  ContinuousLinearEquiv.ext rfl

end starₗᵢ
