/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The span of a single vector

The equivalence of `𝕜` and `𝕜 • x` for `x ≠ 0` are defined as continuous linear equivalence and
isometry.

## Main definitions

* `ContinuousLinearEquiv.toSpanNonzeroSingleton`: The continuous linear equivalence between `𝕜` and
  `𝕜 • x` for `x ≠ 0`.
* `LinearIsometryEquiv.toSpanUnitSingleton`: For `‖x‖ = 1` the continuous linear equivalence is a
  linear isometry equivalence.

-/

variable {𝕜 E : Type*}

namespace LinearMap

variable (𝕜)

section Seminormed

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

theorem toSpanSingleton_homothety (x : E) (c : 𝕜) :
    ‖LinearMap.toSpanSingleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ := by
  rw [mul_comm]
  exact norm_smul _ _

end Seminormed

end LinearMap

namespace ContinuousLinearEquiv

variable (𝕜)

section Seminormed
variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

theorem _root_.LinearEquiv.toSpanNonzeroSingleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
    ‖LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
  LinearMap.toSpanSingleton_homothety _ _ _

end Seminormed

section Normed
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
continuous linear equivalence from `𝕜` to the span of `x`. -/
@[simps!]
noncomputable def toSpanNonzeroSingleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
  ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
linear map from the span of `x` to `𝕜`. -/
noncomputable def coord (x : E) (h : x ≠ 0) : StrongDual 𝕜 (𝕜 ∙ x) :=
  (toSpanNonzeroSingleton 𝕜 x h).symm

@[simp]
theorem coe_toSpanNonzeroSingleton_symm {x : E} (h : x ≠ 0) :
    ⇑(toSpanNonzeroSingleton 𝕜 x h).symm = coord 𝕜 x h :=
  rfl

@[simp]
theorem coord_toSpanNonzeroSingleton {x : E} (h : x ≠ 0) (c : 𝕜) :
    coord 𝕜 x h (toSpanNonzeroSingleton 𝕜 x h c) = c :=
  (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c

@[simp]
theorem toSpanNonzeroSingleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
    toSpanNonzeroSingleton 𝕜 x h (coord 𝕜 x h y) = y :=
  (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y

@[simp]
theorem coord_self (x : E) (h : x ≠ 0) :
    (coord 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
  LinearEquiv.coord_self 𝕜 E x h

end Normed

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- Given a unit element `x` of a normed space `E` over a field `𝕜`, the natural
linear isometry equivalence from `𝕜` to the span of `x`. -/
noncomputable def toSpanUnitSingleton (x : E) (hx : ‖x‖ = 1) :
    𝕜 ≃ₗᵢ[𝕜] 𝕜 ∙ x where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)
  norm_map' := by
    intro
    rw [LinearEquiv.toSpanNonzeroSingleton_homothety, hx, one_mul]

@[simp] theorem toSpanUnitSingleton_apply (x : E) (hx : ‖x‖ = 1) (r : 𝕜) :
    toSpanUnitSingleton x hx r = (⟨r • x, by aesop⟩ : 𝕜 ∙ x) := rfl

end LinearIsometryEquiv
