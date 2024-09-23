/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.UniformField

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `UniformSpace.Completion E`. In this file we provide
necessary instances and define `UniformSpace.Completion.toComplₗᵢ` - coercion
`E → UniformSpace.Completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `UniformSpace.Completion A`.

TODO: Generalise the results here from the concrete `completion` to any `AbstractCompletion`.
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type*)

instance [Zero 𝕜] [Zero E] [SMul 𝕜 E] [PseudoMetricSpace 𝕜] [PseudoMetricSpace E]
    [BoundedSMul 𝕜 E] : BoundedSMul 𝕜 (Completion E) where
  dist_smul_pair' c x₁ x₂ := by
    induction x₁, x₂ using induction_on₂ with
    | hp =>
      exact isClosed_le
        ((continuous_fst.const_smul _).dist (continuous_snd.const_smul _))
        (continuous_const.mul (continuous_fst.dist continuous_snd))
    | ih x₁ x₂ =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq,  Completion.dist_eq]
      exact dist_smul_pair c x₁ x₂
  dist_pair_smul' c₁ c₂ x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_le
        ((continuous_const_smul _).dist (continuous_const_smul _))
        (continuous_const.mul (continuous_id.dist continuous_const))
    | ih x =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq, ← coe_zero, Completion.dist_eq]
      exact dist_pair_smul c₁ c₂ x

instance [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedSpace 𝕜 (Completion E) where
  norm_smul_le := norm_smul_le

section Module

variable {𝕜 E}
variable [Semiring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [UniformContinuousConstSMul 𝕜 E]

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }

@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap

@[simp]
theorem coe_toComplL : ⇑(toComplL : E →L[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

@[simp]
theorem norm_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

end Module

section Algebra

variable (A : Type*)

instance [SeminormedRing A] : NormedRing (Completion A) where
  __ : NormedAddCommGroup (Completion A) := inferInstance
  __ : Ring (Completion A) := inferInstance
  norm_mul x y := by
    induction x, y using induction_on₂ with
    | hp =>
      exact
        isClosed_le (Continuous.comp continuous_norm continuous_mul)
          (Continuous.comp _root_.continuous_mul
            (Continuous.prod_map continuous_norm continuous_norm))
    | ih x y =>
      simp only [← coe_mul, norm_coe]
      exact norm_mul_le x y

instance [SeminormedCommRing A] : NormedCommRing (Completion A) where
  __ : CommRing (Completion A) := inferInstance
  __ : NormedRing (Completion A) := inferInstance

instance
    [NormedField 𝕜] [SeminormedCommRing A] [NormedAlgebra 𝕜 A] [UniformContinuousConstSMul 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) where
  norm_smul_le := norm_smul_le

instance [NormedField A] [CompletableTopField A] :
    NormedField (UniformSpace.Completion A) where
  __ : NormedCommRing (Completion A) := inferInstance
  __ : Field (Completion A) := inferInstance
  norm_mul' x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])

end Algebra

end Completion

end UniformSpace
