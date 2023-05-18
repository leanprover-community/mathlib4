/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.completion
! leanprover-community/mathlib commit d3af0609f6db8691dffdc3e1fb7feb7da72698f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Completion
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Topology.Algebra.UniformRing

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `uniform_space.completion E`. In this file we provide
necessary instances and define `uniform_space.completion.to_complₗᵢ` - coercion
`E → uniform_space.completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `uniform_space.completion A`.

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type _) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance (priority := 100) NormedSpace.to_uniformContinuousConstSMul :
    UniformContinuousConstSMul 𝕜 E :=
  ⟨fun c => (lipschitzWith_smul c).UniformContinuous⟩
#align uniform_space.completion.normed_space.to_has_uniform_continuous_const_smul UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul

instance : NormedSpace 𝕜 (Completion E) :=
  { Completion.module with
    smul := (· • ·)
    norm_smul_le := fun c x =>
      induction_on x
        (isClosed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm)) fun y =>
        by simp only [← coe_smul, norm_coe, norm_smul] }

variable {𝕜 E}

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := coe
    map_smul' := coe_smul
    norm_map' := norm_coe }
#align uniform_space.completion.to_complₗᵢ UniformSpace.Completion.toComplₗᵢ

@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = coe :=
  rfl
#align uniform_space.completion.coe_to_complₗᵢ UniformSpace.Completion.coe_toComplₗᵢ

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap
#align uniform_space.completion.to_complL UniformSpace.Completion.toComplL

@[simp]
theorem coe_toComplL : ⇑(toComplL : E →L[𝕜] Completion E) = coe :=
  rfl
#align uniform_space.completion.coe_to_complL UniformSpace.Completion.coe_toComplL

@[simp]
theorem norm_toComplL {𝕜 E : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap
#align uniform_space.completion.norm_to_complL UniformSpace.Completion.norm_toComplL

section Algebra

variable (𝕜) (A : Type _)

instance [SeminormedRing A] : NormedRing (Completion A) :=
  { Completion.ring,
    Completion.metricSpace with
    dist_eq := fun x y => by
      apply completion.induction_on₂ x y <;> clear x y
      · refine' isClosed_eq (completion.uniform_continuous_extension₂ _).Continuous _
        exact Continuous.comp completion.continuous_extension continuous_sub
      · intro x y
        rw [← completion.coe_sub, norm_coe, completion.dist_eq, dist_eq_norm]
    norm_mul := fun x y => by
      apply completion.induction_on₂ x y <;> clear x y
      ·
        exact
          isClosed_le (Continuous.comp continuous_norm continuous_mul)
            (Continuous.comp Real.continuous_mul
              (Continuous.prod_map continuous_norm continuous_norm))
      · intro x y
        simp only [← coe_mul, norm_coe]
        exact norm_mul_le x y }

instance [SeminormedCommRing A] [NormedAlgebra 𝕜 A] [UniformContinuousConstSMul 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) :=
  { Completion.algebra A 𝕜 with
    norm_smul_le := fun r x =>
      by
      apply completion.induction_on x <;> clear x
      ·
        exact
          isClosed_le (Continuous.comp continuous_norm (continuous_const_smul r))
            (Continuous.comp (continuous_mul_left _) continuous_norm)
      · intro x
        simp only [← coe_smul, norm_coe]
        exact norm_smul_le r x }

end Algebra

end Completion

end UniformSpace

