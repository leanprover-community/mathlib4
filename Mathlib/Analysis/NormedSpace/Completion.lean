/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.UniformRing

#align_import analysis.normed_space.completion from "leanprover-community/mathlib"@"d3af0609f6db8691dffdc3e1fb7feb7da72698f2"

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

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance (priority := 100) NormedSpace.to_uniformContinuousConstSMul :
    UniformContinuousConstSMul 𝕜 E :=
  ⟨fun c => (lipschitzWith_smul c).uniformContinuous⟩
#align uniform_space.completion.normed_space.to_has_uniform_continuous_const_smul UniformSpace.Completion.NormedSpace.to_uniformContinuousConstSMul

instance : NormedSpace 𝕜 (Completion E) :=
  { Completion.instModule with
    smul := (· • ·)
    norm_smul_le := fun c x =>
      induction_on x
        (isClosed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm)) fun y =>
        by simp only [← coe_smul, norm_coe, norm_smul, le_rfl] }
           -- 🎉 no goals

variable {𝕜 E}

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }
#align uniform_space.completion.to_complₗᵢ UniformSpace.Completion.toComplₗᵢ

@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl
#align uniform_space.completion.coe_to_complₗᵢ UniformSpace.Completion.coe_toComplₗᵢ

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap
set_option linter.uppercaseLean3 false in
#align uniform_space.completion.to_complL UniformSpace.Completion.toComplL

@[simp]
theorem coe_toComplL : ⇑(toComplL : E →L[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl
set_option linter.uppercaseLean3 false in
#align uniform_space.completion.coe_to_complL UniformSpace.Completion.coe_toComplL

@[simp]
theorem norm_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap
set_option linter.uppercaseLean3 false in
#align uniform_space.completion.norm_to_complL UniformSpace.Completion.norm_toComplL

section Algebra

variable (𝕜) (A : Type*)

instance [SeminormedRing A] : NormedRing (Completion A) :=
  { Completion.ring,
    Completion.instMetricSpace with
    dist_eq := fun x y => by
      refine Completion.induction_on₂ x y ?_ ?_ <;> clear x y
      -- ⊢ IsClosed {x | dist x.fst x.snd = ‖x.fst - x.snd‖}
                                                    -- ⊢ IsClosed {x | dist x.fst x.snd = ‖x.fst - x.snd‖}
                                                    -- ⊢ ∀ (a b : A), dist (↑A a) (↑A b) = ‖↑A a - ↑A b‖
      · refine' isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous _
        -- ⊢ Continuous fun x => ‖x.fst - x.snd‖
        exact Continuous.comp Completion.continuous_extension continuous_sub
        -- 🎉 no goals
      · intro x y
        -- ⊢ dist (↑A x) (↑A y) = ‖↑A x - ↑A y‖
        rw [← Completion.coe_sub, norm_coe, Completion.dist_eq, dist_eq_norm]
        -- 🎉 no goals
    norm_mul := fun x y => by
      refine Completion.induction_on₂ x y ?_ ?_ <;> clear x y
      -- ⊢ IsClosed {x | ‖x.fst * x.snd‖ ≤ ‖x.fst‖ * ‖x.snd‖}
                                                    -- ⊢ IsClosed {x | ‖x.fst * x.snd‖ ≤ ‖x.fst‖ * ‖x.snd‖}
                                                    -- ⊢ ∀ (a b : A), ‖↑A a * ↑A b‖ ≤ ‖↑A a‖ * ‖↑A b‖
      · exact
          isClosed_le (Continuous.comp continuous_norm continuous_mul)
            (Continuous.comp _root_.continuous_mul
              (Continuous.prod_map continuous_norm continuous_norm))
      · intro x y
        -- ⊢ ‖↑A x * ↑A y‖ ≤ ‖↑A x‖ * ‖↑A y‖
        simp only [← coe_mul, norm_coe]
        -- ⊢ ‖x * y‖ ≤ ‖x‖ * ‖y‖
        exact norm_mul_le x y }
        -- 🎉 no goals

instance [SeminormedCommRing A] [NormedAlgebra 𝕜 A] [UniformContinuousConstSMul 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) :=
  { Completion.algebra A 𝕜 with
    norm_smul_le := fun r x => by
      refine Completion.induction_on x ?_ ?_ <;> clear x
      -- ⊢ IsClosed {a | ‖r • a‖ ≤ ‖r‖ * ‖a‖}
                                                 -- ⊢ IsClosed {a | ‖r • a‖ ≤ ‖r‖ * ‖a‖}
                                                 -- ⊢ ∀ (a : A), ‖r • ↑A a‖ ≤ ‖r‖ * ‖↑A a‖
      · exact
          isClosed_le (Continuous.comp continuous_norm (continuous_const_smul r))
            (Continuous.comp (continuous_mul_left _) continuous_norm)
      · intro x
        -- ⊢ ‖r • ↑A x‖ ≤ ‖r‖ * ‖↑A x‖
        simp only [← coe_smul, norm_coe]
        -- ⊢ ‖r • x‖ ≤ ‖r‖ * ‖x‖
        exact norm_smul_le r x }
        -- 🎉 no goals

end Algebra

end Completion

end UniformSpace
