/-
Copyright (c) 2025 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Integration of bounded continuous functions against finite measures and locally integrable maps

In this file, some specialized definitions are introduced for bundling properties of integrals of
bounded continuous functions against finite measures and locally integrable maps.
They are meant to be used as intermediate constructions for the development of distribution theory.

## Main definitions

- `FiniteMeasure.testAgainstCLM` wraps the integral with respect to a finite measure
  as a continuous linear map on bounded continuous functions.
- `LocallyIntegrable.testAgainstCLM` wraps the integral against a locally integrable function as
  as a continuous linear map on bounded continuous functions.
-/

open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section BochnerIntegral

variable {X : Type*} {mX : MeasurableSpace X} [TopologicalSpace X] [OpensMeasurableSpace X]
variable (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E]
  [BorelSpace E] [NormedSpace ℝ E]

namespace FiniteMeasure

/-- `FiniteMeasure.testAgainstₗ` wraps the integral with respect to a finite measure `μ`
as a `𝕜`-linear map on bounded continuous functions. -/
noncomputable def testAgainstₗ (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [IsFiniteMeasure μ] :
    (X →ᵇ E) →ₗ[𝕜] E where
  toFun := (∫ x, · x ∂μ)
  map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
  map_smul' c f := integral_smul c f

/-- `FiniteMeasure.testAgainstCLM` wraps the integral with respect to a finite measure `μ`
as a continuous `𝕜`-linear map on bounded continuous functions. -/
noncomputable def testAgainstCLM (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [IsFiniteMeasure μ] :
    (X →ᵇ E) →L[𝕜] E :=
  (testAgainstₗ μ 𝕜).mkContinuous (μ.real Set.univ) (fun f ↦ f.norm_integral_le_mul_norm μ)

end FiniteMeasure

namespace LocallyIntegrable

variable {𝕜 : Type*} [NormedField 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
variable [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

open TopologicalSpace

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
theorem integrable_smul_LocallyIntegrable {f : X → E} (hf : LocallyIntegrable f μ) (K : Compacts X)
    (φ : X →ᵇ 𝕜) :
    Integrable (fun x ↦ (φ x) • (f x)) (μ.restrict K) :=
  ((hf.locallyIntegrableOn K).continuousOn_smul K.isCompact.isClosed.isLocallyClosed
      φ.continuous.continuousOn).integrableOn_isCompact K.isCompact

variable [SMulCommClass ℝ 𝕜 E]

variable (𝕜) {μ}

/-- `LocallyIntegrable.testAgainstₗ` wraps the integral against a locally integrable function `f` on
a fixed compact `K` as a `𝕜`-linear map on scalar valued bounded continuous functions. -/
noncomputable def testAgainstₗ {f : X → E} (hf : LocallyIntegrable f μ) (K : Compacts X) :
    (X →ᵇ 𝕜) →ₗ[𝕜] E where
  toFun φ := ∫ x, φ x • f x ∂(μ.restrict K)
  map_add' φ Φ:= by
    simp_rw [add_apply, add_smul, integral_add (integrable_smul_LocallyIntegrable μ hf K φ)
      (integrable_smul_LocallyIntegrable μ hf K Φ)]
  map_smul' c φ := by
    simp_rw [coe_smul, RingHom.id_apply, ← integral_smul c (fun x ↦ φ x • f x), smul_assoc]

/-- `LocallyIntegrable.testAgainstCLM` wraps the integral against a locally integrable
function `f` on a fixed compact `K` as a continuous `𝕜`-linear map on scalar valued bounded
continuous functions. -/
noncomputable def testAgainstCLM {f : X → E} (hf : LocallyIntegrable f μ) (K : Compacts X) :
    (X →ᵇ 𝕜) →L[𝕜] E :=
  (testAgainstₗ 𝕜 hf K).mkContinuous (∫ x, ‖f x‖ ∂(μ.restrict K))
  (by
    intro φ
    have h : ∀ᵐ x ∂(μ.restrict K), ‖φ x • f x‖ ≤ ‖φ‖ * ‖f x‖ :=
      (ae_of_all _ fun x ↦ by grw [norm_smul, norm_coe_le_norm])
    apply le_trans (norm_integral_le_of_norm_le
      ((hf.integrableOn_isCompact K.isCompact).norm.const_mul _) h)
    rw [mul_comm, integral_const_mul_of_integrable (hf.integrableOn_isCompact K.isCompact).norm]
  )

end LocallyIntegrable

end BochnerIntegral

end BoundedContinuousFunction
