/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Integration of bounded continuous functions

In this file, some results are collected about integrals of bounded continuous functions. They are
mostly specializations of results in general integration theory, but they are used directly in this
specialized form in some other files, in particular in those related to the topology of weak
convergence of probability measures and finite measures.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section BochnerIntegral

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E]

variable [OpensMeasurableSpace X] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℝ E]

namespace FiniteMeasure

/-- `integralFiniteMeasureₗ` wraps the integral with respect to a finite measure `μ`
as a `𝕜`-linear map on bounded continuous functions -/
noncomputable def testAgainstₗ (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] [IsFiniteMeasure μ] :
    (X →ᵇ E) →ₗ[𝕜] E where
  toFun := (∫ x, · x ∂μ)
  map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
  map_smul' c f := integral_smul c f

/-- `integralFiniteMeasureCLM` wraps the integral with respect to a finite measure `μ`
as a continuous `𝕜`-linear map on bounded continuous functions -/
noncomputable def testAgainstCLM (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] [IsFiniteMeasure μ] :
    (X →ᵇ E) →L[𝕜] E :=
  (testAgainstₗ μ 𝕜).mkContinuous (measureUnivNNReal μ)
    (fun f ↦ le_trans (f.norm_integral_le_mul_norm _) le_rfl)

variable {𝕜 : Type*} [NormedField 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
variable [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

end FiniteMeasure

namespace LocallyIntegrable

open TopologicalSpace LocallyIntegrableOn

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
theorem integrable_smul_LocallyIntegrable {f : X → E} (hf : LocallyIntegrable f μ)
  (K : Compacts X) (φ : X →ᵇ 𝕜) :
    Integrable (fun x ↦ (φ x) • (f x)) (μ.restrict K) := by
  refine integrableOn_isCompact ?_ K.isCompact
  exact LocallyIntegrableOn.continuousOn_smul K.isCompact.isClosed.isLocallyClosed
    (hf.locallyIntegrableOn K) φ.continuous.continuousOn

variable [SMulCommClass ℝ 𝕜 E]

variable (𝕜) {μ}

/-- `testAgainstLocallyIntegrableₗ` wraps the integral against a locally  integrable function `f` on
a fixed compact `K` as a `𝕜`-linear map on scalar valued bounded continuous functions -/
noncomputable def testAgainsₗ {f : X → E} (hf : LocallyIntegrable f μ)
  (K : Compacts X) :
    (X →ᵇ 𝕜) →ₗ[𝕜] E where
  toFun := fun φ : (X →ᵇ 𝕜) ↦ ∫ (x : X), φ x • f x ∂(μ.restrict K)
  map_add' := by
    intro φ Φ
    simp_rw [add_apply, add_smul, integral_add (integrable_smul_LocallyIntegrable μ hf K φ)
      (integrable_smul_LocallyIntegrable μ hf K Φ)]
  map_smul' := by
    intro c φ
    simp_rw [coe_smul, RingHom.id_apply, ← integral_smul c (fun (x : X) ↦  φ x • f x), smul_assoc]

/-- `testAgainstLocallyIntegrableₗ` wraps the integral against a locally  integrable function `f` on
a fixed compact `K` as a continuous `𝕜`-linear map on scalar valued bounded continuous functions -/
noncomputable def testAgainstCLM {f : X → E} (hf : LocallyIntegrable f μ)
  (K : Compacts X) :
    (X →ᵇ 𝕜) →L[𝕜] E :=
  (testAgainstLocallyIntegrableₗ 𝕜 hf K).mkContinuous (∫ x, ‖f x‖ ∂(μ.restrict K))
  (by
    intro φ
    have hf' : Integrable f (μ.restrict K) :=
      integrableOn_isCompact (hf.locallyIntegrableOn K) K.isCompact
    set g := fun x ↦ ‖φ‖ * ‖f x‖ with g_def
    have hg : Integrable g (μ.restrict K) := (Integrable.norm hf').const_mul _
    have h : ∀ᵐ (x : X) ∂(μ.restrict K), ‖(fun a ↦ (φ a) • f a) x‖ ≤ g x := by
      apply ae_of_all
      intro x
      simp only [g, norm_smul]
      bound [φ.norm_coe_le_norm x]
    apply le_trans (norm_integral_le_of_norm_le hg h)
    rw [mul_comm, integral_const_mul_of_integrable hf'.norm]
  )

end LocallyIntegrabe

end BochnerIntegral

end BoundedContinuousFunction
