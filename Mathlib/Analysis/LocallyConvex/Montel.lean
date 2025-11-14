/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Montel spaces

-/

open Filter Topology Set ContinuousLinearMap Bornology

section definition

variable {𝕜 E F : Type*}
variable [SeminormedRing 𝕜] [Zero E] [SMul 𝕜 E]
  [TopologicalSpace E]

class MontelSpace (𝕜 E : Type*) [SeminormedRing 𝕜] [Zero E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  heine_borel : ∀ (s : Set E) (_ : IsClosed s) (_ : IsVonNBounded 𝕜 s), IsCompact s

namespace MontelSpace

variable (𝕜) in
theorem isCompact_of_isClosed_isVonNBounded [hm : MontelSpace 𝕜 E] {s : Set E}
    (h_closed : IsClosed s) (h_bounded : IsVonNBounded 𝕜 s) : IsCompact s :=
  hm.heine_borel s h_closed h_bounded

end MontelSpace

end definition

section Normed

namespace MontelSpace

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [hM : MontelSpace 𝕜 E]

theorem finiteDimensional : FiniteDimensional 𝕜 E :=
  FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one
    (isCompact_of_isClosed_isVonNBounded 𝕜 Metric.isClosed_closedBall
      (NormedSpace.isVonNBounded_closedBall _ _ _) )

end MontelSpace

end Normed

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
variable {E F : Type*}
  [AddCommGroup E] [Module 𝕜₁ E]
  [UniformSpace E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F]

open CompactConvergenceCLM

variable (σ E F) in
/-- The linear equivalence that sends a continuous linear map to the type copy endowed with the
weak operator topology.

This definition is only used to prove the continuous linear equivalence. -/
private def _root_.LinearEquiv.toCompactConvergenceCLM :
    (E →SL[σ] F) ≃ₗ[𝕜₂] E →SL_c[σ] F :=
  LinearEquiv.refl 𝕜₂ _

variable [IsUniformAddGroup E] [ContinuousSMul 𝕜₁ E]

variable (σ E F) in
/-- If `E` is a Montel space, then the strong topology on `E →L[𝕜] F` coincides with the topology
of compact convergence.

We realize this equality in terms of a continuous linear equivalence between the type synonyms.

This is Proposition 34.5 in Treves - Topological vector spaces, distributions, and kernels. -/
def _root_.ContinuousLinearEquiv.toCompactConvergenceCLM [T1Space E] [MontelSpace 𝕜₁ E] :
    (E →SL[σ] F) ≃L[𝕜₂] E →SL_c[σ] F where
  __ := LinearEquiv.toCompactConvergenceCLM σ E F
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, continuous_def]
    intro s hs
    apply hs.mono
    apply UniformConvergenceCLM.topologicalSpace_mono
    intro x hx
    exact hx.totallyBounded.isVonNBounded 𝕜₁
  continuous_invFun := by
    apply continuous_of_continuousAt_zero (LinearEquiv.toCompactConvergenceCLM σ E F).symm
    rw [ContinuousAt, _root_.map_zero, CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_iff
      ContinuousLinearMap.hasBasis_nhds_zero]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    use ⟨closure a, b⟩
    exact ⟨⟨MontelSpace.isCompact_of_isClosed_isVonNBounded 𝕜₁ isClosed_closure
      ha.closure, hb⟩, fun _ hf _ hx ↦ hf _ (subset_closure hx)⟩

@[simp]
theorem _root_.ContinuousLinearEquiv.toCompactConvergenceCLM_apply [T1Space E] [MontelSpace 𝕜₁ E]
    (f : E →SL[σ] F) (x : E) : ContinuousLinearEquiv.toCompactConvergenceCLM σ E F f x = f x := rfl

@[simp]
theorem _root_.ContinuousLinearEquiv.toCompactConvergenceCLM_symm_apply [T1Space E]
    [MontelSpace 𝕜₁ E] (f : E →SL_c[σ] F) (x : E) :
    (ContinuousLinearEquiv.toCompactConvergenceCLM σ E F).symm f x = f x := rfl
