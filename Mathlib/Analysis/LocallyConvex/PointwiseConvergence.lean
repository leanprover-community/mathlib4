/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.PointwiseConvergence
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.StrongTopology

/-!
# The topology of pointwise convergence is locally convex

We prove that the topology of pointwise convergence is induced by a family of seminorms and
that it is locally convex in the topological sense

* `PointwiseConvergenceCLM.seminorm`: the seminorms on `E →SLₚₜ[σ] F` given by `A ↦ ‖A x‖` for fixed
`x : E`.
* `PointwiseConvergenceCLM.withSeminorm`: the topology is induced by the seminorms.
* `PointwiseConvergenceCLM.instLocallyConvexSpace`: `E →SLₚₜ[σ] F` is locally convex.

-/

@[expose] public section

variable {α R 𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₃ →+* 𝕜₂} {D E F G : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]

namespace PointwiseConvergenceCLM

section NormedSpace

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
protected def seminorm (x : E) : Seminorm 𝕜₂ (E →SLₚₜ[σ] F) where
  toFun A := ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]

variable (σ E F) in
/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
protected abbrev seminormFamily : SeminormFamily 𝕜₂ (E →SLₚₜ[σ] F) E :=
  PointwiseConvergenceCLM.seminorm

variable (σ E F) in
/-- The coercion `E →SLₚₜ[σ] F` to `E → F` as a linear map.

The topology on `E →SLₚₜ[σ] F` is induced by this map. -/
def inducingFn : (E →SLₚₜ[σ] F) →ₗ[𝕜₂] (E → F) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (σ E F) in
theorem isInducing_inducingFn : Topology.IsInducing (inducingFn σ E F) :=
  (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing

lemma withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F) :=
  let e : E ≃ (Σ _ : E, Fin 1) := .symm <| .sigmaUnique _ _
  (isInducing_inducingFn σ E F).withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ F)
    |>.congr_equiv e

section Tendsto

open Filter
open scoped Topology

theorem tendsto_nhds {f : Filter α} (u : α → E →SLₚₜ[σ] F) (y₀ : E →SLₚₜ[σ] F) :
    Tendsto u f (𝓝 y₀) ↔ ∀ (x : E) (ε : ℝ), 0 < ε → ∀ᶠ (k : α) in f, ‖u k x - y₀ x‖ < ε :=
  PointwiseConvergenceCLM.withSeminorms.tendsto_nhds _ _

theorem tendsto_nhds_atTop [SemilatticeSup α] [Nonempty α] (u : α → E →SLₚₜ[σ] F)
    (y₀ : E →SLₚₜ[σ] F) :
    Tendsto u atTop (𝓝 y₀) ↔
      ∀ (x : E) (ε : ℝ), 0 < ε → ∃ (k₀ : α), ∀ (k : α), k₀ ≤ k → ‖u k x - y₀ x‖ < ε :=
  PointwiseConvergenceCLM.withSeminorms.tendsto_nhds_atTop _ _

end Tendsto

section ContinuousLinearMap

variable [AddCommGroup D] [TopologicalSpace D] [Module 𝕜₃ D]
  [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [NormedAddCommGroup G] [NormedSpace 𝕜₂ G]

open NNReal ContinuousLinearMap

variable (F G) in
/-- Define a continuous linear map between `E →SLₚₜ[σ] F` and `D →SLₚₜ[τ] G`.

Use `PointwiseConvergenceCLM.precomp` for the special case of the adjoint operator. -/
def mkCLM (A : (E →SL[σ] F) →ₗ[𝕜₂] D →SL[τ] G) (hbound : ∀ (f : D), ∃ (s : Finset E) (C : ℝ≥0),
  ∀ (B : E →SL[σ] F), ∃ (g : E) (_hb : g ∈ s), ‖(A B) f‖ ≤ C • ‖B g‖) :
    (E →SLₚₜ[σ] F) →L[𝕜₂] D →SLₚₜ[τ] G where
  __ := (toUniformConvergenceCLM _ _ _).toLinearMap.comp
    (A.comp (toUniformConvergenceCLM _ _ _).symm.toLinearMap)
  cont := by
    apply Seminorm.continuous_from_bounded PointwiseConvergenceCLM.withSeminorms
      PointwiseConvergenceCLM.withSeminorms A
    intro f
    obtain ⟨s, C, h⟩ := hbound f
    use s, C
    rw [← Seminorm.finset_sup_smul]
    intro B
    obtain ⟨g, h₁, h₂⟩ := h ((toUniformConvergenceCLM _ _ _).symm B)
    refine le_trans ?_ (Seminorm.le_finset_sup_apply h₁)
    exact h₂

end ContinuousLinearMap

end NormedSpace

section IsTopologicalAddGroup

variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜₂ F]
  [Semiring R] [PartialOrder R]
  [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

instance : LocallyConvexSpace R (E →SLₚₜ[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R {(s : Set E) | Set.Finite s} ⟨∅, Set.finite_empty⟩
    (directedOn_of_sup_mem fun _ _ => Set.Finite.union)

end IsTopologicalAddGroup

end PointwiseConvergenceCLM
