/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Algebraic operations on `SeparationQuotient`

In this file we construct a section of the quotient map `E → SeparationQuotient E` as a continuous
linear map `SeparationQuotient E →L[K] E`.
-/

open Topology

namespace SeparationQuotient
section VectorSpace

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul K E]

/-- There exists a continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`.

Note that continuity of this map comes for free, because `mk` is a topology inducing map.
-/
theorem exists_out_continuousLinearMap :
    ∃ f : SeparationQuotient E →L[K] E, mkCLM K E ∘L f = .id K (SeparationQuotient E) := by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, isInducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

/-- A continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`. -/
noncomputable def outCLM : SeparationQuotient E →L[K] E :=
  (exists_out_continuousLinearMap K E).choose

@[simp]
theorem mkCLM_comp_outCLM : mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E) :=
  (exists_out_continuousLinearMap K E).choose_spec

variable {E} in
@[simp]
theorem mk_outCLM (x : SeparationQuotient E) : mk (outCLM K E x) = x :=
  DFunLike.congr_fun (mkCLM_comp_outCLM K E) x

@[simp]
theorem mk_comp_outCLM : mk ∘ outCLM K E = id := funext (mk_outCLM K)

variable {K} in
theorem postcomp_mkCLM_surjective {L : Type*} [Semiring L] (σ : L →+* K)
    (F : Type*) [AddCommMonoid F] [Module L F] [TopologicalSpace F] :
    Function.Surjective ((mkCLM K E).comp : (F →SL[σ] E) → (F →SL[σ] SeparationQuotient E)) := by
  intro f
  use (outCLM K E).comp f
  rw [← ContinuousLinearMap.comp_assoc, mkCLM_comp_outCLM, ContinuousLinearMap.id_comp]

/-- The `SeparationQuotient.outCLM K E` map is a topological embedding. -/
theorem isEmbedding_outCLM : IsEmbedding (outCLM K E) :=
  Function.LeftInverse.isEmbedding (mk_outCLM K) continuous_mk (map_continuous _)

@[deprecated (since := "2024-10-26")]
alias outCLM_embedding := isEmbedding_outCLM

theorem outCLM_injective : Function.Injective (outCLM K E) :=
  (isEmbedding_outCLM K E).injective

end VectorSpace

section VectorSpaceUniform

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul K E]

theorem outCLM_isUniformInducing : IsUniformInducing (outCLM K E) := by
  rw [← isUniformInducing_mk.isUniformInducing_comp_iff, mk_comp_outCLM]
  exact .id

theorem outCLM_isUniformEmbedding : IsUniformEmbedding (outCLM K E) where
  injective := outCLM_injective K E
  toIsUniformInducing := outCLM_isUniformInducing K E

theorem outCLM_uniformContinuous : UniformContinuous (outCLM K E) :=
  (outCLM_isUniformInducing K E).uniformContinuous

end VectorSpaceUniform
end SeparationQuotient
