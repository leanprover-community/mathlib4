/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Topology on continuous alternating maps

In this file we define `UniformSpace` and `TopologicalSpace` structures
on the space of continuous alternating maps between topological vector spaces.

The structures are induced by those on `ContinuousMultilinearMap`s,
and most of the lemmas follow from the corresponding lemmas about `ContinuousMultilinearMap`s.
-/

open Bornology Function Set
open scoped Topology UniformConvergence Filter

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]

section UniformAddGroup

variable [UniformSpace F] [UniformAddGroup F]

instance instUniformSpace : UniformSpace (E [⋀^ι]→L[𝕜] F) :=
  .comap toContinuousMultilinearMap inferInstance

lemma uniformEmbedding_toContinuousMultilinearMap :
    UniformEmbedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) where
  inj := toContinuousMultilinearMap_injective
  comap_uniformity := rfl

lemma uniformContinuous_toContinuousMultilinearMap :
    UniformContinuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) :=
  uniformEmbedding_toContinuousMultilinearMap.uniformContinuous

theorem uniformContinuous_coe_fun [ContinuousSMul 𝕜 E] :
    UniformContinuous (DFunLike.coe : (E [⋀^ι]→L[𝕜] F) → (ι → E) → F) :=
  ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap

theorem uniformContinuous_eval_const [ContinuousSMul 𝕜 E] (x : ι → E) :
    UniformContinuous fun f : E [⋀^ι]→L[𝕜] F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

instance instUniformAddGroup : UniformAddGroup (E [⋀^ι]→L[𝕜] F) :=
  uniformEmbedding_toContinuousMultilinearMap.uniformAddGroup
    (toContinuousMultilinearMapLinear (R := ℕ))

instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E [⋀^ι]→L[𝕜] F) :=
  uniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul fun _ _ ↦ rfl

section CompleteSpace

variable [ContinuousSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [CompleteSpace F] [T2Space F]

open UniformOnFun in
theorem completeSpace (h : RestrictGenTopology {s : Set (ι → E) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) := by
  have := ContinuousMultilinearMap.completeSpace (F := F) h
  rw [completeSpace_iff_isComplete_range
    uniformEmbedding_toContinuousMultilinearMap.toUniformInducing, range_toContinuousMultilinearMap]
  simp only [setOf_forall]
  apply IsClosed.isComplete
  repeat refine isClosed_iInter fun _ ↦ ?_
  exact isClosed_singleton.preimage (ContinuousMultilinearMap.continuous_eval_const _)

instance instCompleteSpace [TopologicalAddGroup E] [SequentialSpace (ι → E)] :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) :=
  completeSpace <| .of_seq fun _u x hux ↦ (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F] [ContinuousSMul 𝕜 E]

theorem uniformEmbedding_restrictScalars :
    UniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) := by
  rw [← uniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.uniformEmbedding_restrictScalars 𝕜').comp
    uniformEmbedding_toContinuousMultilinearMap

theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  (uniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end UniformAddGroup

variable [TopologicalSpace F] [TopologicalAddGroup F]

instance instTopologicalSpace : TopologicalSpace (E [⋀^ι]→L[𝕜] F) :=
  .induced toContinuousMultilinearMap inferInstance

lemma embedding_toContinuousMultilinearMap :
    Embedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  uniformEmbedding_toContinuousMultilinearMap.embedding

@[continuity, fun_prop]
lemma continuous_toContinuousMultilinearMap :
    Continuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  embedding_toContinuousMultilinearMap.continuous

instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E [⋀^ι]→L[𝕜] F) :=
  embedding_toContinuousMultilinearMap.continuousConstSMul id rfl

instance instContinuousSMul [ContinuousSMul 𝕜 F] : ContinuousSMul 𝕜 (E [⋀^ι]→L[𝕜] F) :=
  embedding_toContinuousMultilinearMap.continuousSMul continuous_id rfl

theorem hasBasis_nhds_zero_of_basis {ι' : Type*} {p : ι' → Prop} {b : ι' → Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : E [⋀^ι]→L[𝕜] F)).HasBasis
      (fun Si : Set (ι → E) × ι' => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  rw [nhds_induced]
  exact (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis h).comap _

theorem hasBasis_nhds_zero :
    (𝓝 (0 : E [⋀^ι]→L[𝕜] F)).HasBasis
      (fun SV : Set (ι → E) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 ∈ 𝓝 0)
      fun SV => { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

variable [ContinuousSMul 𝕜 E]

@[continuity, fun_prop]
theorem continuous_eval_const (x : ι → E) :
    Continuous fun p : E [⋀^ι]→L[𝕜] F ↦ p x :=
  (ContinuousMultilinearMap.continuous_eval_const x).comp continuous_toContinuousMultilinearMap

theorem continuous_coe_fun :
    Continuous (DFunLike.coe : E [⋀^ι]→L[𝕜] F → (ι → E) → F) :=
  continuous_pi continuous_eval_const

instance instT2Space [T2Space F] : T2Space (E [⋀^ι]→L[𝕜] F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coe_fun

instance instT3Space [T2Space F] : T2Space (E [⋀^ι]→L[𝕜] F) :=
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

theorem embedding_restrictScalars :
    Embedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  (uniformEmbedding_restrictScalars _).embedding

@[continuity, fun_prop]
theorem continuous_restrictScalars :
    Continuous
      (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
   embedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousMultilinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps (config := .asFn) apply]
def restrictScalarsCLM [ContinuousConstSMul 𝕜' F] :
    E [⋀^ι]→L[𝕜] F →L[𝕜'] E [⋀^ι]→L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

variable (𝕜 E F)

/-- The application of a multilinear map as a `ContinuousLinearMap`. -/
def apply [ContinuousConstSMul 𝕜 F] (m : ι → E) : E [⋀^ι]→L[𝕜] F →L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const m

variable {𝕜 E F}

@[simp]
lemma apply_apply [ContinuousConstSMul 𝕜 F] {m : ι → E} {c : E [⋀^ι]→L[𝕜] F} :
    apply 𝕜 E F m c = c m := rfl

theorem hasSum_eval {α : Type*} {p : α → E [⋀^ι]→L[𝕜] F}
    {q : E [⋀^ι]→L[𝕜] F} (h : HasSum p q) (m : ι → E) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)

theorem tsum_eval [T2Space F] {α : Type*} {p : α → E [⋀^ι]→L[𝕜] F} (hp : Summable p)
    (m : ι → E) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

end ContinuousAlternatingMap
