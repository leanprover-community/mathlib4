/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.Multilinear.Bounded
import Mathlib.Topology.Algebra.UniformConvergence

/-!
# Topology on continuous multilinear maps

In this file we define `TopologicalSpace` and `UniformSpace` structures
on `ContinuousMultilinearMap 𝕜 E F`,
where `E i` is a family of vector spaces over `𝕜` with topologies
and `F` is a topological vector space.
-/
open Bornology Set
open scoped Topology UniformConvergence Filter

namespace ContinuousMultilinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
  [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F]

/-- An auxiliary definition used to define topology on `ContinuousMultilinearMap 𝕜 E F`. -/
def toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
  UniformOnFun.ofFun _ f

@[simp]
lemma toUniformOnFun_toFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    UniformOnFun.toFun _ f.toUniformOnFun = f :=
  rfl

instance instTopologicalSpace [TopologicalSpace F] [TopologicalAddGroup F] :
    TopologicalSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .induced toUniformOnFun <|
    @UniformOnFun.topologicalSpace _ _ (TopologicalAddGroup.toUniformSpace F) _

instance instUniformSpace [UniformSpace F] [UniformAddGroup F] :
    UniformSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace _ _ _) <| by
    rw [instTopologicalSpace, UniformAddGroup.toUniformSpace_eq]; rfl

section UniformAddGroup

variable [UniformSpace F] [UniformAddGroup F]

lemma uniformEmbedding_toUniformOnFun :
    UniformEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F → _) where
  inj := DFunLike.coe_injective
  comap_uniformity := rfl

lemma embedding_toUniformOnFun : Embedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F → _) :=
  uniformEmbedding_toUniformOnFun.embedding

theorem uniformContinuous_coe_fun [∀ i, ContinuousSMul 𝕜 (E i)] :
    UniformContinuous (DFunLike.coe : ContinuousMultilinearMap 𝕜 E F → (Π i, E i) → F) :=
  (UniformOnFun.uniformContinuous_toFun isVonNBounded_covers).comp
    uniformEmbedding_toUniformOnFun.uniformContinuous

theorem uniformContinuous_eval_const [∀ i, ContinuousSMul 𝕜 (E i)] (x : Π i, E i) :
    UniformContinuous fun f : ContinuousMultilinearMap 𝕜 E F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

instance instUniformAddGroup : UniformAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  let φ : ContinuousMultilinearMap 𝕜 E F →+ (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ ↦ rfl, map_zero' := rfl }
  uniformEmbedding_toUniformOnFun.uniformAddGroup φ

instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) :=
  haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  uniformEmbedding_toUniformOnFun.uniformContinuousConstSMul fun _ _ ↦ rfl

end UniformAddGroup

variable [TopologicalSpace F] [TopologicalAddGroup F]

instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) := by
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  infer_instance

instance instContinuousSMul [ContinuousSMul 𝕜 F] :
    ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 E F) :=
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] (Π i, E i) → F :=
    { toFun := (↑), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ φ
    embedding_toUniformOnFun.toInducing fun _ _ hu ↦ hu.image_multilinear _

theorem hasBasis_nhds_zero_of_basis {ι : Type*} {p : ι → Prop} {b : ι → Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun Si : Set (Π i, E i) × ι => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  rw [nhds_induced]
  refine (UniformOnFun.hasBasis_nhds_zero_of_basis _ ?_ ?_ h).comap DFunLike.coe
  · exact ⟨∅, isVonNBounded_empty _ _⟩
  · exact directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union

theorem hasBasis_nhds_zero :
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun SV : Set (Π i, E i) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 ∈ 𝓝 0) fun SV =>
      { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

variable [∀ i, ContinuousSMul 𝕜 (E i)]

theorem continuous_eval_const (x : Π i, E i) :
    Continuous fun p : ContinuousMultilinearMap 𝕜 E F ↦ p x := by
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  exact (uniformContinuous_eval_const x).continuous
#align continuous_multilinear_map.continuous_eval_left ContinuousMultilinearMap.continuous_eval_const

@[deprecated (since := "2024-04-10")] alias continuous_eval_left := continuous_eval_const

theorem continuous_coe_fun :
    Continuous (DFunLike.coe : ContinuousMultilinearMap 𝕜 E F → (Π i, E i) → F) :=
  continuous_pi continuous_eval_const

instance instT2Space [T2Space F] : T2Space (ContinuousMultilinearMap 𝕜 E F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coe_fun

variable (𝕜 E F)

/-- The application of a multilinear map as a `ContinuousLinearMap`. -/
def apply [ContinuousConstSMul 𝕜 F] (m : Π i, E i) : ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const m

variable {𝕜 E F}

@[simp]
lemma apply_apply [ContinuousConstSMul 𝕜 F] {m : Π i, E i} {c : ContinuousMultilinearMap 𝕜 E F} :
    apply 𝕜 E F m c = c m := rfl

theorem hasSum_eval {α : Type*} {p : α → ContinuousMultilinearMap 𝕜 E F}
    {q : ContinuousMultilinearMap 𝕜 E F} (h : HasSum p q) (m : Π i, E i) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)
#align continuous_multilinear_map.has_sum_eval ContinuousMultilinearMap.hasSum_eval

theorem tsum_eval [T2Space F] {α : Type*} {p : α → ContinuousMultilinearMap 𝕜 E F} (hp : Summable p)
    (m : Π i, E i) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm
#align continuous_multilinear_map.tsum_eval ContinuousMultilinearMap.tsum_eval

end ContinuousMultilinearMap
