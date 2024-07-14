/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Module.UniformConvergence

#align_import topology.algebra.module.strong_topology from "leanprover-community/mathlib"@"8905e5ed90859939681a725b00f6063e65096d95"

/-!
# Strong topologies on the space of continuous linear maps

In this file, we define the strong topologies on `E →L[𝕜] F` associated with a family
`𝔖 : Set (Set E)` to be the topology of uniform convergence on the elements of `𝔖` (also called
the topology of `𝔖`-convergence).

The lemma `UniformOnFun.continuousSMul_of_image_bounded` tells us that this is a
vector space topology if the continuous linear image of any element of `𝔖` is bounded (in the sense
of `Bornology.IsVonNBounded`).

We then declare an instance for the case where `𝔖` is exactly the set of all bounded subsets of
`E`, giving us the so-called "topology of uniform convergence on bounded sets" (or "topology of
bounded convergence"), which coincides with the operator norm topology in the case of
`NormedSpace`s.

Other useful examples include the weak-* topology (when `𝔖` is the set of finite sets or the set
of singletons) and the topology of compact convergence (when `𝔖` is the set of relatively compact
sets).

## Main definitions

* `UniformConvergenceCLM` is a type synonym for `E →SL[σ] F` equipped with the `𝔖`-topology.
* `UniformConvergenceCLM.instTopologicalSpace` is the topology mentioned above for an arbitrary `𝔖`.
* `ContinuousLinearMap.topologicalSpace` is the topology of bounded convergence. This is
  declared as an instance.

## Main statements

* `UniformConvergenceCLM.instTopologicalAddGroup` and
  `UniformConvergenceCLM.instContinuousSMul` show that the strong topology
  makes `E →L[𝕜] F` a topological vector space, with the assumptions on `𝔖` mentioned above.
* `ContinuousLinearMap.topologicalAddGroup` and
  `ContinuousLinearMap.continuousSMul` register these facts as instances for the special
  case of bounded convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## TODO

* Add convergence on compact subsets

## Tags

uniform convergence, bounded convergence
-/


open scoped Topology UniformConvergence

section General

/-! ### 𝔖-Topologies -/

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E E' F F' : Type*}
  [AddCommGroup E] [Module 𝕜₁ E] [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace E] [TopologicalSpace E'] (F)

/-- Given `E` and `F` two topological vector spaces and `𝔖 : Set (Set E)`, then
`UniformConvergenceCLM σ F 𝔖` is a type synonym of `E →SL[σ] F` equipped with the "topology of
uniform convergence on the elements of `𝔖`".

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →SL[σ] F` a
topological vector space. -/
@[nolint unusedArguments]
def UniformConvergenceCLM [TopologicalSpace F] [TopologicalAddGroup F] (_ : Set (Set E)) :=
  E →SL[σ] F

namespace UniformConvergenceCLM

instance instFunLike [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) : FunLike (UniformConvergenceCLM σ F 𝔖) E F :=
  ContinuousLinearMap.funLike

instance instContinuousSemilinearMapClass [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) : ContinuousSemilinearMapClass (UniformConvergenceCLM σ F 𝔖) σ E F :=
  ContinuousLinearMap.continuousSemilinearMapClass

instance instTopologicalSpace [TopologicalSpace F] [TopologicalAddGroup F] (𝔖 : Set (Set E)) :
    TopologicalSpace (UniformConvergenceCLM σ F 𝔖) :=
  (@UniformOnFun.topologicalSpace E F (TopologicalAddGroup.toUniformSpace F) 𝔖).induced
    (DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → (E →ᵤ[𝔖] F))
#align continuous_linear_map.strong_topology UniformConvergenceCLM.instTopologicalSpace

theorem topologicalSpace_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    instTopologicalSpace σ F 𝔖 = TopologicalSpace.induced DFunLike.coe
      (UniformOnFun.topologicalSpace E F 𝔖) := by
  rw [instTopologicalSpace]
  congr
  exact UniformAddGroup.toUniformSpace_eq

/-- The uniform structure associated with `ContinuousLinearMap.strongTopology`. We make sure
that this has nice definitional properties. -/
instance instUniformSpace [UniformSpace F] [UniformAddGroup F]
    (𝔖 : Set (Set E)) : UniformSpace (UniformConvergenceCLM σ F 𝔖) :=
  UniformSpace.replaceTopology
    ((UniformOnFun.uniformSpace E F 𝔖).comap
      (DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → (E →ᵤ[𝔖] F)))
    (by rw [UniformConvergenceCLM.instTopologicalSpace, UniformAddGroup.toUniformSpace_eq]; rfl)
#align continuous_linear_map.strong_uniformity UniformConvergenceCLM.instUniformSpace

theorem uniformSpace_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    instUniformSpace σ F 𝔖 = UniformSpace.comap DFunLike.coe (UniformOnFun.uniformSpace E F 𝔖) := by
  rw [instUniformSpace, UniformSpace.replaceTopology_eq]

@[simp]
theorem uniformity_toTopologicalSpace_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    (UniformConvergenceCLM.instUniformSpace σ F 𝔖).toTopologicalSpace =
      UniformConvergenceCLM.instTopologicalSpace σ F 𝔖 :=
  rfl
#align continuous_linear_map.strong_uniformity_topology_eq UniformConvergenceCLM.uniformity_toTopologicalSpace_eq

theorem uniformEmbedding_coeFn [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    UniformEmbedding (α := UniformConvergenceCLM σ F 𝔖) (β := E →ᵤ[𝔖] F) DFunLike.coe :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩
#align continuous_linear_map.strong_uniformity.uniform_embedding_coe_fn UniformConvergenceCLM.uniformEmbedding_coeFn

theorem embedding_coeFn [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    Embedding (X := UniformConvergenceCLM σ F 𝔖) (Y := E →ᵤ[𝔖] F)
      (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  UniformEmbedding.embedding (uniformEmbedding_coeFn _ _ _)
#align continuous_linear_map.strong_topology.embedding_coe_fn UniformConvergenceCLM.embedding_coeFn

instance instAddCommGroup [TopologicalSpace F] [TopologicalAddGroup F] (𝔖 : Set (Set E)) :
    AddCommGroup (UniformConvergenceCLM σ F 𝔖) := ContinuousLinearMap.addCommGroup

instance instUniformAddGroup [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    UniformAddGroup (UniformConvergenceCLM σ F 𝔖) := by
  let φ : (UniformConvergenceCLM σ F 𝔖) →+ E →ᵤ[𝔖] F :=
    ⟨⟨(DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → E →ᵤ[𝔖] F), rfl⟩, fun _ _ => rfl⟩
  exact (uniformEmbedding_coeFn _ _ _).uniformAddGroup φ
#align continuous_linear_map.strong_uniformity.uniform_add_group UniformConvergenceCLM.instUniformAddGroup

instance instTopologicalAddGroup [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) : TopologicalAddGroup (UniformConvergenceCLM σ F 𝔖) := by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  infer_instance
#align continuous_linear_map.strong_topology.topological_add_group UniformConvergenceCLM.instTopologicalAddGroup

theorem t2Space [TopologicalSpace F] [TopologicalAddGroup F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) : T2Space (UniformConvergenceCLM σ F 𝔖) := by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  haveI : T2Space (E →ᵤ[𝔖] F) := UniformOnFun.t2Space_of_covering h𝔖
  exact (embedding_coeFn σ F 𝔖).t2Space
#align continuous_linear_map.strong_topology.t2_space UniformConvergenceCLM.t2Space

instance instDistribMulAction (M : Type*) [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    DistribMulAction M (UniformConvergenceCLM σ F 𝔖) := ContinuousLinearMap.distribMulAction

instance instModule (R : Type*) [Semiring R] [Module R F] [SMulCommClass 𝕜₂ R F]
    [TopologicalSpace F] [ContinuousConstSMul R F] [TopologicalAddGroup F] (𝔖 : Set (Set E)) :
    Module R (UniformConvergenceCLM σ F 𝔖) := ContinuousLinearMap.module

theorem continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] (𝔖 : Set (Set E))
    (h𝔖₃ : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜₁ S) :
    ContinuousSMul 𝕜₂ (UniformConvergenceCLM σ F 𝔖) := by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  let φ : (UniformConvergenceCLM σ F 𝔖) →ₗ[𝕜₂] E → F :=
    ⟨⟨DFunLike.coe, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  exact UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜₂ E F (UniformConvergenceCLM σ F 𝔖) φ
    ⟨rfl⟩ fun u s hs => (h𝔖₃ s hs).image u
#align continuous_linear_map.strong_topology.has_continuous_smul UniformConvergenceCLM.continuousSMul

theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [TopologicalAddGroup F]
    {ι : Type*} (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop}
    {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : UniformConvergenceCLM σ F 𝔖)).HasBasis
      (fun Si : Set E × ι => Si.1 ∈ 𝔖 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } := by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  rw [(embedding_coeFn σ F 𝔖).toInducing.nhds_eq_comap]
  exact (UniformOnFun.hasBasis_nhds_zero_of_basis 𝔖 h𝔖₁ h𝔖₂ h).comap DFunLike.coe
#align continuous_linear_map.strong_topology.has_basis_nhds_zero_of_basis UniformConvergenceCLM.hasBasis_nhds_zero_of_basis

theorem hasBasis_nhds_zero [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 (0 : UniformConvergenceCLM σ F 𝔖)).HasBasis
      (fun SV : Set E × Set F => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 0 : Filter F)) fun SV =>
      { f : UniformConvergenceCLM σ F 𝔖 | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  hasBasis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ (𝓝 0).basis_sets
#align continuous_linear_map.strong_topology.has_basis_nhds_zero UniformConvergenceCLM.hasBasis_nhds_zero

instance instUniformContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [UniformAddGroup F] [UniformContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    UniformContinuousConstSMul M (UniformConvergenceCLM σ F 𝔖) :=
  (uniformEmbedding_coeFn σ F 𝔖).toUniformInducing.uniformContinuousConstSMul fun _ _ ↦ by rfl

instance instContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    ContinuousConstSMul M (UniformConvergenceCLM σ F 𝔖) :=
  let _ := TopologicalAddGroup.toUniformSpace F
  have _ : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  have _ := uniformContinuousConstSMul_of_continuousConstSMul M F
  inferInstance

theorem tendsto_iff_tendstoUniformlyOn {ι : Type*} {p : Filter ι} [UniformSpace F]
    [UniformAddGroup F] (𝔖 : Set (Set E)) {a : ι → UniformConvergenceCLM σ F 𝔖}
    {a₀ : UniformConvergenceCLM σ F 𝔖} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ s ∈ 𝔖, TendstoUniformlyOn (a · ·) a₀ p s := by
  rw [(embedding_coeFn σ F 𝔖).tendsto_nhds_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rfl

variable {𝔖₁ 𝔖₂ : Set (Set E)}

theorem uniformSpace_mono [UniformSpace F] [UniformAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instUniformSpace σ F 𝔖₁ ≤ instUniformSpace σ F 𝔖₂ := by
  simp_rw [uniformSpace_eq]
  exact UniformSpace.comap_mono (UniformOnFun.mono (le_refl _) h)

theorem topologicalSpace_mono [TopologicalSpace F] [TopologicalAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instTopologicalSpace σ F 𝔖₁ ≤ instTopologicalSpace σ F 𝔖₂ := by
  letI := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  simp_rw [← uniformity_toTopologicalSpace_eq]
  exact UniformSpace.toTopologicalSpace_mono (uniformSpace_mono σ F h)

end UniformConvergenceCLM

end General

namespace ContinuousLinearMap

section BoundedSets

/-! ### Topology of bounded convergence  -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E E' F F' G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F] [Module 𝕜₂ F] [AddCommGroup F']
  [Module ℝ F'] [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

/-- The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topology induced by
the operator norm when `E` and `F` are normed spaces. -/
instance topologicalSpace [TopologicalSpace F] [TopologicalAddGroup F] :
    TopologicalSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.instTopologicalSpace σ F { S | Bornology.IsVonNBounded 𝕜₁ S }

instance topologicalAddGroup [TopologicalSpace F] [TopologicalAddGroup F] :
    TopologicalAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instTopologicalAddGroup σ F _

instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F]
    [TopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E →SL[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | Bornology.IsVonNBounded 𝕜₁ S } fun _ hs => hs

instance uniformSpace [UniformSpace F] [UniformAddGroup F] : UniformSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformSpace σ F { S | Bornology.IsVonNBounded 𝕜₁ S }

instance uniformAddGroup [UniformSpace F] [UniformAddGroup F] : UniformAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformAddGroup σ F _

instance [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜₁ E] [T2Space F] :
    T2Space (E →SL[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _
    (Set.eq_univ_of_forall fun x =>
      Set.mem_sUnion_of_mem (Set.mem_singleton x) (Bornology.isVonNBounded_singleton x))

protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [TopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL[σ] F)).HasBasis (fun Si : Set E × ι => Bornology.IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Bornology.IsVonNBounded 𝕜₁ S }
    ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union) h
#align continuous_linear_map.has_basis_nhds_zero_of_basis ContinuousLinearMap.hasBasis_nhds_zero_of_basis

protected theorem hasBasis_nhds_zero [TopologicalSpace F] [TopologicalAddGroup F] :
    (𝓝 (0 : E →SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => Bornology.IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets
#align continuous_linear_map.has_basis_nhds_zero ContinuousLinearMap.hasBasis_nhds_zero

instance uniformContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [UniformAddGroup F] [UniformContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _

instance continuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instContinuousConstSMul σ F _ _

variable (G) [TopologicalSpace F] [TopologicalSpace G]

/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps]
def precomp [TopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E →SL[σ] F) : (F →SL[τ] G) →L[𝕜₃] E →SL[ρ] G where
  toFun f := f.comp L
  map_add' f g := add_comp f g L
  map_smul' a f := smul_comp a f L
  cont := by
    letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    rw [(UniformConvergenceCLM.embedding_coeFn _ _ _).continuous_iff]
    -- Porting note: without this, the following doesn't work
    change Continuous ((fun f ↦ UniformOnFun.ofFun _ (f ∘ L)) ∘ DFunLike.coe)
    exact (UniformOnFun.precomp_uniformContinuous fun S hS => hS.image L).continuous.comp
        (UniformConvergenceCLM.embedding_coeFn _ _ _).continuous
#align continuous_linear_map.precomp ContinuousLinearMap.precomp

variable (E) {G}

/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps]
def postcomp [TopologicalAddGroup F] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) : (E →SL[σ] F) →SL[τ] E →SL[ρ] G where
  toFun f := L.comp f
  map_add' := comp_add L
  map_smul' := comp_smulₛₗ L
  cont := by
    letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
    haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
    rw [(UniformConvergenceCLM.embedding_coeFn _ _ _).continuous_iff]
    exact
      (UniformOnFun.postcomp_uniformContinuous L.uniformContinuous).continuous.comp
        (UniformConvergenceCLM.embedding_coeFn _ _ _).continuous
#align continuous_linear_map.postcomp ContinuousLinearMap.postcomp

end BoundedSets

section BilinearMaps

variable {𝕜 : Type*} [NormedField 𝕜] {E F G : Type*}
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- Send a continuous bilinear map to an abstract bilinear map (forgetting continuity). -/
def toLinearMap₂ (L : E →L[𝕜] F →L[𝕜] G) : E →ₗ[𝕜] F →ₗ[𝕜] G := (coeLM 𝕜).comp L.toLinearMap

@[simp] lemma toLinearMap₂_apply (L : E →L[𝕜] F →L[𝕜] G) (v : E) (w : F) :
    L.toLinearMap₂ v w = L v w := rfl

end BilinearMaps

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NontriviallyNormedField 𝕜₄] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalAddGroup G] [TopologicalAddGroup H] [ContinuousConstSMul 𝕜₃ G]
  [ContinuousConstSMul 𝕜₄ H] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps]
def arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E →SL[σ₁₄] H) ≃SL[σ₄₃] F →SL[σ₂₃] G :=
{ e₁₂.arrowCongrEquiv e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
    map_add' := fun f g => by simp only [add_comp, comp_add]
    map_smul' := fun t f => by simp only [smul_comp, comp_smulₛₗ]
    continuous_toFun := ((postcomp F e₄₃.toContinuousLinearMap).comp
      (precomp H e₁₂.symm.toContinuousLinearMap)).continuous
    continuous_invFun := ((precomp H e₁₂.toContinuousLinearMap).comp
      (postcomp F e₄₃.symm.toContinuousLinearMap)).continuous }
set_option linter.uppercaseLean3 false in
#align continuous_linear_equiv.arrow_congrSL ContinuousLinearEquiv.arrowCongrSL
set_option linter.uppercaseLean3 false in
#align continuous_linear_equiv.arrow_congrSL_apply ContinuousLinearEquiv.arrowCongrSL_apply
set_option linter.uppercaseLean3 false in
#align continuous_linear_equiv.arrow_congrSL_symm_apply ContinuousLinearEquiv.arrowCongrSL_symm_apply

-- Porting note: the following two lemmas were autogenerated by `simps` in Lean3, but this is
-- no longer the case. The first one can already be proven by `simp`, but the second can't.

theorem arrowCongrSL_toLinearEquiv_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (L : E →SL[σ₁₄] H) : (e₁₂.arrowCongrSL e₄₃).toLinearEquiv L =
      (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align continuous_linear_equiv.arrow_congrSL_to_linear_equiv_apply ContinuousLinearEquiv.arrowCongrSL_toLinearEquiv_apply

@[simp]
theorem arrowCongrSL_toLinearEquiv_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (L : F →SL[σ₂₃] G) : (e₁₂.arrowCongrSL e₄₃).toLinearEquiv.symm L =
      (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align continuous_linear_equiv.arrow_congrSL_to_linear_equiv_symm_apply ContinuousLinearEquiv.arrowCongrSL_toLinearEquiv_symm_apply

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*} [AddCommGroup E]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup H] [NontriviallyNormedField 𝕜] [Module 𝕜 E]
  [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H] [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalAddGroup G] [TopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. -/
def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] F →L[𝕜] G :=
  e₁.arrowCongrSL e₂
#align continuous_linear_equiv.arrow_congr ContinuousLinearEquiv.arrowCongr

@[simp] lemma arrowCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E →L[𝕜] H) (x : F) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl

@[simp] lemma arrowCongr_symm (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := rfl

end Linear

end ContinuousLinearEquiv
