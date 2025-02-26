/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.UniformConvergence
import Mathlib.Topology.Algebra.SeparationQuotient.Section
import Mathlib.Topology.Hom.ContinuousEvalConst

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

* `UniformConvergenceCLM.instIsTopologicalAddGroup` and
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

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity

section General

/-! ### 𝔖-Topologies -/

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E F : Type*}
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F]
variable (F)

/-- Given `E` and `F` two topological vector spaces and `𝔖 : Set (Set E)`, then
`UniformConvergenceCLM σ F 𝔖` is a type synonym of `E →SL[σ] F` equipped with the "topology of
uniform convergence on the elements of `𝔖`".

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →SL[σ] F` a
topological vector space. -/
@[nolint unusedArguments]
def UniformConvergenceCLM [TopologicalSpace F] (_ : Set (Set E)) := E →SL[σ] F

namespace UniformConvergenceCLM

instance instFunLike [TopologicalSpace F] (𝔖 : Set (Set E)) :
    FunLike (UniformConvergenceCLM σ F 𝔖) E F :=
  ContinuousLinearMap.funLike

instance instContinuousSemilinearMapClass [TopologicalSpace F] (𝔖 : Set (Set E)) :
    ContinuousSemilinearMapClass (UniformConvergenceCLM σ F 𝔖) σ E F :=
  ContinuousLinearMap.continuousSemilinearMapClass

instance instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    TopologicalSpace (UniformConvergenceCLM σ F 𝔖) :=
  (@UniformOnFun.topologicalSpace E F (IsTopologicalAddGroup.toUniformSpace F) 𝔖).induced
    (DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → (E →ᵤ[𝔖] F))

theorem topologicalSpace_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    instTopologicalSpace σ F 𝔖 = TopologicalSpace.induced (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe)
      (UniformOnFun.topologicalSpace E F 𝔖) := by
  rw [instTopologicalSpace]
  congr
  exact UniformAddGroup.toUniformSpace_eq

/-- The uniform structure associated with `ContinuousLinearMap.strongTopology`. We make sure
that this has nice definitional properties. -/
instance instUniformSpace [UniformSpace F] [UniformAddGroup F]
    (𝔖 : Set (Set E)) : UniformSpace (UniformConvergenceCLM σ F 𝔖) :=
  UniformSpace.replaceTopology
    ((UniformOnFun.uniformSpace E F 𝔖).comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe))
    (by rw [UniformConvergenceCLM.instTopologicalSpace, UniformAddGroup.toUniformSpace_eq]; rfl)

theorem uniformSpace_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    instUniformSpace σ F 𝔖 =
      UniformSpace.comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe)
        (UniformOnFun.uniformSpace E F 𝔖) := by
  rw [instUniformSpace, UniformSpace.replaceTopology_eq]

@[simp]
theorem uniformity_toTopologicalSpace_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    (UniformConvergenceCLM.instUniformSpace σ F 𝔖).toTopologicalSpace =
      UniformConvergenceCLM.instTopologicalSpace σ F 𝔖 :=
  rfl

theorem isUniformInducing_coeFn [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformInducing (α := UniformConvergenceCLM σ F 𝔖) (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  ⟨rfl⟩

theorem isUniformEmbedding_coeFn [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformEmbedding (α := UniformConvergenceCLM σ F 𝔖) (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  ⟨isUniformInducing_coeFn .., DFunLike.coe_injective⟩

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_coeFn := isUniformEmbedding_coeFn

theorem isEmbedding_coeFn [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    IsEmbedding (X := UniformConvergenceCLM σ F 𝔖) (Y := E →ᵤ[𝔖] F)
      (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  IsUniformEmbedding.isEmbedding (isUniformEmbedding_coeFn _ _ _)

@[deprecated (since := "2024-10-26")]
alias embedding_coeFn := isEmbedding_coeFn

instance instAddCommGroup [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    AddCommGroup (UniformConvergenceCLM σ F 𝔖) := ContinuousLinearMap.addCommGroup

@[simp]
theorem coe_zero [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    ⇑(0 : UniformConvergenceCLM σ F 𝔖) = 0 :=
  rfl

instance instUniformAddGroup [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    UniformAddGroup (UniformConvergenceCLM σ F 𝔖) := by
  let φ : (UniformConvergenceCLM σ F 𝔖) →+ E →ᵤ[𝔖] F :=
    ⟨⟨(DFunLike.coe : (UniformConvergenceCLM σ F 𝔖) → E →ᵤ[𝔖] F), rfl⟩, fun _ _ => rfl⟩
  exact (isUniformEmbedding_coeFn _ _ _).uniformAddGroup φ

instance instIsTopologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) : IsTopologicalAddGroup (UniformConvergenceCLM σ F 𝔖) := by
  letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  infer_instance

theorem continuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) :
    ContinuousEvalConst (UniformConvergenceCLM σ F 𝔖) E F where
  continuous_eval_const x := by
    letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
    haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
    exact (UniformOnFun.uniformContinuous_eval h𝔖 x).continuous.comp
      (isEmbedding_coeFn σ F 𝔖).continuous

theorem t2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = univ) : T2Space (UniformConvergenceCLM σ F 𝔖) := by
  letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  haveI : T2Space (E →ᵤ[𝔖] F) := UniformOnFun.t2Space_of_covering h𝔖
  exact (isEmbedding_coeFn σ F 𝔖).t2Space

instance instDistribMulAction (M : Type*) [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    DistribMulAction M (UniformConvergenceCLM σ F 𝔖) := ContinuousLinearMap.distribMulAction

instance instModule (R : Type*) [Semiring R] [Module R F] [SMulCommClass 𝕜₂ R F]
    [TopologicalSpace F] [ContinuousConstSMul R F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    Module R (UniformConvergenceCLM σ F 𝔖) := ContinuousLinearMap.module

theorem continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] (𝔖 : Set (Set E))
    (h𝔖₃ : ∀ S ∈ 𝔖, IsVonNBounded 𝕜₁ S) :
    ContinuousSMul 𝕜₂ (UniformConvergenceCLM σ F 𝔖) := by
  letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  let φ : (UniformConvergenceCLM σ F 𝔖) →ₗ[𝕜₂] E → F :=
    ⟨⟨DFunLike.coe, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  exact UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜₂ E F (UniformConvergenceCLM σ F 𝔖) φ
    ⟨rfl⟩ fun u s hs => (h𝔖₃ s hs).image u

theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop}
    {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : UniformConvergenceCLM σ F 𝔖)).HasBasis
      (fun Si : Set E × ι => Si.1 ∈ 𝔖 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } := by
  letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  rw [(isEmbedding_coeFn σ F 𝔖).isInducing.nhds_eq_comap]
  exact (UniformOnFun.hasBasis_nhds_zero_of_basis 𝔖 h𝔖₁ h𝔖₂ h).comap DFunLike.coe

theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 (0 : UniformConvergenceCLM σ F 𝔖)).HasBasis
      (fun SV : Set E × Set F => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 0 : Filter F)) fun SV =>
      { f : UniformConvergenceCLM σ F 𝔖 | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  hasBasis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ (𝓝 0).basis_sets

theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : UniformConvergenceCLM σ F 𝔖) =
      ⨅ (s : Set E) (_ : s ∈ 𝔖) (i : ι) (_ : p i),
        𝓟 {f : UniformConvergenceCLM σ F 𝔖 | MapsTo f s (b i)} := by
  letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  rw [(isEmbedding_coeFn σ F 𝔖).isInducing.nhds_eq_comap,
    UniformOnFun.nhds_eq_of_basis _ _ h.uniformity_of_nhds_zero]
  simp [MapsTo]

theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    𝓝 (0 : UniformConvergenceCLM σ F 𝔖) =
      ⨅ s ∈ 𝔖, ⨅ t ∈ 𝓝 (0 : F),
        𝓟 {f : UniformConvergenceCLM σ F 𝔖 | MapsTo f s t} :=
  nhds_zero_eq_of_basis _ _ _ (𝓝 0).basis_sets

variable {F} in
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {𝔖 : Set (Set E)} {s : Set E} (hs : s ∈ 𝔖) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : UniformConvergenceCLM σ F 𝔖 in 𝓝 0, MapsTo f s U := by
  rw [nhds_zero_eq]
  apply_rules [mem_iInf_of_mem, mem_principal_self]

variable {σ F} in
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {𝔖 : Set (Set E)} {S : Set (UniformConvergenceCLM σ F 𝔖)} (hS : IsVonNBounded R S)
    {s : Set E} (hs : s ∈ 𝔖) : IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) := by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo σ hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

variable {σ F} in
/-- A set `S` of continuous linear maps with topology of uniform convergence on sets `s ∈ 𝔖`
is von Neumann bounded iff for any `s ∈ 𝔖`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded. -/
theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {𝔖 : Set (Set E)} {S : Set (UniformConvergenceCLM σ F 𝔖)} :
    IsVonNBounded R S ↔ ∀ s ∈ 𝔖, IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) := by
  refine ⟨fun hS s hs ↦ isVonNBounded_image2_apply hS hs, fun h ↦ ?_⟩
  simp_rw [isVonNBounded_iff_absorbing_le, nhds_zero_eq, le_iInf_iff, le_principal_iff]
  intro s hs U hU
  rw [Filter.mem_absorbing, Absorbs]
  filter_upwards [h s hs hU, eventually_ne_cobounded 0] with c hc hc₀ f hf
  rw [mem_smul_set_iff_inv_smul_mem₀ hc₀]
  intro x hx
  simpa only [mem_smul_set_iff_inv_smul_mem₀ hc₀] using hc (mem_image2_of_mem hf hx)

instance instUniformContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [UniformAddGroup F] [UniformContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    UniformContinuousConstSMul M (UniformConvergenceCLM σ F 𝔖) :=
  (isUniformInducing_coeFn σ F 𝔖).uniformContinuousConstSMul fun _ _ ↦ by rfl

instance instContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    ContinuousConstSMul M (UniformConvergenceCLM σ F 𝔖) :=
  let _ := IsTopologicalAddGroup.toUniformSpace F
  have _ : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  have _ := uniformContinuousConstSMul_of_continuousConstSMul M F
  inferInstance

theorem tendsto_iff_tendstoUniformlyOn {ι : Type*} {p : Filter ι} [UniformSpace F]
    [UniformAddGroup F] (𝔖 : Set (Set E)) {a : ι → UniformConvergenceCLM σ F 𝔖}
    {a₀ : UniformConvergenceCLM σ F 𝔖} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ s ∈ 𝔖, TendstoUniformlyOn (a · ·) a₀ p s := by
  rw [(isEmbedding_coeFn σ F 𝔖).tendsto_nhds_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rfl

variable {F} in
theorem isUniformInducing_postcomp
    {G : Type*} [AddCommGroup G] [UniformSpace G] [UniformAddGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [UniformAddGroup F]
    (g : F →SL[τ] G) (hg : IsUniformInducing g) (𝔖 : Set (Set E)) :
    IsUniformInducing (α := UniformConvergenceCLM σ F 𝔖) (β := UniformConvergenceCLM ρ G 𝔖)
      g.comp := by
  rw [← (isUniformInducing_coeFn _ _ _).of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp (isUniformInducing_coeFn _ _ _)

theorem completeSpace [UniformSpace F] [UniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    {𝔖 : Set (Set E)} (h𝔖 : IsRestrictGen 𝔖) (h𝔖U : ⋃₀ 𝔖 = univ) :
    CompleteSpace (UniformConvergenceCLM σ F 𝔖) := by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp σ (SeparationQuotient.mkCLM 𝕜₂ F)
      SeparationQuotient.isUniformInducing_mk _).completeSpace_congr]
    exacts [this _ inferInstance, SeparationQuotient.postcomp_mkCLM_surjective F σ E]
  rw [completeSpace_iff_isComplete_range (isUniformInducing_coeFn _ _ _)]
  apply IsClosed.isComplete
  have H₁ : IsClosed {f : E →ᵤ[𝔖] F | Continuous ((UniformOnFun.toFun 𝔖) f)} :=
    UniformOnFun.isClosed_setOf_continuous h𝔖
  convert H₁.inter <| (LinearMap.isClosed_range_coe E F σ).preimage
    (UniformOnFun.uniformContinuous_toFun h𝔖U).continuous
  exact ContinuousLinearMap.range_coeFn_eq

variable {𝔖₁ 𝔖₂ : Set (Set E)}

theorem uniformSpace_mono [UniformSpace F] [UniformAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instUniformSpace σ F 𝔖₁ ≤ instUniformSpace σ F 𝔖₂ := by
  simp_rw [uniformSpace_eq]
  exact UniformSpace.comap_mono (UniformOnFun.mono (le_refl _) h)

theorem topologicalSpace_mono [TopologicalSpace F] [IsTopologicalAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instTopologicalSpace σ F 𝔖₁ ≤ instTopologicalSpace σ F 𝔖₂ := by
  letI := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  simp_rw [← uniformity_toTopologicalSpace_eq]
  exact UniformSpace.toTopologicalSpace_mono (uniformSpace_mono σ F h)

end UniformConvergenceCLM

end General

namespace ContinuousLinearMap

section BoundedSets

/-! ### Topology of bounded convergence  -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

/-- The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topology induced by
the operator norm when `E` and `F` are normed spaces. -/
instance topologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.instTopologicalSpace σ F { S | IsVonNBounded 𝕜₁ S }

instance topologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F] :
    IsTopologicalAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instIsTopologicalAddGroup σ F _

instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E →SL[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsVonNBounded 𝕜₁ S } fun _ hs => hs

instance uniformSpace [UniformSpace F] [UniformAddGroup F] : UniformSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformSpace σ F { S | IsVonNBounded 𝕜₁ S }

instance uniformAddGroup [UniformSpace F] [UniformAddGroup F] : UniformAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformAddGroup σ F _

instance instContinuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] : ContinuousEvalConst (E →SL[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst σ F _ Bornology.isVonNBounded_covers

instance instT2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₁ E]
    [T2Space F] : T2Space (E →SL[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _ Bornology.isVonNBounded_covers

protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL[σ] F)).HasBasis (fun Si : Set E × ι => IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h

protected theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F] :
    (𝓝 (0 : E →SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

theorem isUniformEmbedding_toUniformOnFun [UniformSpace F] [UniformAddGroup F] :
    IsUniformEmbedding
      fun f : E →SL[σ] F ↦ UniformOnFun.ofFun {s | Bornology.IsVonNBounded 𝕜₁ s} f :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn ..

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_toUniformOnFun := isUniformEmbedding_toUniformOnFun

instance uniformContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [UniformAddGroup F] [UniformContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _

instance continuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instContinuousConstSMul σ F _ _

protected theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (i : ι) (_ : p i),
        𝓟 {f : E →SL[σ] F | MapsTo f s (b i)} :=
  UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h

protected theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (U : Set F) (_ : U ∈ 𝓝 0),
        𝓟 {f : E →SL[σ] F | MapsTo f s U} :=
  UniformConvergenceCLM.nhds_zero_eq ..

/-- If `s` is a von Neumann bounded set and `U` is a neighbourhood of zero,
then sufficiently small continuous linear maps map `s` to `U`. -/
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : E →SL[σ] F in 𝓝 0, MapsTo f s U :=
  UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

/-- If `S` is a von Neumann bounded set of continuous linear maps `f : E →SL[σ] F`
and `s` is a von Neumann bounded set in the domain,
then the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

See also `isVonNBounded_iff` for an `Iff` version with stronger typeclass assumptions. -/
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} (hS : IsVonNBounded R S) {s : Set E} (hs : IsVonNBounded 𝕜₁ s) :
    IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

/-- A set `S` of continuous linear maps is von Neumann bounded
iff for any von Neumann bounded set `s`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

For the forward implication with weaker typeclass assumptions, see `isVonNBounded_image2_apply`. -/
theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} :
    IsVonNBounded R S ↔
      ∀ s, IsVonNBounded 𝕜₁ s → IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_iff

theorem completeSpace [UniformSpace F] [UniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    [ContinuousSMul 𝕜₁ E] (h : IsRestrictGen {s : Set E | IsVonNBounded 𝕜₁ s}) :
    CompleteSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.completeSpace _ _ h isVonNBounded_covers

instance instCompleteSpace [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E] [SequentialSpace E]
    [UniformSpace F] [UniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F] :
    CompleteSpace (E →SL[σ] F) :=
  completeSpace <| .of_seq fun _ _ h ↦ (h.isVonNBounded_range 𝕜₁).insert _

variable (G) [TopologicalSpace F] [TopologicalSpace G]

/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps]
def precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E →SL[σ] F) : (F →SL[τ] G) →L[𝕜₃] E →SL[ρ] G where
  toFun f := f.comp L
  map_add' f g := add_comp f g L
  map_smul' a f := smul_comp a f L
  cont := by
    letI : UniformSpace G := IsTopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    rw [(UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous_iff]
    -- Porting note: without this, the following doesn't work
    change Continuous ((fun f ↦ UniformOnFun.ofFun _ (f ∘ L)) ∘ DFunLike.coe)
    exact (UniformOnFun.precomp_uniformContinuous fun S hS => hS.image L).continuous.comp
        (UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous

variable (E) {G}

/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps]
def postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) : (E →SL[σ] F) →SL[τ] E →SL[ρ] G where
  toFun f := L.comp f
  map_add' := comp_add L
  map_smul' := comp_smulₛₗ L
  cont := by
    letI : UniformSpace G := IsTopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
    haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
    rw [(UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous_iff]
    exact
      (UniformOnFun.postcomp_uniformContinuous L.uniformContinuous).continuous.comp
        (UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous

end BoundedSets

section BilinearMaps

variable {𝕜 : Type*} [NormedField 𝕜] {E F G : Type*}
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- Send a continuous bilinear map to an abstract bilinear map (forgetting continuity). -/
def toLinearMap₂ (L : E →L[𝕜] F →L[𝕜] G) : E →ₗ[𝕜] F →ₗ[𝕜] G := (coeLM 𝕜).comp L.toLinearMap

@[simp] lemma toLinearMap₂_apply (L : E →L[𝕜] F →L[𝕜] G) (v : E) (w : F) :
    L.toLinearMap₂ v w = L v w := rfl

end BilinearMaps

section RestrictScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {F : Type*} [AddCommGroup F]

section UniformSpace

variable [UniformSpace F] [UniformAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) := by
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h ↦ h.extend_scalars _, fun h ↦ h.restrict_scalars _⟩

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_restrictScalars := isUniformEmbedding_restrictScalars

theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end UniformSpace

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

theorem isEmbedding_restrictScalars :
    IsEmbedding (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[deprecated (since := "2024-10-26")]
alias embedding_restrictScalars := isEmbedding_restrictScalars

@[continuity, fun_prop]
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
   (isEmbedding_restrictScalars _).continuous

variable (𝕜 E F)
variable (𝕜'' : Type*) [Ring 𝕜'']
  [Module 𝕜'' F] [ContinuousConstSMul 𝕜'' F] [SMulCommClass 𝕜 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F]

/-- `ContinuousLinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
def restrictScalarsL : (E →L[𝕜] F) →L[𝕜''] E →L[𝕜'] F :=
  .mk <| restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''

variable {𝕜 E F 𝕜' 𝕜''}

@[simp]
theorem coe_restrictScalarsL : (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E →L[𝕜] F) →ₗ[𝕜''] E →L[𝕜'] F) =
    restrictScalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
  rfl

@[simp]
theorem coe_restrict_scalarsL' : ⇑(restrictScalarsL 𝕜 E F 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl

end RestrictScalars

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [ContinuousConstSMul 𝕜₃ G]
  [ContinuousConstSMul 𝕜₄ H] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps apply symm_apply toLinearEquiv_apply toLinearEquiv_symm_apply]
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

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*} [AddCommGroup E]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup H] [NormedField 𝕜] [Module 𝕜 E]
  [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H] [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. -/
def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] F →L[𝕜] G :=
  e₁.arrowCongrSL e₂

@[simp] lemma arrowCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E →L[𝕜] H) (x : F) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl

@[simp] lemma arrowCongr_symm (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := rfl

end Linear

end ContinuousLinearEquiv
