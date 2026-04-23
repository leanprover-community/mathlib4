/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Hom.ContinuousEvalConst

/-!
# Topologies of uniform convergence on the space of continuous linear maps

In this file, we define the "topology of `𝔖`-convergence" on `E →L[𝕜] F`, where
`𝔖 : Set (Set E)`. It is the topology of uniform convergence on the elements of `𝔖`.
Similarly to `UniformOnFun`, we define a type synonym `UniformConvergenceCLM` for
`E →L[𝕜] F` endowed with this topology.

The lemma `UniformOnFun.continuousSMul_of_image_bounded` tells us that this is a
vector space topology if the continuous linear image of any element of `𝔖` is bounded (in the sense
of `Bornology.IsVonNBounded`).

The most important examples for such topologies are:
- the topology of bounded convergence (also called the "strong topology" on the dual space),
  when `𝔖` is the set of `IsVonNBounded` subsets.
  This coincides with the operator norm topology in the case of `NormedSpace`s,
  and is declared as an instance on `E →L[𝕜] F`
- the topology of pointwise convergence (also called "weak-\* topology"
  or "strong-operator topology" depending on the context), when `𝔖` is the set of finite
  sets or the set of singletons. This is declared as an instance on `PointwiseConvergenceCLM`.
- the topology of compact convergence, when `𝔖` is the set of compact
  sets. This is declared as an instance on `CompactConvergenceCLM`.

## Main definitions

* `UniformConvergenceCLM` is a type synonym for `E →SL[σ] F` equipped with the `𝔖`-topology.
  We denote it by `E →SLᵤ[σ, 𝔖] F`.
* `UniformConvergenceCLM.instTopologicalSpace` is the topology mentioned above for an arbitrary `𝔖`.

## Main statements

* `UniformConvergenceCLM.instIsTopologicalAddGroup` and
  `UniformConvergenceCLM.instContinuousSMul` show that the strong topology
  makes `E →L[𝕜] F` a topological vector space, with the assumptions on `𝔖` mentioned above.

## Notation

* `E →SLᵤ[σ, 𝔖] F` is space of continuous linear maps equipped with the topology
  of `𝔖`-convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

@[expose] public section

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity

/-! ### 𝔖-Topologies -/

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
  {E F G : Type*}
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F]
variable (F)

/-- Given `E` and `F` two topological vector spaces and `𝔖 : Set (Set E)`, then
`UniformConvergenceCLM σ F 𝔖` (denoted `E →SLᵤ[σ, 𝔖] F`) is a type synonym of `E →SL[σ] F` equipped
with the "topology of uniform convergence on the elements of `𝔖`".

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →SL[σ] F` a
topological vector space. -/
@[nolint unusedArguments]
def UniformConvergenceCLM [TopologicalSpace F] (_ : Set (Set E)) := E →SL[σ] F

-- There seems to be a Lean bug here: the following causes troubles later
-- `notation:25 E " →SLᵤ[" σ ", " 𝔖 "] " F => UniformConvergenceCLM σ (E := E) F 𝔖`
-- (probably because of `(E := E)` ?)

@[inherit_doc]
scoped[UniformConvergenceCLM]
notation:25 E' " →SLᵤ[" σ ", " 𝔖 "] " F => UniformConvergenceCLM σ (E := E') F 𝔖

@[inherit_doc]
scoped[UniformConvergenceCLM]
notation:25 E' " →Lᵤ[" R ", " 𝔖 "] " F => UniformConvergenceCLM (RingHom.id R) (E := E') F 𝔖

namespace UniformConvergenceCLM

instance instFunLike [TopologicalSpace F] (𝔖 : Set (Set E)) :
    FunLike (E →SLᵤ[σ, 𝔖] F) E F :=
  inferInstanceAs <| FunLike (E →SL[σ] F) E F

@[ext]
theorem ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f g : E →SLᵤ[σ, 𝔖] F}
    (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance instContinuousSemilinearMapClass [TopologicalSpace F] (𝔖 : Set (Set E)) :
    ContinuousSemilinearMapClass (E →SLᵤ[σ, 𝔖] F) σ E F :=
  inferInstanceAs <| ContinuousSemilinearMapClass (E →SL[σ] F) σ E F

instance instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    TopologicalSpace (E →SLᵤ[σ, 𝔖] F) :=
  (@UniformOnFun.topologicalSpace E F (IsTopologicalAddGroup.rightUniformSpace F) 𝔖).induced
    (DFunLike.coe : (E →SLᵤ[σ, 𝔖] F) → (E →ᵤ[𝔖] F))

theorem topologicalSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    instTopologicalSpace σ F 𝔖 = TopologicalSpace.induced (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe)
      (UniformOnFun.topologicalSpace E F 𝔖) := by
  rw [instTopologicalSpace]
  congr
  exact IsUniformAddGroup.rightUniformSpace_eq

/-- The uniform structure associated with `ContinuousLinearMap.strongTopology`. We make sure
that this has nice definitional properties. -/
instance instUniformSpace [UniformSpace F] [IsUniformAddGroup F]
    (𝔖 : Set (Set E)) : UniformSpace (E →SLᵤ[σ, 𝔖] F) :=
  UniformSpace.replaceTopology
    ((UniformOnFun.uniformSpace E F 𝔖).comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe))
    (by
      rw [UniformConvergenceCLM.instTopologicalSpace, IsUniformAddGroup.rightUniformSpace_eq]; rfl)

theorem uniformSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    instUniformSpace σ F 𝔖 =
      UniformSpace.comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe)
        (UniformOnFun.uniformSpace E F 𝔖) := by
  rw [instUniformSpace, UniformSpace.replaceTopology_eq]

@[simp]
theorem uniformity_toTopologicalSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    (UniformConvergenceCLM.instUniformSpace σ F 𝔖).toTopologicalSpace =
      UniformConvergenceCLM.instTopologicalSpace σ F 𝔖 :=
  rfl

theorem isUniformInducing_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformInducing (α := E →SLᵤ[σ, 𝔖] F) (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  ⟨rfl⟩

theorem isUniformEmbedding_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformEmbedding (α := E →SLᵤ[σ, 𝔖] F) (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  ⟨isUniformInducing_coeFn .., DFunLike.coe_injective⟩

theorem isEmbedding_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsEmbedding (X := E →SLᵤ[σ, 𝔖] F) (Y := E →ᵤ[𝔖] F)
      (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  IsUniformEmbedding.isEmbedding (isUniformEmbedding_coeFn _ _ _)

instance instAddCommGroup [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    AddCommGroup (E →SLᵤ[σ, 𝔖] F) :=
  inferInstanceAs <| AddCommGroup (E →SL[σ] F)

@[simp]
theorem neg_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    (f : E →SLᵤ[σ, 𝔖] F) (x : E) : (-f) x = -f x :=
  rfl

@[simp]
theorem add_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    (f g : E →SLᵤ[σ, 𝔖] F) (x : E) : (f + g) x = f x + g x :=
  rfl

@[simp]
theorem sum_apply {ι : Type*} [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    (t : Finset ι) (f : ι → E →SLᵤ[σ, 𝔖] F) (x : E) :
    (∑ d ∈ t, f d) x = ∑ d ∈ t, (f d) x :=
  ContinuousLinearMap.sum_apply t f x

@[simp]
theorem sub_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    (f g : E →SLᵤ[σ, 𝔖] F) (x : E) : (f - g) x = f x - g x :=
  rfl

@[simp]
theorem coe_zero [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    ⇑(0 : E →SLᵤ[σ, 𝔖] F) = 0 :=
  rfl

instance instIsUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformAddGroup (E →SLᵤ[σ, 𝔖] F) := by
  let φ : (E →SLᵤ[σ, 𝔖] F) →+ E →ᵤ[𝔖] F :=
    ⟨⟨(DFunLike.coe : (E →SLᵤ[σ, 𝔖] F) → E →ᵤ[𝔖] F), rfl⟩, fun _ _ => rfl⟩
  exact (isUniformEmbedding_coeFn _ _ _).isUniformAddGroup φ

instance instIsTopologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) : IsTopologicalAddGroup (E →SLᵤ[σ, 𝔖] F) := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  infer_instance

theorem continuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) :
    ContinuousEvalConst (E →SLᵤ[σ, 𝔖] F) E F where
  continuous_eval_const x := by
    letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    exact (UniformOnFun.uniformContinuous_eval h𝔖 x).continuous.comp
      (isEmbedding_coeFn σ F 𝔖).continuous

theorem t2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = univ) : T2Space (E →SLᵤ[σ, 𝔖] F) := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  haveI : T2Space (E →ᵤ[𝔖] F) := UniformOnFun.t2Space_of_covering h𝔖
  exact (isEmbedding_coeFn σ F 𝔖).t2Space

instance instDistribMulAction (M : Type*) [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    DistribMulAction M (E →SLᵤ[σ, 𝔖] F) :=
  inferInstanceAs <| DistribMulAction M (E →SL[σ] F)

@[simp]
theorem smul_apply {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E))
    (c : M) (f : E →SLᵤ[σ, 𝔖] F) (x : E) :
    (c • f) x = c • f x :=
  rfl

instance instModule (R : Type*) [Semiring R] [Module R F] [SMulCommClass 𝕜₂ R F]
    [TopologicalSpace F] [ContinuousConstSMul R F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    Module R (E →SLᵤ[σ, 𝔖] F) :=
  inferInstanceAs <| Module R (E →SL[σ] F)

theorem continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] (𝔖 : Set (Set E))
    (h𝔖₃ : ∀ S ∈ 𝔖, IsVonNBounded 𝕜₁ S) :
    ContinuousSMul 𝕜₂ (E →SLᵤ[σ, 𝔖] F) := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let φ : (E →SLᵤ[σ, 𝔖] F) →ₗ[𝕜₂] E → F :=
    ⟨⟨DFunLike.coe, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  exact UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜₂ E F (E →SLᵤ[σ, 𝔖] F) φ
    ⟨rfl⟩ fun u s hs => (h𝔖₃ s hs).image u

theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop}
    {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SLᵤ[σ, 𝔖] F)).HasBasis
      (fun Si : Set E × ι => Si.1 ∈ 𝔖 ∧ p Si.2)
      fun Si => { f : E →SLᵤ[σ, 𝔖] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [(isEmbedding_coeFn σ F 𝔖).isInducing.nhds_eq_comap]
  exact (UniformOnFun.hasBasis_nhds_zero_of_basis 𝔖 h𝔖₁ h𝔖₂ h).comap DFunLike.coe

theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 (0 : E →SLᵤ[σ, 𝔖] F)).HasBasis
      (fun SV : Set E × Set F => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 0 : Filter F)) fun SV =>
      { f : E →SLᵤ[σ, 𝔖] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  hasBasis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ (𝓝 0).basis_sets

theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E →SLᵤ[σ, 𝔖] F) =
      ⨅ (s : Set E) (_ : s ∈ 𝔖) (i : ι) (_ : p i),
        𝓟 {f : E →SLᵤ[σ, 𝔖] F | MapsTo f s (b i)} := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [(isEmbedding_coeFn σ F 𝔖).isInducing.nhds_eq_comap,
    UniformOnFun.nhds_eq_of_basis _ _ h.uniformity_of_nhds_zero]
  simp [MapsTo]

theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    𝓝 (0 : E →SLᵤ[σ, 𝔖] F) =
      ⨅ s ∈ 𝔖, ⨅ t ∈ 𝓝 (0 : F),
        𝓟 {f : E →SLᵤ[σ, 𝔖] F | MapsTo f s t} :=
  nhds_zero_eq_of_basis _ _ _ (𝓝 0).basis_sets

variable {F} in
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {𝔖 : Set (Set E)} {s : Set E} (hs : s ∈ 𝔖) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : E →SLᵤ[σ, 𝔖] F in 𝓝 0, MapsTo f s U := by
  rw [nhds_zero_eq]
  apply_rules [mem_iInf_of_mem, mem_principal_self]

variable {σ F} in
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [DistribMulAction R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {𝔖 : Set (Set E)} {S : Set (E →SLᵤ[σ, 𝔖] F)} (hS : IsVonNBounded R S)
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
    {𝔖 : Set (Set E)} {S : Set (E →SLᵤ[σ, 𝔖] F)} :
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
    [UniformSpace F] [IsUniformAddGroup F] [UniformContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    UniformContinuousConstSMul M (E →SLᵤ[σ, 𝔖] F) :=
  (isUniformInducing_coeFn σ F 𝔖).uniformContinuousConstSMul fun _ _ ↦ by rfl

instance instContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    ContinuousConstSMul M (E →SLᵤ[σ, 𝔖] F) :=
  let _ := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have _ := uniformContinuousConstSMul_of_continuousConstSMul M F
  inferInstance

theorem tendsto_iff_tendstoUniformlyOn {ι : Type*} {p : Filter ι} [UniformSpace F]
    [IsUniformAddGroup F] (𝔖 : Set (Set E)) {a : ι → E →SLᵤ[σ, 𝔖] F}
    {a₀ : E →SLᵤ[σ, 𝔖] F} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ s ∈ 𝔖, TendstoUniformlyOn (a · ·) a₀ p s := by
  rw [(isEmbedding_coeFn σ F 𝔖).tendsto_nhds_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rfl

variable {F} in
theorem isUniformInducing_postcomp
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [IsUniformAddGroup F]
    (g : F →SL[τ] G) (hg : IsUniformInducing g) (𝔖 : Set (Set E)) :
    IsUniformInducing (α := E →SLᵤ[σ, 𝔖] F) (β := E →SLᵤ[ρ, 𝔖] G)
      g.comp := by
  rw [← (isUniformInducing_coeFn _ _ _).of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp (isUniformInducing_coeFn _ _ _)

variable {F} in
theorem isUniformEmbedding_postcomp
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [IsUniformAddGroup F]
    (g : F →SL[τ] G) (hg : IsUniformEmbedding g) (𝔖 : Set (Set E)) :
    IsUniformEmbedding (α := E →SLᵤ[σ, 𝔖] F) (β := E →SLᵤ[ρ, 𝔖] G)
      g.comp :=
  .mk (isUniformInducing_postcomp _ g hg.isUniformInducing _) fun _ _ ↦ g.cancel_left hg.injective

theorem completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    {𝔖 : Set (Set E)} (h𝔖 : IsCoherentWith 𝔖) (h𝔖U : ⋃₀ 𝔖 = univ) :
    CompleteSpace (E →SLᵤ[σ, 𝔖] F) := by
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

theorem uniformSpace_mono [UniformSpace F] [IsUniformAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instUniformSpace σ F 𝔖₁ ≤ instUniformSpace σ F 𝔖₂ := by
  simp_rw [uniformSpace_eq]
  exact UniformSpace.comap_mono (UniformOnFun.mono (le_refl _) h)

theorem topologicalSpace_mono [TopologicalSpace F] [IsTopologicalAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instTopologicalSpace σ F 𝔖₁ ≤ instTopologicalSpace σ F 𝔖₂ := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  simp_rw [← uniformity_toTopologicalSpace_eq]
  exact UniformSpace.toTopologicalSpace_mono (uniformSpace_mono σ F h)

variable {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {σ : 𝕜₁ →+* 𝕜₂} [Module 𝕜₁ E] in
variable {F} in
/-- Let `𝔖` be a family of bounded subsets of `F`, and `B : E × F → G` a bilinear map.
If `B` is (jointly) continuous, then it is `𝔖`-**hypocontinuous**:
in curried form, it defines a continuous linear map `E →L[𝕜] (F →Lᵤ[𝕜, 𝔖] G)`.

Note that, in full generality, the converse is not true.
See also `ContinuousLinearMap.continuous_of_continuous_uncurry`. -/
protected theorem continuous_of_continuous_uncurry [AddCommGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₃ →+* 𝕜₂} [RingHomSurjective τ]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    {𝔖 : Set (Set E)} (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜₁ s)
    (B : G →ₛₗ[τ] (E →SLᵤ[σ, 𝔖] F))
    (hB : Continuous (fun p : G × E ↦ B p.1 p.2)) :
    Continuous B := by
  apply continuous_of_tendsto_nhds_zero
  suffices ∀ s ∈ 𝔖, ∀ U ∈ 𝓝 0, ∀ᶠ (g : G) in 𝓝 0, ∀ e ∈ s, B g e ∈ U by
    simpa [UniformConvergenceCLM.nhds_zero_eq, MapsTo]
  intro S hS U hU
  rcases mem_nhds_prod_iff.mp <| hB.tendsto' (0 : G × E) 0 (by simp) hU
    with ⟨V, hV, W, hW, hVW⟩
  rcases (h𝔖 S hS) hW |>.eventually_nhdsNE_zero.and eventually_mem_nhdsWithin |>.exists with
    ⟨c, hc, c_ne : c ≠ 0⟩
  rcases RingHom.surjective τ (σ c) with ⟨d, hd⟩
  have d_ne : d ≠ 0 := by rwa [← map_ne_zero τ, hd, map_ne_zero σ]
  filter_upwards [(set_smul_mem_nhds_zero_iff d_ne).mpr hV]
  rintro _ ⟨a, ha, rfl⟩ x hx
  rw [map_smulₛₗ, hd, UniformConvergenceCLM.smul_apply, ← map_smulₛₗ]
  exact @hVW ⟨_, _⟩ ⟨ha, hc hx⟩

section Equiv

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] (𝔖 : Set (Set E))

/-- The linear equivalence that maps a continuous linear map to the type copy endowed with the
uniform convergence topology. -/
def _root_.ContinuousLinearMap.toUniformConvergenceCLM :
    (E →SL[σ] F) ≃ₗ[𝕜₂] E →SLᵤ[σ, 𝔖] F where
  __ := LinearEquiv.refl _ _

variable {σ F 𝔖}

@[simp]
lemma _root_.ContinuousLinearMap.toUniformConvergenceCLM_apply {A : E →SL[σ] F} {x : E} :
    ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖 A x = A x := rfl

@[simp]
lemma _root_.ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
    {A : E →SLᵤ[σ, 𝔖] F} {x : E} :
    (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖).symm A x = A x := rfl

end Equiv

end UniformConvergenceCLM

namespace ContinuousLinearMap

open scoped UniformConvergenceCLM

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

variable (𝔖 : Set (Set E)) (𝔗 : Set (Set F))

variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map for the uniform
convergence topology. -/
@[simps]
def precompUniformConvergenceCLM [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    (L : E →SL[σ] F) (hL : MapsTo (L '' ·) 𝔖 𝔗) :
    (F →SLᵤ[τ, 𝔗] G) →L[𝕜₃] (E →SLᵤ[ρ, 𝔖] G) where
  toFun f := f.comp L
  map_add' f g := add_comp f g L
  map_smul' a f := smul_comp a f L
  cont := by
    letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
    rw [(UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous_iff]
    exact (UniformOnFun.precomp_uniformContinuous hL).continuous.comp
        (UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous

@[deprecated (since := "2026-01-27")]
alias precomp_uniformConvergenceCLM := precompUniformConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias precomp_uniformConvergenceCLM_apply := precompUniformConvergenceCLM_apply

/-- Post-composition by a *fixed* continuous linear map as a continuous linear map for the uniform
convergence topology. -/
@[simps]
def postcompUniformConvergenceCLM [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) :
    (E →SLᵤ[σ, 𝔖] F) →SL[τ] (E →SLᵤ[ρ, 𝔖] G) where
  toFun f := L.comp f
  map_add' := comp_add L
  map_smul' := comp_smulₛₗ L
  cont := by
    letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
    letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    rw [(UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous_iff]
    exact
      (UniformOnFun.postcomp_uniformContinuous L.uniformContinuous).continuous.comp
        (UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous

@[deprecated (since := "2026-01-27")]
alias postcomp_uniformConvergenceCLM := postcompUniformConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias postcomp_uniformConvergenceCLM_apply := postcompUniformConvergenceCLM_apply

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

open scoped UniformConvergenceCLM

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₄ H]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. This version is for the type alias
`UniformConvergenceCLM`. -/
def uniformConvergenceCLMCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁₂ ⁻¹' t ∈ 𝔖) :
    (E →SLᵤ[σ₁₄, 𝔖] H) ≃SL[σ₄₃] (F →SLᵤ[σ₂₃, 𝔗] G) :=
  haveI mapsto₁ : MapsTo (e₁₂ '' ·) 𝔖 𝔗 := fun s ↦ by simp [h, preimage_image_eq _ e₁₂.injective]
  haveI mapsto₂ : MapsTo (e₁₂.symm '' ·) 𝔗 𝔖 := fun t ↦ by simp [h, e₁₂.image_symm_eq_preimage]
  { e₁₂.arrowCongrEquivₛₗ e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
    continuous_toFun := ((postcompUniformConvergenceCLM _ e₄₃.toContinuousLinearMap).comp
      (precompUniformConvergenceCLM H _ _ e₁₂.symm.toContinuousLinearMap mapsto₂)).continuous
    continuous_invFun :=
      ((precompUniformConvergenceCLM H _ _ e₁₂.toContinuousLinearMap mapsto₁).comp
        (postcompUniformConvergenceCLM _ e₄₃.symm.toContinuousLinearMap)).continuous }

@[simp]
lemma uniformConvergenceCLMCongrSL_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁₂ ⁻¹' t ∈ 𝔖) (φ : E →SLᵤ[σ₁₄, 𝔖] H) (f : F) :
    uniformConvergenceCLMCongrSL e₁₂ e₄₃ 𝔖 𝔗 h φ f = e₄₃ (φ (e₁₂.symm f)) :=
  rfl

@[simp]
lemma uniformConvergenceCLMCongrSL_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁₂ ⁻¹' t ∈ 𝔖) (φ : F →SLᵤ[σ₂₃, 𝔗] G) (e : E) :
    (uniformConvergenceCLMCongrSL e₁₂ e₄₃ 𝔖 𝔗 h).symm φ e = e₄₃.symm (φ (e₁₂ e)) :=
  rfl

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*}
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. This version is for the type alias
`UniformConvergenceCLM`. -/
def uniformConvergenceCLMCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁ ⁻¹' t ∈ 𝔖) :
    (E →Lᵤ[𝕜, 𝔖] H) ≃L[𝕜] (F →Lᵤ[𝕜, 𝔗] G) :=
  e₁.uniformConvergenceCLMCongrSL e₂ 𝔖 𝔗 h

@[simp]
lemma uniformConvergenceCLMCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁ ⁻¹' t ∈ 𝔖) (φ : E →Lᵤ[𝕜, 𝔖] H) (f : F) :
    uniformConvergenceCLMCongr e₁ e₂ 𝔖 𝔗 h φ f = e₂ (φ (e₁.symm f)) :=
  rfl

@[simp]
lemma uniformConvergenceCLMCongr_symm_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁ ⁻¹' t ∈ 𝔖) (φ : F →Lᵤ[𝕜, 𝔗] G) (e : E) :
    (uniformConvergenceCLMCongr e₁ e₂ 𝔖 𝔗 h).symm φ e = e₂.symm (φ (e₁ e)) :=
  rfl

end Linear

section Pi

open scoped UniformConvergenceCLM

variable (𝕜 : Type*) [NormedField 𝕜] {E ι : Type*} (F : ι → Type*)
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜 (F i)]

/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →Lᵤ[𝕜, 𝔖] F i` and `E →Lᵤ[𝕜, 𝔖] Π i, F i`. -/
def UniformConvergenceCLM.piEquivL (𝔖 : Set (Set E)) :
    (Π i, E →Lᵤ[𝕜, 𝔖] F i) ≃L[𝕜] (E →Lᵤ[𝕜, 𝔖] Π i, F i) :=
  letI : ∀ i, UniformSpace (F i) := fun i ↦ IsTopologicalAddGroup.rightUniformSpace (F i)
  haveI : ∀ i, IsUniformAddGroup (F i) := fun i ↦ isUniformAddGroup_of_addCommGroup
  { toFun F := ContinuousLinearMap.pi F
    invFun f i := (ContinuousLinearMap.proj i).comp f
    map_add' _ _ := by ext; rfl
    map_smul' _ _ := by ext; rfl
    left_inv _ := by ext; rfl
    right_inv _ := by ext; rfl
    continuous_toFun := by
      rw [UniformConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff]
      rw [UniformOnFun.uniformEquivPiComm _ _ |>.isUniformEmbedding.isEmbedding.continuous_iff]
      refine continuous_pi fun i ↦ ?_
      exact UniformConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous.comp (continuous_apply i)
    continuous_invFun := by
      apply continuous_pi (A := fun i ↦ E →Lᵤ[𝕜, 𝔖] F i) fun i ↦ ?_
      exact (ContinuousLinearMap.proj i : (Π j, F j) →L[𝕜] F i).postcompUniformConvergenceCLM 𝔖
        |>.continuous}

@[simp]
lemma UniformConvergenceCLM.piEquivL_apply (𝔖 : Set (Set E))
    (T : Π i, E →Lᵤ[𝕜, 𝔖] F i) (e : E) (i : ι) :
    piEquivL 𝕜 F 𝔖 T e i = T i e :=
  rfl

@[simp]
lemma UniformConvergenceCLM.piEquivL_symm_apply (𝔖 : Set (Set E))
    (T : E →Lᵤ[𝕜, 𝔖] Π i, F i) (e : E) (i : ι) :
    (piEquivL 𝕜 F 𝔖).symm T i e = T e i :=
  rfl

end Pi

end ContinuousLinearEquiv
