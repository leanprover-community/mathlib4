/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Yury Kudryashov
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Compact convergence (uniform convergence on compact sets)

Given a topological space `α` and a uniform space `β` (e.g., a metric space or a topological group),
the space of continuous maps `C(α, β)` carries a natural uniform space structure.
We define this uniform space structure in this file
and also prove its basic properties.

## Main definitions

- `ContinuousMap.toUniformOnFunIsCompact`:
  natural embedding of `C(α, β)`
  into the space `α →ᵤ[{K | IsCompact K}] β` of all maps `α → β`
  with the uniform space structure of uniform convergence on compacts.

- `ContinuousMap.compactConvergenceUniformSpace`:
  the `UniformSpace` structure on `C(α, β)` induced by the map above.

## Main results

* `ContinuousMap.mem_compactConvergence_entourage_iff`:
  a characterisation of the entourages of `C(α, β)`.

  The entourages are generated by the following sets.
  Given `K : Set α` and `V : Set (β × β)`,
  let `E(K, V) : Set (C(α, β) × C(α, β))` be the set of pairs of continuous functions `α → β`
  which are `V`-close on `K`:
  $$
    E(K, V) = \{ (f, g) | ∀ (x ∈ K), (f x, g x) ∈ V \}.
  $$
  Then the sets `E(K, V)` for all compact sets `K` and all entourages `V`
  form a basis of entourages of `C(α, β)`.

  As usual, this basis of entourages provides a basis of neighbourhoods
  by fixing `f`, see `nhds_basis_uniformity'`.

* `Filter.HasBasis.compactConvergenceUniformity`:
  a similar statement that uses a basis of entourages of `β` instead of all entourages.
  It is useful, e.g., if `β` is a metric space.

* `ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn`:
  a sequence of functions `Fₙ` in `C(α, β)` converges in the compact-open topology to some `f`
  iff `Fₙ` converges to `f` uniformly on each compact subset `K` of `α`.

* Topology induced by the uniformity described above agrees with the compact-open topology.
  This is essentially the same as `ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn`.

  This fact is not available as a separate theorem.
  Instead, we override the projection of `ContinuousMap.compactConvergenceUniformity`
  to `TopologicalSpace` to be `ContinuousMap.compactOpen` and prove that they agree,
  see Note [forgetful inheritance] and implementation notes below.

* `ContinuousMap.tendsto_iff_tendstoLocallyUniformly`:
  on a weakly locally compact space,
  a sequence of functions `Fₙ` in `C(α, β)` converges to some `f`
  iff `Fₙ` converges to `f` locally uniformly.

* `ContinuousMap.tendsto_iff_tendstoUniformly`:
  on a compact space, a sequence of functions `Fₙ` in `C(α, β)` converges to some `f`
  iff `Fₙ` converges to `f` uniformly.

## Implementation details

For technical reasons (see Note [forgetful inheritance]),
instead of defining a `UniformSpace C(α, β)` structure
and proving in a theorem that it agrees with the compact-open topology,
we override the projection right in the definition,
so that the resulting instance uses the compact-open topology.

## TODO

* Results about uniformly continuous functions `γ → C(α, β)`
  and uniform limits of sequences `ι → γ → C(α, β)`.
-/


universe u₁ u₂ u₃

open scoped Uniformity Topology UniformConvergence

open UniformSpace Set Filter

variable {α : Type u₁} {β : Type u₂} [TopologicalSpace α] [UniformSpace β]
variable (K : Set α) (V : Set (β × β)) (f : C(α, β))

namespace ContinuousMap

/-- Compact-open topology on `C(α, β)` agrees with the topology of uniform convergence on compacts:
a family of continuous functions `F i` tends to `f` in the compact-open topology
if and only if the `F i` tends to `f` uniformly on all compact sets. -/
theorem tendsto_iff_forall_compact_tendstoUniformlyOn
    {ι : Type u₃} {p : Filter ι} {F : ι → C(α, β)} {f} :
    Tendsto F p (𝓝 f) ↔ ∀ K, IsCompact K → TendstoUniformlyOn (fun i a => F i a) f p K := by
  rw [tendsto_nhds_compactOpen]
  constructor
  · -- Let us prove that convergence in the compact-open topology
    -- implies uniform convergence on compacts.
    -- Consider a compact set `K`
    intro h K hK
    -- Since `K` is compact, it suffices to prove locally uniform convergence
    rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
    -- Now choose an entourage `U` in the codomain and a point `x ∈ K`.
    intro U hU x _
    -- Choose an open symmetric entourage `V` such that `V ○ V ⊆ U`.
    rcases comp_open_symm_mem_uniformity_sets hU with ⟨V, hV, hVo, hVsymm, hVU⟩
    -- Then choose a closed entourage `W ⊆ V`
    rcases mem_uniformity_isClosed hV with ⟨W, hW, hWc, hWU⟩
    -- Consider `s = {y ∈ K | (f x, f y) ∈ W}`
    set s := K ∩ f ⁻¹' ball (f x) W
    -- This is a neighbourhood of `x` within `K`, because `W` is an entourage.
    have hnhds : s ∈ 𝓝[K] x := inter_mem_nhdsWithin _ <| f.continuousAt _ (ball_mem_nhds _ hW)
    -- This set is compact because it is an intersection of `K`
    -- with a closed set `{y | (f x, f y) ∈ W} = f ⁻¹' UniformSpace.ball (f x) W`
    have hcomp : IsCompact s := hK.inter_right <| (isClosed_ball _ hWc).preimage f.continuous
    -- `f` maps `s` to the open set `ball (f x) V = {z | (f x, z) ∈ V}`
    have hmaps : MapsTo f s (ball (f x) V) := fun x hx ↦ hWU hx.2
    use s, hnhds
    -- Continuous maps `F i` in a neighbourhood of `f` map `s` to `ball (f x) V` as well.
    refine (h s hcomp _ (isOpen_ball _ hVo) hmaps).mono fun g hg y hy ↦ ?_
    -- Then for `y ∈ s` we have `(f y, f x) ∈ V` and `(f x, F i y) ∈ V`, thus `(f y, F i y) ∈ U`
    exact hVU ⟨f x, hVsymm.mk_mem_comm.2 <| hmaps hy, hg hy⟩
  · -- Now we prove that uniform convergence on compacts
    -- implies convergence in the compact-open topology
    -- Consider a compact set `K`, an open set `U`, and a continuous map `f` that maps `K` to `U`
    intro h K hK U hU hf
    -- Due to Lebesgue number lemma, there exists an entourage `V`
    -- such that `U` includes the `V`-thickening of `f '' K`.
    rcases lebesgue_number_of_compact_open (hK.image (map_continuous f)) hU hf.image_subset
        with ⟨V, hV, -, hVf⟩
    -- Then any continuous map that is uniformly `V`-close to `f` on `K`
    -- maps `K` to `U` as well
    filter_upwards [h K hK V hV] with g hg x hx using hVf _ (mem_image_of_mem f hx) (hg x hx)

/-- Interpret a bundled continuous map as an element of `α →ᵤ[{K | IsCompact K}] β`.

We use this map to induce the `UniformSpace` structure on `C(α, β)`. -/
def toUniformOnFunIsCompact (f : C(α, β)) : α →ᵤ[{K | IsCompact K}] β :=
  UniformOnFun.ofFun {K | IsCompact K} f

@[simp]
theorem toUniformOnFun_toFun (f : C(α, β)) :
    UniformOnFun.toFun _ f.toUniformOnFunIsCompact = f := rfl

theorem range_toUniformOnFunIsCompact :
    range (toUniformOnFunIsCompact) = {f : UniformOnFun α β {K | IsCompact K} | Continuous f} :=
  Set.ext fun f ↦ ⟨fun g ↦ g.choose_spec ▸ g.choose.2, fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

open UniformSpace in
/-- Uniform space structure on `C(α, β)`.

The uniformity comes from `α →ᵤ[{K | IsCompact K}] β` (i.e., `UniformOnFun α β {K | IsCompact K}`)
which defines topology of uniform convergence on compact sets.
We use `ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn`
to show that the induced topology agrees with the compact-open topology
and replace the topology with `compactOpen` to avoid non-defeq diamonds,
see Note [forgetful inheritance]. -/
instance compactConvergenceUniformSpace : UniformSpace C(α, β) :=
  .replaceTopology (.comap toUniformOnFunIsCompact inferInstance) <| by
    refine TopologicalSpace.ext_nhds fun f ↦ eq_of_forall_le_iff fun l ↦ ?_
    simp_rw [← tendsto_id', tendsto_iff_forall_compact_tendstoUniformlyOn,
      nhds_induced, tendsto_comap_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    rfl

theorem isUniformEmbedding_toUniformOnFunIsCompact :
    IsUniformEmbedding (toUniformOnFunIsCompact : C(α, β) → α →ᵤ[{K | IsCompact K}] β) where
  comap_uniformity := rfl
  inj := DFunLike.coe_injective

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_toUniformOnFunIsCompact := isUniformEmbedding_toUniformOnFunIsCompact

-- The following definitions and theorems
-- used to be a part of the construction of the `UniformSpace C(α, β)` structure
-- before it was migrated to `UniformOnFun`

theorem _root_.Filter.HasBasis.compactConvergenceUniformity {ι : Type*} {pi : ι → Prop}
    {s : ι → Set (β × β)} (h : (𝓤 β).HasBasis pi s) :
    HasBasis (𝓤 C(α, β)) (fun p : Set α × ι => IsCompact p.1 ∧ pi p.2) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ s p.2 } := by
  rw [← isUniformEmbedding_toUniformOnFunIsCompact.comap_uniformity]
  exact .comap _ <| UniformOnFun.hasBasis_uniformity_of_basis _ _ {K | IsCompact K}
    ⟨∅, isCompact_empty⟩ (directedOn_of_sup_mem fun _ _ ↦ IsCompact.union) h

theorem hasBasis_compactConvergenceUniformity :
    HasBasis (𝓤 C(α, β)) (fun p : Set α × Set (β × β) => IsCompact p.1 ∧ p.2 ∈ 𝓤 β) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ p.2 } :=
  (basis_sets _).compactConvergenceUniformity

theorem mem_compactConvergence_entourage_iff (X : Set (C(α, β) × C(α, β))) :
    X ∈ 𝓤 C(α, β) ↔
      ∃ (K : Set α) (V : Set (β × β)), IsCompact K ∧ V ∈ 𝓤 β ∧
        { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V } ⊆ X := by
  simp [hasBasis_compactConvergenceUniformity.mem_iff, and_assoc]

/-- If `K` is a compact exhaustion of `α`
and `V i` bounded by `p i` is a basis of entourages of `β`,
then `fun (n, i) ↦ {(f, g) | ∀ x ∈ K n, (f x, g x) ∈ V i}` bounded by `p i`
is a basis of entourages of `C(α, β)`. -/
theorem _root_.CompactExhaustion.hasBasis_compactConvergenceUniformity {ι : Type*}
    {p : ι → Prop} {V : ι → Set (β × β)} (K : CompactExhaustion α) (hb : (𝓤 β).HasBasis p V) :
    HasBasis (𝓤 C(α, β)) (fun i : ℕ × ι ↦ p i.2) fun i ↦
      {fg | ∀ x ∈ K i.1, (fg.1 x, fg.2 x) ∈ V i.2} :=
  (UniformOnFun.hasBasis_uniformity_of_covering_of_basis {K | IsCompact K} K.isCompact
    (Monotone.directed_le K.subset) (fun _ ↦ K.exists_superset_of_isCompact) hb).comap _

theorem _root_.CompactExhaustion.hasAntitoneBasis_compactConvergenceUniformity
    {V : ℕ → Set (β × β)} (K : CompactExhaustion α) (hb : (𝓤 β).HasAntitoneBasis V) :
    HasAntitoneBasis (𝓤 C(α, β)) fun n ↦ {fg | ∀ x ∈ K n, (fg.1 x, fg.2 x) ∈ V n} :=
  (UniformOnFun.hasAntitoneBasis_uniformity {K | IsCompact K} K.isCompact
    K.subset (fun _ ↦ K.exists_superset_of_isCompact) hb).comap _

/-- If `α` is a weakly locally compact σ-compact space
(e.g., a proper pseudometric space or a compact spaces)
and the uniformity on `β` is pseudometrizable,
then the uniformity on `C(α, β)` is pseudometrizable too.
-/
instance [WeaklyLocallyCompactSpace α] [SigmaCompactSpace α] [IsCountablyGenerated (𝓤 β)] :
    IsCountablyGenerated (𝓤 (C(α, β))) :=
  let ⟨_V, hV⟩ := exists_antitone_basis (𝓤 β)
  ((CompactExhaustion.choice α).hasAntitoneBasis_compactConvergenceUniformity
    hV).isCountablyGenerated

variable {ι : Type u₃} {p : Filter ι} {F : ι → C(α, β)} {f}

/-- Locally uniform convergence implies convergence in the compact-open topology. -/
theorem tendsto_of_tendstoLocallyUniformly (h : TendstoLocallyUniformly (fun i a => F i a) f p) :
    Tendsto F p (𝓝 f) := by
  rw [tendsto_iff_forall_compact_tendstoUniformlyOn]
  intro K hK
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
  exact h.tendstoLocallyUniformlyOn

/-- In a weakly locally compact space,
convergence in the compact-open topology is the same as locally uniform convergence.

The right-to-left implication holds in any topological space,
see `ContinuousMap.tendsto_of_tendstoLocallyUniformly`. -/
theorem tendsto_iff_tendstoLocallyUniformly [WeaklyLocallyCompactSpace α] :
    Tendsto F p (𝓝 f) ↔ TendstoLocallyUniformly (fun i a => F i a) f p := by
  refine ⟨fun h V hV x ↦ ?_, tendsto_of_tendstoLocallyUniformly⟩
  rw [tendsto_iff_forall_compact_tendstoUniformlyOn] at h
  obtain ⟨n, hn₁, hn₂⟩ := exists_compact_mem_nhds x
  exact ⟨n, hn₂, h n hn₁ V hV⟩

section Functorial

variable {γ δ : Type*} [TopologicalSpace γ] [UniformSpace δ]

theorem uniformContinuous_comp (g : C(β, δ)) (hg : UniformContinuous g) :
    UniformContinuous (ContinuousMap.comp g : C(α, β) → C(α, δ)) :=
  isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous_iff.mpr <|
    UniformOnFun.postcomp_uniformContinuous hg |>.comp
      isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous

theorem isUniformInducing_comp (g : C(β, δ)) (hg : IsUniformInducing g) :
    IsUniformInducing (ContinuousMap.comp g : C(α, β) → C(α, δ)) :=
  isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing.of_comp_iff.mp <|
    UniformOnFun.postcomp_isUniformInducing hg |>.comp
      isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing

@[deprecated (since := "2024-10-05")]
alias uniformInducing_comp := isUniformInducing_comp

theorem isUniformEmbedding_comp (g : C(β, δ)) (hg : IsUniformEmbedding g) :
    IsUniformEmbedding (ContinuousMap.comp g : C(α, β) → C(α, δ)) :=
  isUniformEmbedding_toUniformOnFunIsCompact.of_comp_iff.mp <|
    UniformOnFun.postcomp_isUniformEmbedding hg |>.comp
      isUniformEmbedding_toUniformOnFunIsCompact

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_comp := isUniformEmbedding_comp

theorem uniformContinuous_comp_left (g : C(α, γ)) :
    UniformContinuous (fun f ↦ f.comp g : C(γ, β) → C(α, β)) :=
  isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous_iff.mpr <|
    UniformOnFun.precomp_uniformContinuous (fun _ hK ↦ hK.image g.continuous) |>.comp
      isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous

/-- Any pair of a homeomorphism `X ≃ₜ Z` and an isomorphism `Y ≃ᵤ T` of uniform spaces gives rise
to an isomorphism `C(X, Y) ≃ᵤ C(Z, T)`. -/
protected def _root_.UniformEquiv.arrowCongr (φ : α ≃ₜ γ) (ψ : β ≃ᵤ δ) :
    C(α, β) ≃ᵤ C(γ, δ) where
  toFun f := .comp ψ.toHomeomorph <| f.comp φ.symm
  invFun f := .comp ψ.symm.toHomeomorph <| f.comp φ
  left_inv f := ext fun _ ↦ ψ.left_inv (f _) |>.trans <| congrArg f <| φ.left_inv _
  right_inv f := ext fun _ ↦ ψ.right_inv (f _) |>.trans <| congrArg f <| φ.right_inv _
  uniformContinuous_toFun := uniformContinuous_comp _ ψ.uniformContinuous |>.comp <|
    uniformContinuous_comp_left _
  uniformContinuous_invFun := uniformContinuous_comp _ ψ.symm.uniformContinuous |>.comp <|
    uniformContinuous_comp_left _

end Functorial

section CompactDomain

variable [CompactSpace α]

theorem hasBasis_compactConvergenceUniformity_of_compact :
    HasBasis (𝓤 C(α, β)) (fun V : Set (β × β) => V ∈ 𝓤 β) fun V =>
      { fg : C(α, β) × C(α, β) | ∀ x, (fg.1 x, fg.2 x) ∈ V } :=
  hasBasis_compactConvergenceUniformity.to_hasBasis
    (fun p hp => ⟨p.2, hp.2, fun _fg hfg x _hx => hfg x⟩) fun V hV =>
    ⟨⟨univ, V⟩, ⟨isCompact_univ, hV⟩, fun _fg hfg x => hfg x (mem_univ x)⟩

/-- Convergence in the compact-open topology is the same as uniform convergence for sequences of
continuous functions on a compact space. -/
theorem tendsto_iff_tendstoUniformly :
    Tendsto F p (𝓝 f) ↔ TendstoUniformly (fun i a => F i a) f p := by
  rw [tendsto_iff_forall_compact_tendstoUniformlyOn, ← tendstoUniformlyOn_univ]
  exact ⟨fun h => h univ isCompact_univ, fun h K _hK => h.mono (subset_univ K)⟩

end CompactDomain

theorem uniformSpace_eq_inf_precomp_of_cover {δ₁ δ₂ : Type*} [TopologicalSpace δ₁]
    [TopologicalSpace δ₂] (φ₁ : C(δ₁, α)) (φ₂ : C(δ₂, α)) (h_proper₁ : IsProperMap φ₁)
    (h_proper₂ : IsProperMap φ₂) (h_cover : range φ₁ ∪ range φ₂ = univ) :
    (inferInstanceAs <| UniformSpace C(α, β)) =
      .comap (comp · φ₁) inferInstance ⊓
      .comap (comp · φ₂) inferInstance := by
  -- We check the analogous result for `UniformOnFun` using
  -- `UniformOnFun.uniformSpace_eq_inf_precomp_of_cover`...
  set 𝔖 : Set (Set α) := {K | IsCompact K}
  set 𝔗₁ : Set (Set δ₁) := {K | IsCompact K}
  set 𝔗₂ : Set (Set δ₂) := {K | IsCompact K}
  have h_image₁ : MapsTo (φ₁ '' ·) 𝔗₁ 𝔖 := fun K hK ↦ hK.image φ₁.continuous
  have h_image₂ : MapsTo (φ₂ '' ·) 𝔗₂ 𝔖 := fun K hK ↦ hK.image φ₂.continuous
  have h_preimage₁ : MapsTo (φ₁ ⁻¹' ·) 𝔖 𝔗₁ := fun K ↦ h_proper₁.isCompact_preimage
  have h_preimage₂ : MapsTo (φ₂ ⁻¹' ·) 𝔖 𝔗₂ := fun K ↦ h_proper₂.isCompact_preimage
  have h_cover' : ∀ S ∈ 𝔖, S ⊆ range φ₁ ∪ range φ₂ := fun S _ ↦ h_cover ▸ subset_univ _
  -- ... and we just pull it back.
  simp_rw [compactConvergenceUniformSpace, replaceTopology_eq,
    UniformOnFun.uniformSpace_eq_inf_precomp_of_cover _ _ _ _ _
      h_image₁ h_image₂ h_preimage₁ h_preimage₂ h_cover',
    UniformSpace.comap_inf, ← UniformSpace.comap_comap]
  rfl

theorem uniformSpace_eq_iInf_precomp_of_cover {δ : ι → Type*} [∀ i, TopologicalSpace (δ i)]
    (φ : Π i, C(δ i, α)) (h_proper : ∀ i, IsProperMap (φ i))
    (h_lf : LocallyFinite fun i ↦ range (φ i)) (h_cover : ⋃ i, range (φ i) = univ) :
    (inferInstanceAs <| UniformSpace C(α, β)) = ⨅ i, .comap (comp · (φ i)) inferInstance := by
  -- We check the analogous result for `UniformOnFun` using
  -- `UniformOnFun.uniformSpace_eq_iInf_precomp_of_cover`...
  set 𝔖 : Set (Set α) := {K | IsCompact K}
  set 𝔗 : Π i, Set (Set (δ i)) := fun i ↦ {K | IsCompact K}
  have h_image : ∀ i, MapsTo (φ i '' ·) (𝔗 i) 𝔖 := fun i K hK ↦ hK.image (φ i).continuous
  have h_preimage : ∀ i, MapsTo (φ i ⁻¹' ·) 𝔖 (𝔗 i) := fun i K ↦ (h_proper i).isCompact_preimage
  have h_cover' : ∀ S ∈ 𝔖, ∃ I : Set ι, I.Finite ∧ S ⊆ ⋃ i ∈ I, range (φ i) := fun S hS ↦ by
    refine ⟨{i | (range (φ i) ∩ S).Nonempty}, h_lf.finite_nonempty_inter_compact hS,
      inter_eq_right.mp ?_⟩
    simp_rw [iUnion₂_inter, mem_setOf, iUnion_nonempty_self, ← iUnion_inter, h_cover, univ_inter]
  -- ... and we just pull it back.
  simp_rw [compactConvergenceUniformSpace, replaceTopology_eq,
    UniformOnFun.uniformSpace_eq_iInf_precomp_of_cover _ _ _ h_image h_preimage h_cover',
    UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
  rfl

section CompleteSpace

variable [CompleteSpace β]

/-- If the topology on `α` is generated by its restrictions to compact sets, then the space of
continuous maps `C(α, β)` is complete (wrt the compact convergence uniformity).

Sufficient conditions on `α` to satisfy this condition are (weak) local compactness (see
`ContinuousMap.instCompleteSpaceOfWeaklyLocallyCompactSpace`) and sequential compactness (see
`ContinuousMap.instCompleteSpaceOfSequentialSpace`). -/
lemma completeSpace_of_restrictGenTopology (h : RestrictGenTopology {K : Set α | IsCompact K}) :
    CompleteSpace C(α, β) := by
  rw [completeSpace_iff_isComplete_range
    isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing,
    range_toUniformOnFunIsCompact, ← completeSpace_coe_iff_isComplete]
  exact (UniformOnFun.isClosed_setOf_continuous h).completeSpace_coe

instance instCompleteSpaceOfWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace α] :
    CompleteSpace C(α, β) :=
  completeSpace_of_restrictGenTopology RestrictGenTopology.isCompact_of_weaklyLocallyCompact

instance instCompleteSpaceOfSequentialSpace [SequentialSpace α] :
    CompleteSpace C(α, β) :=
  completeSpace_of_restrictGenTopology RestrictGenTopology.isCompact_of_seq

end CompleteSpace

end ContinuousMap
