/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module topology.uniform_space.compact_convergence
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.CompactOpen
import Mathbin.Topology.UniformSpace.UniformConvergence

/-!
# Compact convergence (uniform convergence on compact sets)

Given a topological space `α` and a uniform space `β` (e.g., a metric space or a topological group),
the space of continuous maps `C(α, β)` carries a natural uniform space structure. We define this
uniform space structure in this file and also prove the following properties of the topology it
induces on `C(α, β)`:

 1. Given a sequence of continuous functions `Fₙ : α → β` together with some continuous `f : α → β`,
    then `Fₙ` converges to `f` as a sequence in `C(α, β)` iff `Fₙ` converges to `f` uniformly on
    each compact subset `K` of `α`.
 2. Given `Fₙ` and `f` as above and suppose `α` is locally compact, then `Fₙ` converges to `f` iff
    `Fₙ` converges to `f` locally uniformly.
 3. The topology coincides with the compact-open topology.

Property 1 is essentially true by definition, 2 follows from basic results about uniform
convergence, but 3 requires a little work and uses the Lebesgue number lemma.

## The uniform space structure

Given subsets `K ⊆ α` and `V ⊆ β × β`, let `E(K, V) ⊆ C(α, β) × C(α, β)` be the set of pairs of
continuous functions `α → β` which are `V`-close on `K`:
$$
  E(K, V) = \{ (f, g) | ∀ (x ∈ K), (f x, g x) ∈ V \}.
$$
Fixing some `f ∈ C(α, β)`, let `N(K, V, f) ⊆ C(α, β)` be the set of continuous functions `α → β`
which are `V`-close to `f` on `K`:
$$
  N(K, V, f) = \{ g | ∀ (x ∈ K), (f x, g x) ∈ V \}.
$$
Using this notation we can describe the uniform space structure and the topology it induces.
Specifically:
 *  A subset `X ⊆ C(α, β) × C(α, β)` is an entourage for the uniform space structure on `C(α, β)`
    iff there exists a compact `K` and entourage `V` such that `E(K, V) ⊆ X`.
 *  A subset `Y ⊆ C(α, β)` is a neighbourhood of `f` iff there exists a compact `K` and entourage
    `V` such that `N(K, V, f) ⊆ Y`.

The topology on `C(α, β)` thus has a natural subbasis (the compact-open subbasis) and a natural
neighbourhood basis (the compact-convergence neighbourhood basis).

## Main definitions / results

 * `compact_open_eq_compact_convergence`: the compact-open topology is equal to the
   compact-convergence topology.
 * `compact_convergence_uniform_space`: the uniform space structure on `C(α, β)`.
 * `mem_compact_convergence_entourage_iff`: a characterisation of the entourages of `C(α, β)`.
 * `tendsto_iff_forall_compact_tendsto_uniformly_on`: a sequence of functions `Fₙ` in `C(α, β)`
   converges to some `f` iff `Fₙ` converges to `f` uniformly on each compact subset `K` of `α`.
 * `tendsto_iff_tendsto_locally_uniformly`: on a locally compact space, a sequence of functions
   `Fₙ` in `C(α, β)` converges to some `f` iff `Fₙ` converges to `f` locally uniformly.
 * `tendsto_iff_tendsto_uniformly`: on a compact space, a sequence of functions `Fₙ` in `C(α, β)`
   converges to some `f` iff `Fₙ` converges to `f` uniformly.

## Implementation details

We use the forgetful inheritance pattern (see Note [forgetful inheritance]) to make the topology
of the uniform space structure on `C(α, β)` definitionally equal to the compact-open topology.

## TODO

 * When `β` is a metric space, there is natural basis for the compact-convergence topology
   parameterised by triples `(K, ε, f)` for a real number `ε > 0`.
 * When `α` is compact and `β` is a metric space, the compact-convergence topology (and thus also
   the compact-open topology) is metrisable.
 * Results about uniformly continuous functions `γ → C(α, β)` and uniform limits of sequences
   `ι → γ → C(α, β)`.
-/


universe u₁ u₂ u₃

open Filter uniformity Topology

open UniformSpace Set Filter

variable {α : Type u₁} {β : Type u₂} [TopologicalSpace α] [UniformSpace β]

variable (K : Set α) (V : Set (β × β)) (f : C(α, β))

namespace ContinuousMap

/-- Given `K ⊆ α`, `V ⊆ β × β`, and `f : C(α, β)`, we define `compact_conv_nhd K V f` to be the set
of `g : C(α, β)` that are `V`-close to `f` on `K`. -/
def compactConvNhd : Set C(α, β) :=
  { g | ∀ x ∈ K, (f x, g x) ∈ V }
#align continuous_map.compact_conv_nhd ContinuousMap.compactConvNhd

variable {K V}

theorem self_mem_compactConvNhd (hV : V ∈ 𝓤 β) : f ∈ compactConvNhd K V f := fun x hx =>
  refl_mem_uniformity hV
#align continuous_map.self_mem_compact_conv_nhd ContinuousMap.self_mem_compactConvNhd

@[mono]
theorem compactConvNhd_mono {V' : Set (β × β)} (hV' : V' ⊆ V) :
    compactConvNhd K V' f ⊆ compactConvNhd K V f := fun x hx a ha => hV' (hx a ha)
#align continuous_map.compact_conv_nhd_mono ContinuousMap.compactConvNhd_mono

theorem compactConvNhd_mem_comp {g₁ g₂ : C(α, β)} {V' : Set (β × β)}
    (hg₁ : g₁ ∈ compactConvNhd K V f) (hg₂ : g₂ ∈ compactConvNhd K V' g₁) :
    g₂ ∈ compactConvNhd K (V ○ V') f := fun x hx => ⟨g₁ x, hg₁ x hx, hg₂ x hx⟩
#align continuous_map.compact_conv_nhd_mem_comp ContinuousMap.compactConvNhd_mem_comp

/-- A key property of `compact_conv_nhd`. It allows us to apply
`topological_space.nhds_mk_of_nhds_filter_basis` below. -/
theorem compactConvNhd_nhd_basis (hV : V ∈ 𝓤 β) :
    ∃ V' ∈ 𝓤 β,
      V' ⊆ V ∧ ∀ g ∈ compactConvNhd K V' f, compactConvNhd K V' g ⊆ compactConvNhd K V f :=
  by
  obtain ⟨V', h₁, h₂⟩ := comp_mem_uniformity_sets hV
  exact
    ⟨V', h₁, subset.trans (subset_comp_self_of_mem_uniformity h₁) h₂, fun g hg g' hg' =>
      compact_conv_nhd_mono f h₂ (compact_conv_nhd_mem_comp f hg hg')⟩
#align continuous_map.compact_conv_nhd_nhd_basis ContinuousMap.compactConvNhd_nhd_basis

theorem compactConvNhd_subset_inter (K₁ K₂ : Set α) (V₁ V₂ : Set (β × β)) :
    compactConvNhd (K₁ ∪ K₂) (V₁ ∩ V₂) f ⊆ compactConvNhd K₁ V₁ f ∩ compactConvNhd K₂ V₂ f :=
  fun g hg =>
  ⟨fun x hx => mem_of_mem_inter_left (hg x (mem_union_left K₂ hx)), fun x hx =>
    mem_of_mem_inter_right (hg x (mem_union_right K₁ hx))⟩
#align continuous_map.compact_conv_nhd_subset_inter ContinuousMap.compactConvNhd_subset_inter

theorem compact_conv_nhd_compact_entourage_nonempty :
    { KV : Set α × Set (β × β) | IsCompact KV.1 ∧ KV.2 ∈ 𝓤 β }.Nonempty :=
  ⟨⟨∅, univ⟩, isCompact_empty, Filter.univ_mem⟩
#align continuous_map.compact_conv_nhd_compact_entourage_nonempty ContinuousMap.compact_conv_nhd_compact_entourage_nonempty

theorem compactConvNhd_filter_isBasis :
    Filter.IsBasis (fun KV : Set α × Set (β × β) => IsCompact KV.1 ∧ KV.2 ∈ 𝓤 β) fun KV =>
      compactConvNhd KV.1 KV.2 f :=
  { Nonempty := compact_conv_nhd_compact_entourage_nonempty
    inter := by
      rintro ⟨K₁, V₁⟩ ⟨K₂, V₂⟩ ⟨hK₁, hV₁⟩ ⟨hK₂, hV₂⟩
      exact
        ⟨⟨K₁ ∪ K₂, V₁ ∩ V₂⟩, ⟨hK₁.union hK₂, Filter.inter_mem hV₁ hV₂⟩,
          compact_conv_nhd_subset_inter f K₁ K₂ V₁ V₂⟩ }
#align continuous_map.compact_conv_nhd_filter_is_basis ContinuousMap.compactConvNhd_filter_isBasis

/-- A filter basis for the neighbourhood filter of a point in the compact-convergence topology. -/
def compactConvergenceFilterBasis (f : C(α, β)) : FilterBasis C(α, β) :=
  (compactConvNhd_filter_isBasis f).FilterBasis
#align continuous_map.compact_convergence_filter_basis ContinuousMap.compactConvergenceFilterBasis

theorem mem_compact_convergence_nhd_filter (Y : Set C(α, β)) :
    Y ∈ (compactConvergenceFilterBasis f).filterₓ ↔
      ∃ (K : Set α)(V : Set (β × β))(hK : IsCompact K)(hV : V ∈ 𝓤 β), compactConvNhd K V f ⊆ Y :=
  by
  constructor
  · rintro ⟨X, ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩, hY⟩
    exact ⟨K, V, hK, hV, hY⟩
  · rintro ⟨K, V, hK, hV, hY⟩
    exact ⟨compact_conv_nhd K V f, ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩, hY⟩
#align continuous_map.mem_compact_convergence_nhd_filter ContinuousMap.mem_compact_convergence_nhd_filter

/-- The compact-convergence topology. In fact, see `compact_open_eq_compact_convergence` this is
the same as the compact-open topology. This definition is thus an auxiliary convenience definition
and is unlikely to be of direct use. -/
def compactConvergenceTopology : TopologicalSpace C(α, β) :=
  TopologicalSpace.mkOfNhds fun f => (compactConvergenceFilterBasis f).filterₓ
#align continuous_map.compact_convergence_topology ContinuousMap.compactConvergenceTopology

theorem nhds_compact_convergence :
    @nhds _ compactConvergenceTopology f = (compactConvergenceFilterBasis f).filterₓ :=
  by
  rw [TopologicalSpace.nhds_mkOfNhds_filterBasis] <;> rintro g - ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩
  · exact self_mem_compact_conv_nhd g hV
  · obtain ⟨V', hV', h₁, h₂⟩ := compact_conv_nhd_nhd_basis g hV
    exact
      ⟨compact_conv_nhd K V' g, ⟨⟨K, V'⟩, ⟨hK, hV'⟩, rfl⟩, compact_conv_nhd_mono g h₁, fun g' hg' =>
        ⟨compact_conv_nhd K V' g', ⟨⟨K, V'⟩, ⟨hK, hV'⟩, rfl⟩, h₂ g' hg'⟩⟩
#align continuous_map.nhds_compact_convergence ContinuousMap.nhds_compact_convergence

theorem hasBasis_nhds_compact_convergence :
    HasBasis (@nhds _ compactConvergenceTopology f)
      (fun p : Set α × Set (β × β) => IsCompact p.1 ∧ p.2 ∈ 𝓤 β) fun p =>
      compactConvNhd p.1 p.2 f :=
  (nhds_compact_convergence f).symm ▸ (compactConvNhd_filter_isBasis f).HasBasis
#align continuous_map.has_basis_nhds_compact_convergence ContinuousMap.hasBasis_nhds_compact_convergence

/-- This is an auxiliary lemma and is unlikely to be of direct use outside of this file. See
`tendsto_iff_forall_compact_tendsto_uniformly_on` below for the useful version where the topology
is picked up via typeclass inference. -/
theorem tendsto_iff_forall_compact_tendsto_uniformly_on' {ι : Type u₃} {p : Filter ι}
    {F : ι → C(α, β)} :
    Filter.Tendsto F p (@nhds _ compactConvergenceTopology f) ↔
      ∀ K, IsCompact K → TendstoUniformlyOn (fun i a => F i a) f p K :=
  by
  simp only [(has_basis_nhds_compact_convergence f).tendsto_right_iff, TendstoUniformlyOn, and_imp,
    Prod.forall]
  refine' forall_congr' fun K => _
  rw [forall_swap]
  exact forall₃_congr fun hK V hV => Iff.rfl
#align continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on' ContinuousMap.tendsto_iff_forall_compact_tendsto_uniformly_on'

/-- Any point of `compact_open.gen K U` is also an interior point wrt the topology of compact
convergence.

The topology of compact convergence is thus at least as fine as the compact-open topology. -/
theorem compactConvNhd_subset_compact_open (hK : IsCompact K) {U : Set β} (hU : IsOpen U)
    (hf : f ∈ CompactOpen.gen K U) :
    ∃ V ∈ 𝓤 β, IsOpen V ∧ compactConvNhd K V f ⊆ CompactOpen.gen K U :=
  by
  obtain ⟨V, hV₁, hV₂, hV₃⟩ := lebesgue_number_of_compact_open (hK.image f.continuous) hU hf
  refine' ⟨V, hV₁, hV₂, _⟩
  rintro g hg _ ⟨x, hx, rfl⟩
  exact hV₃ (f x) ⟨x, hx, rfl⟩ (hg x hx)
#align continuous_map.compact_conv_nhd_subset_compact_open ContinuousMap.compactConvNhd_subset_compact_open

/-- The point `f` in `compact_conv_nhd K V f` is also an interior point wrt the compact-open
topology.

Since `compact_conv_nhd K V f` are a neighbourhood basis at `f` for each `f`, it follows that
the compact-open topology is at least as fine as the topology of compact convergence. -/
theorem interᵢ_compact_open_gen_subset_compactConvNhd (hK : IsCompact K) (hV : V ∈ 𝓤 β) :
    ∃ (ι : Sort (u₁ + 1))(_ : Fintype ι)(C : ι → Set α)(hC : ∀ i, IsCompact (C i))(U :
      ι → Set β)(hU : ∀ i, IsOpen (U i)),
      (f ∈ ⋂ i, CompactOpen.gen (C i) (U i)) ∧
        (⋂ i, CompactOpen.gen (C i) (U i)) ⊆ compactConvNhd K V f :=
  by
  obtain ⟨W, hW₁, hW₄, hW₂, hW₃⟩ := comp_open_symm_mem_uniformity_sets hV
  obtain ⟨Z, hZ₁, hZ₄, hZ₂, hZ₃⟩ := comp_open_symm_mem_uniformity_sets hW₁
  let U : α → Set α := fun x => f ⁻¹' ball (f x) Z
  have hU : ∀ x, IsOpen (U x) := fun x => f.continuous.is_open_preimage _ (is_open_ball _ hZ₄)
  have hUK : K ⊆ ⋃ x : K, U (x : K) := by
    intro x hx
    simp only [exists_prop, mem_Union, Union_coe_set, mem_preimage]
    exact ⟨(⟨x, hx⟩ : K), by simp [hx, mem_ball_self (f x) hZ₁]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun x : K => hU x.val) hUK
  let C : t → Set α := fun i => K ∩ closure (U ((i : K) : α))
  have hC : K ⊆ ⋃ i, C i := by
    rw [← K.inter_Union, subset_inter_iff]
    refine' ⟨subset.rfl, ht.trans _⟩
    simp only [SetCoe.forall, Subtype.coe_mk, Union_subset_iff]
    exact fun x hx₁ hx₂ => subset_Union_of_subset (⟨_, hx₂⟩ : t) (by simp [subset_closure])
  have hfC : ∀ i : t, C i ⊆ f ⁻¹' ball (f ((i : K) : α)) W :=
    by
    simp only [← image_subset_iff, ← mem_preimage]
    rintro ⟨⟨x, hx₁⟩, hx₂⟩
    have hZW : closure (ball (f x) Z) ⊆ ball (f x) W :=
      by
      intro y hy
      obtain ⟨z, hz₁, hz₂⟩ := uniform_space.mem_closure_iff_ball.mp hy hZ₁
      exact ball_mono hZ₃ _ (mem_ball_comp hz₂ ((mem_ball_symmetry hZ₂).mp hz₁))
    calc
      f '' (K ∩ closure (U x)) ⊆ f '' closure (U x) := image_subset _ (inter_subset_right _ _)
      _ ⊆ closure (f '' U x) := f.continuous.continuous_on.image_closure
      _ ⊆ closure (ball (f x) Z) := by
        apply closure_mono
        simp
      _ ⊆ ball (f x) W := hZW
      
  refine'
    ⟨t, t.fintype_coe_sort, C, fun i => hK.inter_right isClosed_closure, fun i =>
      ball (f ((i : K) : α)) W, fun i => is_open_ball _ hW₄, by simp [compact_open.gen, hfC],
      fun g hg x hx => hW₃ (mem_comp_rel.mpr _)⟩
  simp only [mem_Inter, compact_open.gen, mem_set_of_eq, image_subset_iff] at hg
  obtain ⟨y, hy⟩ := mem_Union.mp (hC hx)
  exact ⟨f y, (mem_ball_symmetry hW₂).mp (hfC y hy), mem_preimage.mp (hg y hy)⟩
#align continuous_map.Inter_compact_open_gen_subset_compact_conv_nhd ContinuousMap.interᵢ_compact_open_gen_subset_compactConvNhd

/-- The compact-open topology is equal to the compact-convergence topology. -/
theorem compactOpen_eq_compact_convergence :
    ContinuousMap.compactOpen = (compactConvergenceTopology : TopologicalSpace C(α, β)) :=
  by
  rw [compact_convergence_topology, ContinuousMap.compactOpen]
  refine' le_antisymm _ _
  · refine' fun X hX => is_open_iff_forall_mem_open.mpr fun f hf => _
    have hXf : X ∈ (compact_convergence_filter_basis f).filterₓ :=
      by
      rw [← nhds_compact_convergence]
      exact @IsOpen.mem_nhds C(α, β) compact_convergence_topology _ _ hX hf
    obtain ⟨-, ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩, hXf⟩ := hXf
    obtain ⟨ι, hι, C, hC, U, hU, h₁, h₂⟩ := Inter_compact_open_gen_subset_compact_conv_nhd f hK hV
    haveI := hι
    exact
      ⟨⋂ i, compact_open.gen (C i) (U i), h₂.trans hXf,
        isOpen_interᵢ fun i => ContinuousMap.isOpen_gen (hC i) (hU i), h₁⟩
  · simp only [TopologicalSpace.le_generateFrom_iff_subset_isOpen, and_imp, exists_prop,
      forall_exists_index, set_of_subset_set_of]
    rintro - K hK U hU rfl f hf
    obtain ⟨V, hV, hV', hVf⟩ := compact_conv_nhd_subset_compact_open f hK hU hf
    exact Filter.mem_of_superset (FilterBasis.mem_filter_of_mem _ ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩) hVf
#align continuous_map.compact_open_eq_compact_convergence ContinuousMap.compactOpen_eq_compact_convergence

/-- The filter on `C(α, β) × C(α, β)` which underlies the uniform space structure on `C(α, β)`. -/
def compactConvergenceUniformity : Filter (C(α, β) × C(α, β)) :=
  ⨅ KV ∈ { KV : Set α × Set (β × β) | IsCompact KV.1 ∧ KV.2 ∈ 𝓤 β },
    𝓟 { fg : C(α, β) × C(α, β) | ∀ x : α, x ∈ KV.1 → (fg.1 x, fg.2 x) ∈ KV.2 }
#align continuous_map.compact_convergence_uniformity ContinuousMap.compactConvergenceUniformity

theorem hasBasis_compactConvergenceUniformity_aux :
    HasBasis (@compactConvergenceUniformity α β _ _)
      (fun p : Set α × Set (β × β) => IsCompact p.1 ∧ p.2 ∈ 𝓤 β) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ p.2 } :=
  by
  refine' Filter.hasBasis_binfᵢ_principal _ compact_conv_nhd_compact_entourage_nonempty
  rintro ⟨K₁, V₁⟩ ⟨hK₁, hV₁⟩ ⟨K₂, V₂⟩ ⟨hK₂, hV₂⟩
  refine' ⟨⟨K₁ ∪ K₂, V₁ ∩ V₂⟩, ⟨hK₁.union hK₂, Filter.inter_mem hV₁ hV₂⟩, _⟩
  simp only [le_eq_subset, Prod.forall, set_of_subset_set_of, ge_iff_le, Order.Preimage, ←
    forall_and, mem_inter_iff, mem_union]
  exact fun f g => forall_imp fun x => by tauto
#align continuous_map.has_basis_compact_convergence_uniformity_aux ContinuousMap.hasBasis_compactConvergenceUniformity_aux

/-- An intermediate lemma. Usually `mem_compact_convergence_entourage_iff` is more useful. -/
theorem mem_compactConvergenceUniformity (X : Set (C(α, β) × C(α, β))) :
    X ∈ @compactConvergenceUniformity α β _ _ ↔
      ∃ (K : Set α)(V : Set (β × β))(hK : IsCompact K)(hV : V ∈ 𝓤 β),
        { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V } ⊆ X :=
  by
  simp only [has_basis_compact_convergence_uniformity_aux.mem_iff, exists_prop, Prod.exists,
    and_assoc']
#align continuous_map.mem_compact_convergence_uniformity ContinuousMap.mem_compactConvergenceUniformity

/-- Note that we ensure the induced topology is definitionally the compact-open topology. -/
instance compactConvergenceUniformSpace : UniformSpace C(α, β)
    where
  uniformity := compactConvergenceUniformity
  refl :=
    by
    simp only [compact_convergence_uniformity, and_imp, Filter.le_principal_iff, Prod.forall,
      Filter.mem_principal, mem_set_of_eq, le_infᵢ_iff, idRel_subset]
    exact fun K V hK hV f x hx => refl_mem_uniformity hV
  symm :=
    by
    simp only [compact_convergence_uniformity, and_imp, Prod.forall, mem_set_of_eq, Prod.fst_swap,
      Filter.tendsto_principal, Prod.snd_swap, Filter.tendsto_infᵢ]
    intro K V hK hV
    obtain ⟨V', hV', hsymm, hsub⟩ := symm_of_uniformity hV
    let X := { fg : C(α, β) × C(α, β) | ∀ x : α, x ∈ K → (fg.1 x, fg.2 x) ∈ V' }
    have hX : X ∈ compact_convergence_uniformity :=
      (mem_compact_convergence_uniformity X).mpr ⟨K, V', hK, hV', by simp⟩
    exact Filter.eventually_of_mem hX fun fg hfg x hx => hsub (hsymm _ _ (hfg x hx))
  comp X hX :=
    by
    obtain ⟨K, V, hK, hV, hX⟩ := (mem_compact_convergence_uniformity X).mp hX
    obtain ⟨V', hV', hcomp⟩ := comp_mem_uniformity_sets hV
    let h := fun s : Set (C(α, β) × C(α, β)) => s ○ s
    suffices
      h { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V' } ∈
        compact_convergence_uniformity.lift' h
      by
      apply Filter.mem_of_superset this
      rintro ⟨f, g⟩ ⟨z, hz₁, hz₂⟩
      refine' hX fun x hx => hcomp _
      exact ⟨z x, hz₁ x hx, hz₂ x hx⟩
    apply Filter.mem_lift'
    exact (mem_compact_convergence_uniformity _).mpr ⟨K, V', hK, hV', subset.refl _⟩
  isOpen_uniformity := by
    rw [compact_open_eq_compact_convergence]
    refine' fun Y => forall₂_congr fun f hf => _
    simp only [mem_compact_convergence_nhd_filter, mem_compact_convergence_uniformity, Prod.forall,
      set_of_subset_set_of, compact_conv_nhd]
    refine' exists₄_congr fun K V hK hV => ⟨_, fun hY g hg => hY f g hg rfl⟩
    rintro hY g₁ g₂ hg₁ rfl
    exact hY hg₁
#align continuous_map.compact_convergence_uniform_space ContinuousMap.compactConvergenceUniformSpace

theorem mem_compact_convergence_entourage_iff (X : Set (C(α, β) × C(α, β))) :
    X ∈ 𝓤 C(α, β) ↔
      ∃ (K : Set α)(V : Set (β × β))(hK : IsCompact K)(hV : V ∈ 𝓤 β),
        { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V } ⊆ X :=
  mem_compactConvergenceUniformity X
#align continuous_map.mem_compact_convergence_entourage_iff ContinuousMap.mem_compact_convergence_entourage_iff

theorem hasBasis_compact_convergence_uniformity :
    HasBasis (𝓤 C(α, β)) (fun p : Set α × Set (β × β) => IsCompact p.1 ∧ p.2 ∈ 𝓤 β) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ p.2 } :=
  hasBasis_compactConvergenceUniformity_aux
#align continuous_map.has_basis_compact_convergence_uniformity ContinuousMap.hasBasis_compact_convergence_uniformity

theorem Filter.HasBasis.compact_convergence_uniformity {ι : Type _} {pi : ι → Prop}
    {s : ι → Set (β × β)} (h : (𝓤 β).HasBasis pi s) :
    HasBasis (𝓤 C(α, β)) (fun p : Set α × ι => IsCompact p.1 ∧ pi p.2) fun p =>
      { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ s p.2 } :=
  by
  refine' has_basis_compact_convergence_uniformity.to_has_basis _ _
  · rintro ⟨t₁, t₂⟩ ⟨h₁, h₂⟩
    rcases h.mem_iff.1 h₂ with ⟨i, hpi, hi⟩
    exact ⟨(t₁, i), ⟨h₁, hpi⟩, fun fg hfg x hx => hi (hfg _ hx)⟩
  · rintro ⟨t, i⟩ ⟨ht, hi⟩
    exact ⟨(t, s i), ⟨ht, h.mem_of_mem hi⟩, subset.rfl⟩
#align filter.has_basis.compact_convergence_uniformity Filter.HasBasis.compact_convergence_uniformity

variable {ι : Type u₃} {p : Filter ι} {F : ι → C(α, β)} {f}

theorem tendsto_iff_forall_compact_tendstoUniformlyOn :
    Tendsto F p (𝓝 f) ↔ ∀ K, IsCompact K → TendstoUniformlyOn (fun i a => F i a) f p K := by
  rw [compact_open_eq_compact_convergence, tendsto_iff_forall_compact_tendsto_uniformly_on']
#align continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn

/-- Locally uniform convergence implies convergence in the compact-open topology. -/
theorem tendsto_of_tendstoLocallyUniformly (h : TendstoLocallyUniformly (fun i a => F i a) f p) :
    Tendsto F p (𝓝 f) :=
  by
  rw [tendsto_iff_forall_compact_tendsto_uniformly_on]
  intro K hK
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
  exact h.tendsto_locally_uniformly_on
#align continuous_map.tendsto_of_tendsto_locally_uniformly ContinuousMap.tendsto_of_tendstoLocallyUniformly

/-- If every point has a compact neighbourhood, then convergence in the compact-open topology
implies locally uniform convergence.

See also `tendsto_iff_tendsto_locally_uniformly`, especially for T2 spaces. -/
theorem tendstoLocallyUniformly_of_tendsto (hα : ∀ x : α, ∃ n, IsCompact n ∧ n ∈ 𝓝 x)
    (h : Tendsto F p (𝓝 f)) : TendstoLocallyUniformly (fun i a => F i a) f p :=
  by
  rw [tendsto_iff_forall_compact_tendsto_uniformly_on] at h
  intro V hV x
  obtain ⟨n, hn₁, hn₂⟩ := hα x
  exact ⟨n, hn₂, h n hn₁ V hV⟩
#align continuous_map.tendsto_locally_uniformly_of_tendsto ContinuousMap.tendstoLocallyUniformly_of_tendsto

/-- Convergence in the compact-open topology is the same as locally uniform convergence on a locally
compact space.

For non-T2 spaces, the assumption `locally_compact_space α` is stronger than we need and in fact
the `←` direction is true unconditionally. See `tendsto_locally_uniformly_of_tendsto` and
`tendsto_of_tendsto_locally_uniformly` for versions requiring weaker hypotheses. -/
theorem tendsto_iff_tendstoLocallyUniformly [LocallyCompactSpace α] :
    Tendsto F p (𝓝 f) ↔ TendstoLocallyUniformly (fun i a => F i a) f p :=
  ⟨tendstoLocallyUniformly_of_tendsto exists_compact_mem_nhds, tendsto_of_tendstoLocallyUniformly⟩
#align continuous_map.tendsto_iff_tendsto_locally_uniformly ContinuousMap.tendsto_iff_tendstoLocallyUniformly

section CompactDomain

variable [CompactSpace α]

theorem hasBasis_compact_convergence_uniformity_of_compact :
    HasBasis (𝓤 C(α, β)) (fun V : Set (β × β) => V ∈ 𝓤 β) fun V =>
      { fg : C(α, β) × C(α, β) | ∀ x, (fg.1 x, fg.2 x) ∈ V } :=
  hasBasis_compact_convergence_uniformity.to_hasBasis
    (fun p hp => ⟨p.2, hp.2, fun fg hfg x hx => hfg x⟩) fun V hV =>
    ⟨⟨univ, V⟩, ⟨isCompact_univ, hV⟩, fun fg hfg x => hfg x (mem_univ x)⟩
#align continuous_map.has_basis_compact_convergence_uniformity_of_compact ContinuousMap.hasBasis_compact_convergence_uniformity_of_compact

/-- Convergence in the compact-open topology is the same as uniform convergence for sequences of
continuous functions on a compact space. -/
theorem tendsto_iff_tendstoUniformly :
    Tendsto F p (𝓝 f) ↔ TendstoUniformly (fun i a => F i a) f p :=
  by
  rw [tendsto_iff_forall_compact_tendsto_uniformly_on, ← tendstoUniformlyOn_univ]
  exact ⟨fun h => h univ isCompact_univ, fun h K hK => h.mono (subset_univ K)⟩
#align continuous_map.tendsto_iff_tendsto_uniformly ContinuousMap.tendsto_iff_tendstoUniformly

end CompactDomain

end ContinuousMap

