/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets in uniform spaces

* `compactSpace_uniformity`: On a compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.

-/

public section

universe u v ua ub uc ud

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

section Compact

open Uniformity Set Filter UniformSpace
open scoped SetRel Topology

variable [UniformSpace α] {K : Set α}

/-- Let `c : ι → Set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {ι : Sort*} {U : ι → Set α} (hK : IsCompact K)
    (hopen : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ i, ball x V ⊆ U i := by
  have : ∀ x ∈ K, ∃ i, ∃ V ∈ 𝓤 α, ball x (V ○ V) ⊆ U i := fun x hx ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff, nhds_eq_comap_uniformity, ← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.relComp monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx ↦ ball x (W x hx)) (fun x hx ↦ ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x ∈ t, W x x.2, (biInter_finset_mem _).2 fun x _ ↦ hW x x.2, fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz ↦ hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩

theorem lebesgue_number_lemma_nhds' {U : (x : α) → x ∈ K → Set α} (hK : IsCompact K)
    (hU : ∀ x hx, U x hx ∈ 𝓝 x) : ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y : K, ball x V ⊆ U y y.2 := by
  rcases lebesgue_number_lemma (U := fun x : K => interior (U x x.2)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

theorem lebesgue_number_lemma_nhds {U : α → Set α} (hK : IsCompact K) (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y, ball x V ⊆ U y := by
  rcases lebesgue_number_lemma (U := fun x => interior (U x)) hK (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x hx)⟩) with ⟨V, V_uni, hV⟩
  exact ⟨V, V_uni, fun x hx => (hV x hx).imp fun _ hy => hy.trans interior_subset⟩

theorem lebesgue_number_lemma_nhdsWithin' {U : (x : α) → x ∈ K → Set α} (hK : IsCompact K)
    (hU : ∀ x hx, U x hx ∈ 𝓝[K] x) : ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y : K, ball x V ∩ K ⊆ U y y.2 :=
  (lebesgue_number_lemma_nhds' hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

theorem lebesgue_number_lemma_nhdsWithin {U : α → Set α} (hK : IsCompact K)
    (hU : ∀ x ∈ K, U x ∈ 𝓝[K] x) : ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ y, ball x V ∩ K ⊆ U y :=
  (lebesgue_number_lemma_nhds hK (fun x hx => Filter.mem_inf_principal'.1 (hU x hx))).imp
    fun _ ⟨V_uni, hV⟩ => ⟨V_uni, fun x hx => (hV x hx).imp fun _ hy => (inter_subset _ _ _).2 hy⟩

/-- Let `U : ι → Set α` be an open cover of a compact set `K`.
Then there exists an entourage `V`
such that for each `x ∈ K` its `V`-neighborhood is included in some `U i`.

Moreover, one can choose an entourage from a given basis. -/
protected theorem Filter.HasBasis.lebesgue_number_lemma {ι' ι : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : ι → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hopen : ∀ j, IsOpen (U j)) (hcover : K ⊆ ⋃ j, U j) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ j, ball x (V i) ⊆ U j := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun i hi ↦ Subset.trans (ball_mono hst _) hi

protected theorem Filter.HasBasis.lebesgue_number_lemma_nhds' {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : (x : α) → x ∈ K → Set α} (hbasis : (𝓤 α).HasBasis p V)
    (hK : IsCompact K) (hU : ∀ x hx, U x hx ∈ 𝓝 x) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ y : K, ball x (V i) ⊆ U y y.2 := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds' hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun y hy ↦ Subset.trans (ball_mono hst _) hy

protected theorem Filter.HasBasis.lebesgue_number_lemma_nhds {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : α → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hU : ∀ x ∈ K, U x ∈ 𝓝 x) : ∃ i, p i ∧ ∀ x ∈ K, ∃ y, ball x (V i) ⊆ U y := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhds hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun y hy ↦ Subset.trans (ball_mono hst _) hy

protected theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin' {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : (x : α) → x ∈ K → Set α} (hbasis : (𝓤 α).HasBasis p V)
    (hK : IsCompact K) (hU : ∀ x hx, U x hx ∈ 𝓝[K] x) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ y : K, ball x (V i) ∩ K ⊆ U y y.2 := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin' hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp
    fun y hy ↦ Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

protected theorem Filter.HasBasis.lebesgue_number_lemma_nhdsWithin {ι' : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : α → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hU : ∀ x ∈ K, U x ∈ 𝓝[K] x) : ∃ i, p i ∧ ∀ x ∈ K, ∃ y, ball x (V i) ∩ K ⊆ U y := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma_nhdsWithin hK hU)
  exact fun s t hst ht x hx ↦ (ht x hx).imp
    fun y hy ↦ Subset.trans (Set.inter_subset_inter_left K (ball_mono hst _)) hy

/-- Let `c : Set (Set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
theorem lebesgue_number_lemma_sUnion {S : Set (Set α)}
    (hK : IsCompact K) (hopen : ∀ s ∈ S, IsOpen s) (hcover : K ⊆ ⋃₀ S) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ s ∈ S, ball x V ⊆ s := by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover

/-- If `K` is a compact set in a uniform space and `{V i | p i}` is a basis of entourages,
then `{⋃ x ∈ K, UniformSpace.ball x (V i) | p i}` is a basis of `𝓝ˢ K`.

Here "`{s i | p i}` is a basis of a filter `l`" means `Filter.HasBasis l p s`. -/
theorem IsCompact.nhdsSet_basis_uniformity {p : ι → Prop} {V : ι → Set (α × α)}
    (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis p fun i => ⋃ x ∈ K, ball x (V i) where
  mem_iff' U := by
    constructor
    · intro H
      have HKU : K ⊆ ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : ∃ i, p i ∧ ⋃ x ∈ K, ball x (V i) ⊆ interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ ↦ isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ ↦ ?_) hi
      exact ball_mem_nhds _ <| hbasis.mem_of_mem hpi

-- TODO: move to a separate file, golf using the regularity of a uniform space.
theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ V ∈ 𝓤 α, Disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) := by
  have : Bᶜ ∈ 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hxa hxb) hb

theorem Disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ i, p i ∧ Disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) := by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩

/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
theorem lebesgue_number_of_compact_open {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V ∈ 𝓤 α, IsOpen V ∧ ∀ x ∈ K, UniformSpace.ball x V ⊆ U :=
  let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩


/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α := by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U ∈ 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩

/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
theorem compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x) :=
  nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)

theorem unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ]
    {u u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) :
    u = u' := by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u, compactSpace_uniformity, h, h']

end Compact

theorem IsClosed.relPreimage_of_isCompact [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : IsCompact t) :
    IsClosed (s.preimage t) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually] at hs ⊢
  simp_rw [Set.mem_compl_iff, SetRel.mem_preimage, not_exists, not_and]
  exact fun y hy => ht.eventually_forall_of_forall_eventually fun x hx => hs _ <| hy _ hx

theorem IsClosed.relImage_of_isCompact [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : IsCompact t) :
    IsClosed (s.image t) :=
  hs.relInv.relPreimage_of_isCompact ht
