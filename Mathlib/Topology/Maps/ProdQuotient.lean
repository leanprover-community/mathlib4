import Mathlib.Topology.Compactness.Compact

open Function Set Filter TopologicalSpace
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

structure IsOpenQuotientMap (f : X → Y) : Prop where
  surjective : Surjective f
  continuous : Continuous f
  isOpenMap : IsOpenMap f

namespace IsOpenQuotientMap

theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) :
    IsOpenQuotientMap (Prod.map f g) where
  surjective := hf.surjective.prodMap hg.surjective
  continuous := hf.continuous.prod_map hg.continuous
  isOpenMap := hf.isOpenMap.prod hg.isOpenMap

theorem piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (hf : ∀ i, IsOpenQuotientMap (f i)) :
    IsOpenQuotientMap (fun (x : ∀ i, X i) (i : ι) ↦ f i (x i)) where
  surjective := surjective_pi_map fun i ↦ (hf i).surjective
  continuous := continuous_dcomp fun i ↦ (hf i).continuous
  isOpenMap := IsOpenMap.dcomp (fun i ↦ (hf i).isOpenMap)
    (eventually_of_forall fun i ↦ (hf i).surjective)

protected theorem comp {Z : Type*} [TopologicalSpace Z] {f : Y → Z} {g : X → Y}
    (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap (f ∘ g) where
  surjective := hf.surjective.comp hg.surjective
  continuous := hf.continuous.comp hg.continuous
  isOpenMap := hf.isOpenMap.comp hg.isOpenMap

protected theorem id : IsOpenQuotientMap (id : X → X) :=
  ⟨surjective_id, continuous_id, IsOpenMap.id⟩

end IsOpenQuotientMap  

@[mk_iff]
structure IsPullbackQuotientMap (f : X → Y) : Prop where
  continuous : Continuous f
  exists_clusterPt_comap {y : Y} {l : Filter Y} (h : ClusterPt y l) :
    ∃ x, f x = y ∧ ClusterPt x (comap f l)

nonrec theorem TopologicalSpace.IsTopologicalBasis.isPullbackQuotientMap_iff {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {f : X → Y} :
    IsPullbackQuotientMap f ↔
      Continuous f ∧ ∀ y : Y, ∀ S ⊆ B, (f ⁻¹' {y} ⊆ ⋃₀ S) →
        ∃ T ⊆ S, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y := by
  simp only [isPullbackQuotientMap_iff, clusterPt_iff_not_disjoint, disjoint_comap_iff_map]
  refine .and .rfl <| forall_congr' fun y ↦ ?_
  constructor
  · intro h S hSB hfS
    contrapose! h
    refine ⟨⨅ s ∈ S, 𝓟 ((f '' s)ᶜ), ?_, fun x hx ↦ ?_⟩
    · rw [iInf_subtype', (hasBasis_iInf_principal_finite _).disjoint_iff_right]
      rintro ⟨T, hTf, hTy⟩
      refine h (Subtype.val '' T) (image_subset_iff.2 fun x _ ↦ x.2) (hTf.image _) ?_
      simpa only [sUnion_image, image_iUnion, compl_iInter, compl_compl] using hTy
    · rcases @hfS x hx with ⟨s, hsS, hxs⟩
      rw [((basis_sets _).map f).disjoint_iff_left]
      refine ⟨s, hB.mem_nhds (hSB hsS) hxs, ?_⟩
      exact mem_iInf_of_mem s <| mem_iInf_of_mem hsS <| mem_principal_self _
  · intro h l H
    contrapose! H
    simp only [l.basis_sets.disjoint_iff_right] at H
    choose! s hsl hsx using H
    set S := B ∩ ⋃ (x : X) (_ : f x = y), {U : Set X | Disjoint U (f ⁻¹' s x)}
    obtain ⟨T, hTS, hTf, hTy⟩ : ∃ T ⊆ S, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y := by
      refine h S inter_subset_left fun x hx ↦ ?_
      rcases hB.mem_nhds_iff.1 (mem_map.1 <| hsx x hx) with ⟨U, hUB, hxU, hU⟩
      refine ⟨U, ⟨hUB, mem_iUnion₂.2 ⟨x, hx, ?_⟩⟩, hxU⟩
      rwa [mem_setOf, disjoint_left]
    refine disjoint_of_disjoint_of_mem disjoint_compl_right hTy ?_
    rw [sUnion_eq_biUnion, image_iUnion₂, compl_iUnion₂, biInter_mem hTf]
    intro U hUT
    rcases mem_iUnion₂.1 (hTS hUT).2 with ⟨x, hxy, hUx⟩
    filter_upwards [hsl x hxy] with y' hy' ⟨x', hx'U, hx'y⟩
    refine disjoint_left.mp hUx hx'U ?_
    rwa [mem_preimage, hx'y]

theorem isPullbackQuotientMap_iff_exists_finite_image_mem_nhds {f : X → Y} :
    IsPullbackQuotientMap f ↔
      Continuous f ∧ ∀ y : Y, ∀ S : Set (Set X),
        (∀ s ∈ S, IsOpen s) → (f ⁻¹' {y} ⊆ ⋃₀ S) → ∃ T ⊆ S, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y :=
  isTopologicalBasis_opens.isPullbackQuotientMap_iff

theorem IsOpenQuotientMap.isPullbackQuotientMap {f : X → Y} (hf : IsOpenQuotientMap f) :
    IsPullbackQuotientMap f where
  continuous := hf.continuous
  exists_clusterPt_comap {y l} h := by
    rcases hf.surjective y with ⟨x, rfl⟩
    refine ⟨x, rfl, ?_⟩
    -- TODO: move to a lemma about `IsOpenMap`
    rw [ClusterPt, ← map_neBot_iff, Filter.push_pull]
    exact h.neBot.mono <| inf_le_inf_right _ (hf.isOpenMap.nhds_le _)

namespace IsPullbackQuotientMap

protected theorem surjective {f : X → Y} (hf : IsPullbackQuotientMap f) : Surjective f := fun _ ↦
  (hf.exists_clusterPt_comap (.of_le_nhds le_rfl)).imp fun _ ↦ And.left

protected theorem id : IsPullbackQuotientMap (id : X → X) :=
  IsOpenQuotientMap.id.isPullbackQuotientMap

theorem exists_finset_biUnion_image_mem_nhds {ι : Type*} {f : X → Y} (hf : IsPullbackQuotientMap f)
    {y : Y} {s : ι → Set X} (hys : f ⁻¹' {y} ⊆ ⋃ i, s i) (hso : ∀ i, IsOpen (s i)) :
    ∃ t : Finset ι, ⋃ i ∈ t, f '' s i ∈ 𝓝 y := by
  classical
  rw [isPullbackQuotientMap_iff_exists_finite_image_mem_nhds] at hf
  rcases hf.2 y (range s) (forall_mem_range.2 hso) hys with ⟨T, hTs, hTf, hTy⟩
  lift T to Finset (Set X) using hTf
  rw [← image_univ, Finset.subset_image_iff] at hTs
  rcases hTs with ⟨t, -, rfl⟩
  refine ⟨t, ?_⟩
  simpa [image_iUnion] using hTy

theorem exists_finite_subset_biUnion_image_mem_nhds
    {ι : Type*} {f : X → Y} {I : Set ι} {y : Y} {s : ι → Set X}
    (hf : IsPullbackQuotientMap f) (hys : f ⁻¹' {y} ⊆ ⋃ i ∈ I, s i) (hso : ∀ i ∈ I, IsOpen (s i)) :
    ∃ t ⊆ I, t.Finite ∧ ⋃ i ∈ t, f '' s i ∈ 𝓝 y := by
  rw [biUnion_eq_iUnion] at hys
  rcases hf.exists_finset_biUnion_image_mem_nhds hys (Subtype.forall.2 hso) with ⟨t, ht⟩
  refine ⟨Subtype.val '' t.toSet, Subtype.coe_image_subset _ _, t.finite_toSet.image _, ?_⟩
  rwa [biUnion_image]

protected theorem comp {Z : Type*} [TopologicalSpace Z] {f : Y → Z} {g : X → Y}
    (hf : IsPullbackQuotientMap f) (hg : IsPullbackQuotientMap g) :
    IsPullbackQuotientMap (f ∘ g) where
  continuous := hf.continuous.comp hg.continuous
  exists_clusterPt_comap {z l} h := by
    rcases hf.exists_clusterPt_comap h with ⟨y, rfl, hy⟩
    rcases hg.exists_clusterPt_comap hy with ⟨x, rfl, hx⟩
    rw [comap_comap] at hx
    exact ⟨x, rfl, hx⟩

protected theorem pullback {Z : Type*} [TopologicalSpace Z] {f : X → Y}
    (hf : IsPullbackQuotientMap f) {g : Z → Y} (hg : Continuous g) :
    IsPullbackQuotientMap (Function.Pullback.snd : f.Pullback g → Z) where
  continuous := continuous_snd.comp continuous_subtype_val
  exists_clusterPt_comap {z l} h := by
    have : ClusterPt (g z) (map g (𝓝 z ⊓ l)) := by
      refine ClusterPt.map ?_ hg.continuousAt tendsto_map
      rwa [ClusterPt, inf_left_idem]
    rcases hf.exists_clusterPt_comap this with ⟨x, hxz, hxl⟩
    refine ⟨⟨(x, z), hxz⟩, rfl, ?_⟩
    rw [(embedding_subtype_val.basis_nhds
      ((basis_sets _).prod_nhds (basis_sets _))).clusterPt_iff (comap_hasBasis _ _)]
    rintro ⟨s, t⟩ ⟨hs : s ∈ 𝓝 x, ht : t ∈ 𝓝 z⟩ u hu
    rw [(basis_sets _).clusterPt_iff ((((basis_sets _).inf (basis_sets _)).map _).comap _)] at hxl
    rcases hxl hs (j := (t, u)) ⟨ht, hu⟩
      with ⟨x', hx's : x' ∈ s, z', ⟨hz't : z' ∈ t, hz'u : z' ∈ u⟩, hfxz'⟩
    refine ⟨⟨(x', z'), hfxz'.symm⟩, ⟨hx's, hz't⟩, hz'u⟩

end IsPullbackQuotientMap

structure IsProdQuotientMap (f : X → Y) : Prop where
  surjective : Surjective f
  continuous : Continuous f
  exists_finite_image_mem_nhds :
    ∀ V : Set Y, ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → (⋃₀ S = f ⁻¹' V) →
      ∀ y ∈ V, ∃ T ⊆ S, T.Finite ∧ (𝓝ˢ (f '' ⋃₀ T)).ker ∈ 𝓝 y

namespace IsProdQuotientMap

-- theorem quotientMap {f : X → Y} (hf : IsProdQuotientMap f) : QuotientMap f := by
--   refine quotientMap_iff.2
--     ⟨hf.surjective, fun V ↦ ⟨fun h ↦ h.preimage hf.continuous, fun ho ↦ ?_⟩⟩
--   refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
--   obtain ⟨T, hTV, -, hTy⟩ : ∃ T ⊆ {f ⁻¹' V}, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y :=
--     hf.exists_finite_image_mem_nhds V {f ⁻¹' V} (sUnion_singleton _) (by simp [ho]) y hy
--   calc
--     V = f '' ⋃₀ {f ⁻¹' V} := by simp [hf.surjective]
--     _ ⊇ f '' ⋃₀ T := by gcongr
--     _ ∈ 𝓝 y := hTy

-- theorem of_open {f : X → Y} (hfc : Continuous f) (hfo : IsOpenMap f) (hsurj : Surjective f) :
--     IsProdQuotientMap f := by
--   refine ⟨hsurj, hfc, fun V S hSV hSo y hy ↦ ?_⟩
--   rcases hsurj y with ⟨x, rfl⟩
--   rw [← mem_preimage, ← hSV, mem_sUnion] at hy
--   rcases hy with ⟨U, hUS, hxU⟩
--   refine ⟨{U}, by simp [hUS], by simp, ?_⟩
--   simpa using hfo.image_mem_nhds ((hSo U hUS).mem_nhds hxU)

-- theorem of_locallyCompact [LocallyCompactSpace Y] {f : X → Y} (hf : QuotientMap f) :
--     IsProdQuotientMap f := by
--   refine ⟨hf.surjective, hf.continuous, fun V S hSV hSo y hy ↦ ?_⟩
  

-- protected theorem id : IsProdQuotientMap (id : X → X) :=
--   .of_open continuous_id IsOpenMap.id surjective_id
  
-- theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
--     {f : X → Y} (hf : IsProdQuotientMap f) {g : X' → Y'} (hg : IsProdQuotientMap g) :
--     IsProdQuotientMap (Prod.map f g) := by
--   sorry

end IsProdQuotientMap
