import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Homeomorph
import Mathlib.Data.Fintype.Option

open Function Set Filter TopologicalSpace
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- TODO: prove `Continuous Pullback.fst` and `Continuous Pullback.snd`

@[simps]
def Homeomorph.pullbackProdFst (f : X → Y) (hf : Continuous f) (Z : Type*) [TopologicalSpace Z] :
    ((f : X → Y).Pullback (Prod.fst : Y × Z → Y)) ≃ₜ X × Z where
  toFun a := (a.fst, a.snd.2)
  invFun a := ⟨(a.1, f a.1, a.2), rfl⟩
  left_inv a := Subtype.eq <| Prod.ext rfl <| Prod.ext a.2 rfl
  right_inv _ := rfl
  continuous_toFun := by simp only [Pullback.fst, Pullback.snd]; fun_prop

namespace TopologicalSpace

/-- Topology on `TopologicalSpace.Opens X` defined in

On topological quotient maps preserved by pullbacks or products
B. J. DAY AND G. M. KELLY

-/
protected def dayKelly (α : Type*) [CompleteLattice α] : TopologicalSpace α where
  IsOpen S := IsUpperSet S ∧ ∀ U : Set α, sSup U ∈ S → ∃ u ⊆ U, u.Finite ∧ sSup u ∈ S
  isOpen_univ := ⟨isUpperSet_univ, fun _ _ ↦ ⟨∅, by simp⟩⟩
  isOpen_inter s t hs ht := by
    refine ⟨hs.1.inter ht.1, fun U ⟨hUs, hUt⟩ ↦ ?_⟩
    rcases hs.2 U hUs with ⟨us, husU, husf, hus⟩
    rcases ht.2 U hUt with ⟨ut, hutU, hutf, hut⟩
    refine ⟨us ∪ ut, union_subset husU hutU, husf.union hutf, ?_⟩
    rw [sSup_union]
    exact ⟨hs.1 le_sup_left hus, ht.1 le_sup_right hut⟩
  isOpen_sUnion S hS := by
    refine ⟨isUpperSet_sUnion fun s hs ↦ (hS s hs).1, fun U hU ↦ ?_⟩
    rcases mem_sUnion.1 hU with ⟨s, hsS, hsU⟩
    rcases (hS s hsS).2 U hsU with ⟨u, huU, huf, hus⟩
    exact ⟨u, huU, huf, s, hsS, hus⟩

theorem isOpen_dayKelly_setOf_isCompact_subset {K : Set X} (hK : IsCompact K) :
    IsOpen[.dayKelly (Opens X)] {U | K ⊆ U} := by
  refine ⟨fun V U hV hle ↦ hle.trans hV, fun U hU ↦ ?_⟩
  rw [mem_setOf, Opens.coe_sSup] at hU
  simpa using hK.elim_finite_subcover_image (fun u _ ↦ u.isOpen) hU

end TopologicalSpace

variable (X) in
class ProdQuotientMapSpace : Prop where
  exists_dayKelly_isOpen : ∀ U : Opens X, ∀ x ∈ U,
    ∃ S : Set (Opens X), U ∈ S ∧ IsOpen[.dayKelly (Opens X)] S ∧ (⋂ s ∈ S, (s : Set X)) ∈ 𝓝 x

instance (priority := 100) [LocallyCompactSpace X] : ProdQuotientMapSpace X := by
  refine ⟨fun U x hxU ↦ ?_⟩
  rcases local_compact_nhds (U.isOpen.mem_nhds hxU) with ⟨K, hKx, hKU, hKc⟩
  exact ⟨{V | K ⊆ V}, hKU, isOpen_dayKelly_setOf_isCompact_subset hKc,
    mem_of_superset hKx <| subset_iInter₂ fun _ ↦ id⟩

instance {α} : Trans (Membership.mem : α → Set α → Prop) Subset Membership.mem :=
  ⟨fun h₁ h₂ => h₂ h₁⟩

instance (priority := 100) [R1Space X] [ProdQuotientMapSpace X] : LocallyCompactSpace X := by
  suffices WeaklyLocallyCompactSpace X from inferInstance
  have : RegularSpace X := by
    refine .of_exists_mem_nhds_isClosed_subset fun x s hxs ↦ ?_
    wlog hso : IsOpen s generalizing s
    · rcases this (interior s) (interior_mem_nhds.2 hxs) isOpen_interior with ⟨t, htx, htc, hts⟩
      exact ⟨t, htx, htc, hts.trans interior_subset⟩
    lift s to Opens X using hso
    rcases ProdQuotientMapSpace.exists_dayKelly_isOpen s x (mem_of_mem_nhds hxs)
      with ⟨S, hS, hSo, hxS⟩
    set t : Set X := ⋂ s ∈ S, s
    refine ⟨_, mem_of_superset hxS subset_closure, isClosed_closure, ?_⟩
    intro y hyS
    by_contra hys
    have : ∀ z ∈ s, ∃ U : Opens X, z ∈ U ∧ y ∉ closure U := by
      intro z hz
      have : ¬y ⤳ z := by
        simp only [specializes_iff_forall_open, not_forall]
        exact ⟨_, s.isOpen, hz, hys⟩
      rw [← disjoint_nhds_nhds_iff_not_specializes, (nhds_basis_opens _).disjoint_iff_right] at this
      rcases this with ⟨U, ⟨hzU, hUo⟩, hU⟩
      refine ⟨⟨U, hUo⟩, hzU, ?_⟩
      rwa [Opens.coe_mk, ← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds]
    choose! U hmem hyU using this
    have : sSup (U '' s) ∈ S := by
      refine hSo.1 (fun z hz ↦ ?_) hS
      simp only [SetLike.mem_coe, sSup_image, Opens.mem_iSup]
      exact ⟨z, hz, hmem z hz⟩
    rcases exists_subset_image_finite_and.1 (hSo.2 _ this) with ⟨v, hsub, hvf, hv⟩
    have := calc
      y ∈ closure t := hyS
      _ ⊆ closure ↑(sSup (U '' v)) := closure_mono <| iInter₂_subset _ ‹_›
      _ = ⋃ z ∈ v, closure (U z) := by
        simp_rw [sSup_image, Opens.coe_iSup, hvf.closure_biUnion]
    rcases mem_iUnion₂.1 this with ⟨z, hzv, hyz⟩
    exact hyU _ (hsub hzv) hyz
  refine ⟨fun x ↦ ?_⟩
  rcases ProdQuotientMapSpace.exists_dayKelly_isOpen ⊤ x trivial with ⟨S, hS, hSo, hxS⟩
  rcases exists_mem_nhds_isClosed_subset hxS with ⟨K, hxK, hKc, hKS⟩
  simp only [subset_iInter_iff] at hKS
  lift K to Closeds X using hKc
  refine ⟨_, isCompact_of_finite_subcover_sUnion fun V hVo hKV ↦ ?_, hxK⟩
  lift V to Set (Opens X) using hVo
  replace hSV : sSup (insert K.compl V) = ⊤ := by
    rwa [sSup_insert, ← SetLike.coe_set_eq, Opens.coe_sup, Opens.coe_sSup, Opens.coe_top,
      Closeds.compl_coe, ← sUnion_image, ← compl_subset_iff_union, compl_compl]
  rcases hSo.2 _ (hSV ▸ hS) with ⟨T, hTsub, hTf, hTS⟩
  rw [exists_subset_image_finite_and]
  refine ⟨T \ {K.compl}, diff_singleton_subset_iff.2 hTsub, hTf.diff _, fun z hz ↦ ?_⟩
  rcases Opens.mem_sSup.1 (hKS _ hTS hz) with ⟨v, hvT, hzv⟩
  rw [sUnion_image, mem_iUnion₂]
  refine ⟨v, ⟨hvT, ?_⟩, hzv⟩
  rintro rfl
  exact hzv hz

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

theorem Homeomorph.isOpenQuotientMap (f : X ≃ₜ Y) : IsOpenQuotientMap f where
  surjective := f.surjective
  continuous := f.continuous
  isOpenMap := f.isOpenMap

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

theorem Homeomorph.isPullbackQuotientMap (f : X ≃ₜ Y) : IsPullbackQuotientMap f :=
  f.isOpenQuotientMap.isPullbackQuotientMap

namespace IsPullbackQuotientMap

protected theorem surjective {f : X → Y} (hf : IsPullbackQuotientMap f) : Surjective f := fun _ ↦
  (hf.exists_clusterPt_comap (.of_le_nhds le_rfl)).imp fun _ ↦ And.left

protected theorem quotientMap {f : X → Y} (hf : IsPullbackQuotientMap f) : QuotientMap f := by
  refine quotientMap_iff.2 ⟨hf.surjective, fun U ↦ ⟨fun h ↦ h.preimage hf.continuous, fun h ↦ ?_⟩⟩
  rw [← isClosed_compl_iff, isClosed_iff_clusterPt]
  intro y hy
  rcases hf.exists_clusterPt_comap hy with ⟨x, rfl, hx⟩
  rwa [comap_principal, ← mem_closure_iff_clusterPt, preimage_compl, closure_compl,
    h.interior_eq] at hx

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
    rcases hf.exists_clusterPt_comap (h.nhds_inf.map hg.continuousAt tendsto_map) with ⟨x, hxz, hxl⟩
    refine ⟨⟨(x, z), hxz⟩, rfl, ?_⟩
    rw [(embedding_subtype_val.basis_nhds
      ((basis_sets _).prod_nhds (basis_sets _))).clusterPt_iff (comap_hasBasis _ _)]
    rintro ⟨s, t⟩ ⟨hs : s ∈ 𝓝 x, ht : t ∈ 𝓝 z⟩ u hu
    rw [(basis_sets _).clusterPt_iff ((((basis_sets _).inf (basis_sets _)).map _).comap _)] at hxl
    rcases hxl hs (j := (t, u)) ⟨ht, hu⟩
      with ⟨x', hx's : x' ∈ s, z', ⟨hz't : z' ∈ t, hz'u : z' ∈ u⟩, hfxz'⟩
    refine ⟨⟨(x', z'), hfxz'.symm⟩, ⟨hx's, hz't⟩, hz'u⟩

protected theorem prodSwap : IsPullbackQuotientMap (Prod.swap : X × Y → Y × X) :=
  (Homeomorph.prodComm X Y).isPullbackQuotientMap

protected theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'} (hf : IsPullbackQuotientMap f) (hg : IsPullbackQuotientMap g) :
    IsPullbackQuotientMap (Prod.map f g) :=
  have H₁ : IsPullbackQuotientMap (Prod.map f id : X × X' → Y × X') :=
    (hf.pullback continuous_fst).comp
      (Homeomorph.pullbackProdFst f hf.continuous X').symm.isPullbackQuotientMap
  have H₂ : IsPullbackQuotientMap (Prod.map g id : X' × Y → Y' × Y) :=
    (hg.pullback continuous_fst).comp
      (Homeomorph.pullbackProdFst g hg.continuous Y).symm.isPullbackQuotientMap
  have H₃ : IsPullbackQuotientMap (Prod.map id g: Y × X' → Y × Y') :=
    IsPullbackQuotientMap.prodSwap.comp (H₂.comp .prodSwap)
  H₃.comp H₁

-- Use the next lemma instead
private theorem piMap_fin {n : ℕ} {X Y : Fin n → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsPullbackQuotientMap (f i)) :
    IsPullbackQuotientMap (f _ ∘' · : (∀ i, X i) → (∀ i, Y i)) := by
  induction n with
  | zero => _
  | succ n ihn => _

protected theorem piMap {ι : Type*} {X Y : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsPullbackQuotientMap (f i)) :
    IsPullbackQuotientMap (f _ ∘' · : (∀ i, X i) → (∀ i, Y i)) := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have H₁ : IsPullbackQuotientMap (f _ ∘' · : (∀ k, X (e.symm k)) → _) := piMap_fin fun _ ↦ h _
  have H₂ : IsPullbackQuotientMap
      (fun x k ↦ f (e.symm k) (x (e.symm k)) : (∀ i, X i) → (∀ k, Y (e.symm k))) :=
    H₁.comp (Homeomorph.piCongrLeft e.symm).symm.isPullbackQuotientMap
  convert (Homeomorph.piCongrLeft e.symm).isPullbackQuotientMap.comp H₂ with x
  ext y i
  rcases e.symm.surjective i with ⟨k, rfl⟩
  dsimp [(· ∘' ·)]
  rw [Equiv.piCongrLeft'_symm_apply_apply]

theorem of_forall_pullback {f : X → Y} (hf : Continuous f)
    (h : ∀ (Z : Type v) (z : Z) (l : Filter Z) (e : Z ≃ Y), Tendsto e l (𝓝 (e z)) →
      letI : TopologicalSpace Z := nhdsAdjoint z l
      QuotientMap (Pullback.snd : f.Pullback e → Z)) :
    IsPullbackQuotientMap f := by
  refine ⟨hf, fun {y l'} hyl' ↦ ?_⟩
  obtain ⟨Z, z, e, l, rfl, hlBot, hlz, hll'⟩ : ∃ (Z : Type v) (z : Z) (e : Z ≃ Y) (l : Filter Z),
      e z = y ∧ l.NeBot ∧ Tendsto e l (𝓝 y) ∧ Tendsto e l l' :=
    ⟨Y, y, .refl _, 𝓝 y ⊓ l', rfl, hyl', inf_le_left, inf_le_right⟩
  letI := nhdsAdjoint z l
  by_contra! H
  have hzo : IsOpen {z} := by
    rw [← (h Z z l e hlz).isOpen_preimage, isOpen_iff_mem_nhds]
    rintro ⟨⟨x, z⟩, hxz : f x = e z⟩ rfl
    obtain ⟨U, hU, s, hs, hUS⟩ : ∃ U ∈ 𝓝 x, ∃ s ∈ l', Disjoint U (f ⁻¹' s) := by
      simpa only [(basis_sets _).clusterPt_iff (l'.basis_sets.comap _), not_forall, id, exists_prop,
        ← not_disjoint_iff_nonempty_inter.not_right] using H x hxz
    have : insert z (e ⁻¹' s) ∈ 𝓝 z := by
      rw [nhds_nhdsAdjoint_same]
      exact union_mem_sup singleton_mem_pure (hll' hs)
    rw [nhds_subtype_eq_comap]
    filter_upwards [preimage_mem_comap <| prod_mem_nhds hU this]
    suffices ∀ x' z', f x' = e z' → x' ∈ U → e z' ∈ s → z' = z by
      simpa [Pullback.snd, or_imp]
    intro x' z' hx'z' hx' hz'
    refine absurd ?_ (disjoint_left.1 hUS hx')
    rwa [mem_preimage, hx'z']
  obtain rfl : l = pure z := hlBot.eq_pure_iff.2 (hzo rfl)
  rcases (h Z z (pure z) e hlz).surjective z with ⟨⟨⟨x', z⟩, heq⟩, rfl⟩
  refine H x' heq (ClusterPt.mono ?_ (comap_mono hll'))
  simp only [map_pure, Pullback.snd, comap_pure, ← mem_closure_iff_clusterPt]
  apply subset_closure
  simp [heq]

end IsPullbackQuotientMap

structure IsProdQuotientMap (f : X → Y) : Prop where
  toQuotientMap : QuotientMap f
  -- TODO: should we try to reformulate it with filters?
  exists_finite_image_mem_nhds :
    ∀ V : Set Y, ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → (⋃₀ S = f ⁻¹' V) →
      ∀ y ∈ V, ∃ T ⊆ S, T.Finite ∧ exterior (f '' ⋃₀ T) ∈ 𝓝 y

theorem IsPullbackQuotientMap.isProdQuotientMap {f : X → Y} (h : IsPullbackQuotientMap f) :
    IsProdQuotientMap f where
  toQuotientMap := h.quotientMap
  exists_finite_image_mem_nhds V S hSo hSV y hy := by
    rw [isPullbackQuotientMap_iff_exists_finite_image_mem_nhds] at h
    rcases h.2 y S hSo (hSV.symm ▸ preimage_mono (singleton_subset_iff.2 hy)) with ⟨T, hTS, hTf, hT⟩
    exact ⟨T, hTS, hTf, mem_of_superset hT subset_exterior⟩

theorem IsOpenQuotientMap.isProdQuotientMap {f : X → Y} (h : IsOpenQuotientMap f) :
    IsProdQuotientMap f :=
  h.isPullbackQuotientMap.isProdQuotientMap

namespace IsProdQuotientMap
  
protected theorem id : IsProdQuotientMap (id : X → X) :=
  IsOpenQuotientMap.id.isProdQuotientMap

theorem IsProdQuotientMap.comp

-- theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
--     {f : X → Y} (hf : IsProdQuotientMap f) {g : X' → Y'} (hg : IsProdQuotientMap g) :
--     IsProdQuotientMap (Prod.map f g) := by
--   sorry

end IsProdQuotientMap
