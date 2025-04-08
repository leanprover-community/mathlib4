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

@[simps! (config := .asFn)]
def Homeomorph.piFinSuccAbove {n : ℕ} (X : Fin (n + 1) → Type*) [∀ i, TopologicalSpace (X i)]
    (i : Fin (n + 1)) : (∀ j, X j) ≃ₜ (X i × ∀ j, X (i.succAbove j)) where
  toEquiv := .piFinSuccAbove X i
  continuous_toFun := Continuous.prod_mk (continuous_apply _) <|
    continuous_pi fun _ ↦ continuous_apply _
  continuous_invFun := continuous_fst.fin_insertNth _  continuous_snd

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
        ∃ T ⊆ S, T.Finite ∧ ⋃ t ∈ T, f '' t ∈ 𝓝 y := by
  simp only [isPullbackQuotientMap_iff, clusterPt_iff_not_disjoint, disjoint_comap_iff_map]
  refine .and .rfl <| forall_congr' fun y ↦ ?_
  constructor
  · intro h S hSB hfS
    contrapose! h
    refine ⟨⨅ s ∈ S, 𝓟 ((f '' s)ᶜ), ?_, fun x hx ↦ ?_⟩
    · rw [iInf_subtype', (hasBasis_iInf_principal_finite _).disjoint_iff_right]
      rintro ⟨T, hTf, hTy⟩
      refine h (Subtype.val '' T) (image_subset_iff.2 fun x _ ↦ x.2) (hTf.image _) ?_
      simpa only [biUnion_image, image_iUnion, compl_iInter, compl_compl] using hTy
    · rcases @hfS x hx with ⟨s, hsS, hxs⟩
      rw [((basis_sets _).map f).disjoint_iff_left]
      refine ⟨s, hB.mem_nhds (hSB hsS) hxs, ?_⟩
      exact mem_iInf_of_mem s <| mem_iInf_of_mem hsS <| mem_principal_self _
  · intro h l H
    contrapose! H
    simp only [l.basis_sets.disjoint_iff_right] at H
    choose! s hsl hsx using H
    set S := B ∩ ⋃ (x : X) (_ : f x = y), {U : Set X | Disjoint U (f ⁻¹' s x)}
    obtain ⟨T, hTS, hTf, hTy⟩ : ∃ T ⊆ S, T.Finite ∧ ⋃ t ∈ T, f '' t ∈ 𝓝 y := by
      refine h S inter_subset_left fun x hx ↦ ?_
      rcases hB.mem_nhds_iff.1 (mem_map.1 <| hsx x hx) with ⟨U, hUB, hxU, hU⟩
      refine ⟨U, ⟨hUB, mem_iUnion₂.2 ⟨x, hx, ?_⟩⟩, hxU⟩
      rwa [mem_setOf, disjoint_left]
    refine disjoint_of_disjoint_of_mem disjoint_compl_right hTy ?_
    rw [compl_iUnion₂, biInter_mem hTf]
    intro U hUT
    rcases mem_iUnion₂.1 (hTS hUT).2 with ⟨x, hxy, hUx⟩
    filter_upwards [hsl x hxy] with y' hy' ⟨x', hx'U, hx'y⟩
    refine disjoint_left.mp hUx hx'U ?_
    rwa [mem_preimage, hx'y]

theorem isPullbackQuotientMap_iff_exists_finite_image_mem_nhds {f : X → Y} :
    IsPullbackQuotientMap f ↔
      Continuous f ∧ ∀ y : Y, ∀ S : Set (Set X),
        (∀ s ∈ S, IsOpen s) → (f ⁻¹' {y} ⊆ ⋃₀ S) → ∃ T ⊆ S, T.Finite ∧ ⋃ t ∈ T, f '' t ∈ 𝓝 y :=
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

/-- Auxiliary lemma. Use the next lemma instead. -/
private theorem piMap_fin {n : ℕ} {X Y : Fin n → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsPullbackQuotientMap (f i)) :
    IsPullbackQuotientMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  induction n with
  | zero => convert (Homeomorph.homeomorphOfUnique (∀ i, X i) (∀ i, Y i)).isPullbackQuotientMap
  | succ n ihn =>
    have H₁ : IsPullbackQuotientMap fun (x : ∀ i, X (.succ i)) i ↦ f (.succ i) (x i) :=
     ihn fun _ ↦ h _
    have H₂ := (h 0).prodMap H₁
    convert (Homeomorph.piFinSuccAbove Y 0).symm.isPullbackQuotientMap.comp <|
      H₂.comp (Homeomorph.piFinSuccAbove X 0).isPullbackQuotientMap with x i
    cases i using Fin.cases <;> rfl

protected theorem piMap {ι : Type*} {X Y : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsPullbackQuotientMap (f i)) :
    IsPullbackQuotientMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have H₁ : IsPullbackQuotientMap (fun (x : ∀ k, X (e.symm k)) i ↦ f _ (x i)) :=
    piMap_fin fun _ ↦ h _
  have H₂ : IsPullbackQuotientMap
      (fun x k ↦ f (e.symm k) (x (e.symm k)) : (∀ i, X i) → (∀ k, Y (e.symm k))) :=
    H₁.comp (Homeomorph.piCongrLeft e.symm).symm.isPullbackQuotientMap
  convert (Homeomorph.piCongrLeft e.symm).isPullbackQuotientMap.comp H₂ with x i
  rcases e.symm.surjective i with ⟨k, rfl⟩
  simp

theorem of_forall_pullback_nhdsAdjoint {f : X → Y} (hf : Continuous f)
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

theorem of_forall_pullback {f : X → Y} (hf : Continuous f)
    (h : ∀ (Z : Type v) [TopologicalSpace Z] (e : Z ≃ Y), Continuous e →
      QuotientMap (Pullback.snd : f.Pullback e → Z)) :
    IsPullbackQuotientMap f :=
  of_forall_pullback_nhdsAdjoint hf fun Z z l e he ↦ @h Z (nhdsAdjoint z l) e <| by
    -- TODO: add `continuous_nhdsAdjoint_dom`
    simp_rw [continuous_iff_le_induced, gc_nhds _ _, nhds_induced, ← tendsto_iff_comap, he]

end IsPullbackQuotientMap

structure IsProdQuotientMap (f : X → Y) : Prop where
  toQuotientMap : QuotientMap f
  -- TODO: should we try to reformulate it with filters?
  exists_finite_exterior_biUnion_mem_nhds' :
    ∀ V : Set Y, ∀ S : Set (Set X), IsOpen V → (∀ s ∈ S, IsOpen s) → (⋃₀ S = f ⁻¹' V) →
      ∀ y ∈ V, ∃ T ⊆ S, T.Finite ∧ exterior (⋃ t ∈ T, f '' t) ∈ 𝓝 y

theorem IsPullbackQuotientMap.isProdQuotientMap {f : X → Y} (h : IsPullbackQuotientMap f) :
    IsProdQuotientMap f where
  toQuotientMap := h.quotientMap
  exists_finite_exterior_biUnion_mem_nhds' V S _ hSo hSV y hy := by
    rw [isPullbackQuotientMap_iff_exists_finite_image_mem_nhds] at h
    rcases h.2 y S hSo (hSV.symm ▸ preimage_mono (singleton_subset_iff.2 hy)) with ⟨T, hTS, hTf, hT⟩
    exact ⟨T, hTS, hTf, mem_of_superset hT subset_exterior⟩

theorem IsOpenQuotientMap.isProdQuotientMap {f : X → Y} (h : IsOpenQuotientMap f) :
    IsProdQuotientMap f :=
  h.isPullbackQuotientMap.isProdQuotientMap

theorem Homeomorph.isProdQuotientMap (f : X ≃ₜ Y) : IsProdQuotientMap f :=
  f.isPullbackQuotientMap.isProdQuotientMap

namespace IsProdQuotientMap

protected theorem continuous {f : X → Y} (hf : IsProdQuotientMap f) : Continuous f :=
  hf.toQuotientMap.continuous

theorem exists_finite_exterior_biUnion_mem_nhds {ι : Type*} {f : X → Y} (hf : IsProdQuotientMap f)
    {V : Set Y} {I : Set ι} {s : ι → Set X} {y : Y} (hSo : ∀ i ∈ I, IsOpen (s i))
    (hsV : f ⁻¹' V ⊆ ⋃ i ∈ I, s i) (hy : V ∈ 𝓝 y) :
    ∃ T ⊆ I, T.Finite ∧ exterior (⋃ i ∈ T, f '' s i) ∈ 𝓝 y := by
  let S' := (s · ∩ f ⁻¹' interior V) '' I
  have hS'o : ∀ s ∈ S', IsOpen s :=
    forall_mem_image.2 fun s hs ↦ (hSo s hs).inter (isOpen_interior.preimage hf.continuous)
  have hS'V : ⋃₀ S' = f ⁻¹' interior V := by
    simp only [S', sUnion_image, ← iUnion_inter, inter_eq_right]
    exact (preimage_mono interior_subset).trans hsV
  rw [← mem_interior_iff_mem_nhds] at hy
  have := hf.exists_finite_exterior_biUnion_mem_nhds' _ _ isOpen_interior hS'o hS'V y hy
  rcases exists_subset_image_finite_and.1 this with ⟨T, hTS, hTf, hT⟩
  refine ⟨T, hTS, hTf, mem_of_superset hT <| exterior_mono ?_⟩
  rw [biUnion_image]
  gcongr
  exact inter_subset_left

protected theorem id : IsProdQuotientMap (id : X → X) :=
  IsOpenQuotientMap.id.isProdQuotientMap

theorem of_quotientMap_nhdsAdjoint_prodMap_id {f : X → Y}
    (h : ∀ U : Opens Y, ∀ l : Filter (Opens Y),
      letI := nhdsAdjoint U l
      QuotientMap (Prod.map f id : X × Opens Y → Y × Opens Y)) :
    IsProdQuotientMap f := by
  -- letI := TopologicalSpace.dayKelly (Opens Y)
  have hsurj : Surjective f := fun y ↦ by
    letI := nhdsAdjoint (⊥ : Opens Y) ⊥
    let ⟨⟨x, _⟩, hx⟩ := (h _ _).surjective (y, ⊥)
    exact ⟨x, congr_arg Prod.fst hx⟩
  have hquot : QuotientMap f := by
    refine quotientMap_iff.2 ⟨hsurj, fun U ↦ ?_⟩
    letI := nhdsAdjoint (⊥ : Opens Y) ⊥
    rw [← (quotientMap_fst (Y := Opens Y)).isOpen_preimage,
      ← (quotientMap_fst (X := X) (Y := Opens Y)).isOpen_preimage, ← (h _ _).isOpen_preimage]
    rfl
  refine ⟨hquot, fun V S hVo hSo hS y hyV ↦ ?_⟩
  lift V to Opens Y using hVo
  set l : Filter (Opens Y) := ⨅ s ∈ S, 𝓟 {W : Opens Y | MapsTo f s W}
  letI := nhdsAdjoint V l
  have ho : IsOpen {(y, W) : Y × Opens Y | y ∈ W} := by
    rw [← (h _ _).isOpen_preimage, isOpen_iff_mem_nhds]
    rintro ⟨x, W⟩ (hxW : f x ∈ W)
    rcases eq_or_ne W V with rfl | hW
    · obtain ⟨s, hsS, hxs⟩ : x ∈ ⋃₀ S := by rwa [hS]
      have : {W : Opens Y | MapsTo f s W} ∈ 𝓝 W := by
        rw [nhds_nhdsAdjoint_same, mem_sup, mem_pure]
        refine ⟨fun x' hx' ↦ ?_, mem_iInf_of_mem s <| mem_iInf_of_mem hsS (mem_principal_self _)⟩
        rw [← mem_preimage, ← hS]
        exact ⟨s, hsS, hx'⟩
      filter_upwards [prod_mem_nhds ((hSo s hsS).mem_nhds hxs) this]
      rintro ⟨x', U⟩ ⟨hx's, hU⟩
      exact hU hx's
    · rw [nhds_prod_eq, nhds_nhdsAdjoint_of_ne _ hW, prod_pure, mem_map]
      filter_upwards [(W.isOpen.preimage hquot.continuous).mem_nhds hxW] with _ using id
  rcases mem_nhds_prod_iff.1 (ho.mem_nhds hyV) with ⟨U, hyU, W, hVW, hUW⟩
  simp only [nhds_nhdsAdjoint_same, mem_sup, l, iInf_subtype', mem_pure, mem_iInf', mem_principal]
    at hVW
  rcases hVW with ⟨h, t, htf, u, hu, -, rfl, -⟩
  refine ⟨(↑) '' t, Subtype.coe_image_subset S t, htf.image _,  mem_of_superset hyU ?_⟩
  simp only [biUnion_image, mem_iInter, subset_exterior_iff] at h ⊢
  refine fun W hWo hW x' hx' ↦ ?_
  lift W to Opens Y using hWo
  simp only [iUnion₂_subset_iff, ← mapsTo'] at hW
  exact @hUW (x', W) ⟨hx', mem_iInter₂.2 fun i hi ↦ hu i (hW i hi)⟩

theorem of_quotientMap_prodMap_id {f : X → Y}
    (h : ∀ (Z : Type v) [TopologicalSpace Z], QuotientMap (Prod.map f id : X × Z → Y × Z)) :
    IsProdQuotientMap f :=
  of_quotientMap_nhdsAdjoint_prodMap_id fun U l ↦ @h _ (nhdsAdjoint U l)

theorem of_basis {B : Set (Set X)} {ι : Y → Sort*} {pi : ∀ y, ι y → Prop} {si : ∀ y, ι y → Set Y}
    (hB : TopologicalSpace.IsTopologicalBasis B) (hb : ∀ y, (𝓝 y).HasBasis (pi y) (si y))
    {f : X → Y} (h₁ : QuotientMap f)
    (h₂ : ∀ S ⊆ B, ∀ (y : Y) (i : ι y), pi y i → f ⁻¹' (si y i) ⊆ ⋃₀ S →
      ∃ T ⊆ S, T.Finite ∧ exterior (⋃ t ∈ T, f '' t) ∈ 𝓝 y) : IsProdQuotientMap f := by
  refine ⟨h₁, fun V S hVo hSo hS y hy ↦ ?_⟩
  rcases (hb y).mem_iff.1 (hVo.mem_nhds hy) with ⟨i, hpi, hsi⟩
  set S' := {s ∈ B | ∃ t ∈ S, s ⊆ t}
  have hS'i : f ⁻¹' si y i ⊆ ⋃₀ S' := by
    intro x hx
    obtain ⟨t, htS, hxt⟩ : x ∈ ⋃₀ S := hS ▸ preimage_mono hsi hx
    rcases hB.mem_nhds_iff.1 ((hSo t htS).mem_nhds hxt) with ⟨s, hsB, hxs, hst⟩
    exact ⟨s, ⟨hsB, t, htS, hst⟩, hxs⟩
  rcases h₂ S' inter_subset_left y i hpi hS'i with ⟨T, hTS', hTf, hTy⟩
  choose! u huS hut using fun s (h : s ∈ S') ↦ h.2
  refine ⟨u '' T, image_subset_iff.2 fun s hs ↦ huS _ (hTS' hs), hTf.image _,
    mem_of_superset hTy ?_⟩
  rw [biUnion_image]
  gcongr with s hs
  exact hut s (hTS' hs)

-- Helper lemma. Use `prodMap_id` instead
private theorem quotientMap_prodMap_id {f : X → Y} (hf : IsProdQuotientMap f)
    (Z : Type*) [TopologicalSpace Z] : QuotientMap (Prod.map f id : X × Z → Y × Z) := by
  refine quotientMap_iff.2 ⟨hf.toQuotientMap.surjective.prodMap surjective_id, fun U ↦ ?_⟩
  refine ⟨fun hU ↦ hU.preimage (hf.continuous.prod_map continuous_id),
    fun hU ↦ isOpen_iff_mem_nhds.2 ?_⟩
  have ho {z : Z} : IsOpen {y | (y, z) ∈ U} := by
    rw [← hf.toQuotientMap.isOpen_preimage]
    exact hU.preimage (Continuous.Prod.mk_left z)
  rintro ⟨y, z⟩ hyz
  rcases hf.toQuotientMap.surjective y with ⟨x, rfl⟩
  choose! u v huo hxu hvo hzv huvU
    using fun (x : X) (h : (f x, z) ∈ U) ↦ mem_nhds_prod_iff'.1 (hU.mem_nhds h)
  have hsub : f ⁻¹' {x | (x, z) ∈ U} ⊆ ⋃ i ∈ {x | (f x, z) ∈ U}, u i := fun x hx ↦
    mem_iUnion₂_of_mem hx (hxu x hx)
  rcases hf.exists_finite_exterior_biUnion_mem_nhds (I := {x | (f x, z) ∈ U})
    huo hsub (ho.mem_nhds hyz) with ⟨T, hT, hTf, hnhds'⟩
  have : ⋂ i ∈ T, v i ∈ 𝓝 z :=
    (biInter_mem hTf).2 fun i hi ↦ (hvo _ (hT hi)).mem_nhds (hzv _ (hT hi))
  filter_upwards [prod_mem_nhds hnhds' this] with (y', z') ⟨hy', hz'⟩
  simp only [mem_iInter₂, mem_exterior, iUnion_subset_iff, image_subset_iff] at hy' hz'
  exact hy' _ ho (fun i hi x' hx' ↦ @huvU _ (hT hi) (_, _) ⟨hx', hz' i hi⟩)

theorem prodMap_id {f : X → Y} (hf : IsProdQuotientMap f) (Z : Type*) [TopologicalSpace Z] :
    IsProdQuotientMap (Prod.map f id : X × Z → Y × Z) :=
  of_quotientMap_prodMap_id fun T _ ↦
    (Homeomorph.prodAssoc Y Z T).symm.quotientMap.comp <|
      (hf.quotientMap_prodMap_id (Z × T)).comp (Homeomorph.prodAssoc X Z T).quotientMap

protected theorem comp {Z : Type*} [TopologicalSpace Z] {f : Y → Z} {g : X → Y}
    (hf : IsProdQuotientMap f) (hg : IsProdQuotientMap g) : IsProdQuotientMap (f ∘ g) :=
  of_quotientMap_prodMap_id fun T _ ↦
    (hf.quotientMap_prodMap_id T).comp (hg.quotientMap_prodMap_id T)

theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → Y} (hf : IsProdQuotientMap f) {g : X' → Y'} (hg : IsProdQuotientMap g) :
    IsProdQuotientMap (Prod.map f g) :=
  have H₁ : IsProdQuotientMap (Prod.map f id : X × X' → Y × X') := hf.prodMap_id _
  have H₂ : IsProdQuotientMap (Prod.map g id : X' × Y → Y' × Y) := hg.prodMap_id _
  have H₃ : IsProdQuotientMap (Prod.map id g: Y × X' → Y × Y') :=
    (Homeomorph.prodComm _ _).isProdQuotientMap.comp
      (H₂.comp (Homeomorph.prodComm _ _).isProdQuotientMap)
  H₃.comp H₁

/-- Auxiliary lemma. Use the next lemma instead. -/
private theorem piMap_fin {n : ℕ} {X Y : Fin n → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsProdQuotientMap (f i)) :
    IsProdQuotientMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  induction n with
  | zero => convert (Homeomorph.homeomorphOfUnique (∀ i, X i) (∀ i, Y i)).isProdQuotientMap
  | succ n ihn =>
    have H₁ : IsProdQuotientMap fun (x : ∀ i, X (.succ i)) i ↦ f (.succ i) (x i) :=
     ihn fun _ ↦ h _
    have H₂ := (h 0).prodMap H₁
    convert (Homeomorph.piFinSuccAbove Y 0).symm.isProdQuotientMap.comp <|
      H₂.comp (Homeomorph.piFinSuccAbove X 0).isProdQuotientMap with x i
    cases i using Fin.cases <;> rfl

protected theorem piMap {ι : Type*} {X Y : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsProdQuotientMap (f i)) :
    IsProdQuotientMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have H₁ : IsProdQuotientMap (fun (x : ∀ k, X (e.symm k)) i ↦ f _ (x i)) :=
    piMap_fin fun _ ↦ h _
  have H₂ : IsProdQuotientMap
      (fun x k ↦ f (e.symm k) (x (e.symm k)) : (∀ i, X i) → (∀ k, Y (e.symm k))) :=
    H₁.comp (Homeomorph.piCongrLeft e.symm).symm.isProdQuotientMap
  convert (Homeomorph.piCongrLeft e.symm).isProdQuotientMap.comp H₂ with x i
  rcases e.symm.surjective i with ⟨k, rfl⟩
  simp

end IsProdQuotientMap

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

theorem continuous_cod_dayKelly_opens_of_isOpen {f : X → Opens Y}
    (h : IsOpen {x : X × Y | x.2 ∈ f x.1}) : Continuous[_, .dayKelly _] f := by
  letI : TopologicalSpace (Opens Y) := .dayKelly _
  refine ⟨fun U hU ↦ isOpen_iff_mem_nhds.2 fun x (hx : f x ∈ U) ↦ ?_⟩
  have : ∀ y ∈ f x, ∃ (u : Opens X) (v : Opens Y), x ∈ u ∧ y ∈ v ∧
      (u ×ˢ v : Set (X × Y)) ⊆ {x | x.2 ∈ f x.1} := by
    intro y hy
    rcases isOpen_prod_iff.1 h x y hy with ⟨u, v, huo, hvo, h⟩
    exact ⟨⟨u, huo⟩, ⟨v, hvo⟩, h⟩
  choose! u v hu hv huv using this
  have : f x = sSup (v '' f x) := by
    simp only [sSup_image, le_antisymm_iff, iSup_le_iff]
    refine ⟨fun y hy ↦ ?_, fun y hy y' hy' ↦ @huv y hy (x, y') ⟨hu y hy, hy'⟩⟩
    simp only [Opens.coe_iSup, mem_iUnion]
    exact ⟨y, hy, hv y hy⟩
  rcases exists_subset_image_finite_and.1 (hU.2 _ (this ▸ hx)) with ⟨t, htx, htf, ht⟩
  filter_upwards [(biInter_mem htf).2 fun y hy ↦ (u y).isOpen.mem_nhds (hu y (htx hy))] with x' hx'
  refine hU.1 (sSup_le <| forall_mem_image.2 fun y' hy' y'' hy'' ↦ ?_) ht
  exact @huv _ (htx hy') (_, _) ⟨mem_iInter₂.1 hx' _ hy', hy''⟩

namespace ProdQuotientMapSpace

variable (X) in
def admissibleTopologies : Set (TopologicalSpace (Opens X)) :=
  {_t : TopologicalSpace (Opens X) | IsOpen {(x, U) : X × Opens X | x ∈ U}}

theorem mem_admissibleTopologies {t : TopologicalSpace (Opens X)} :
    t ∈ admissibleTopologies X ↔ IsOpen {(x, U) : X × Opens X | x ∈ U} := .rfl

@[nolint unusedArguments]
def Fiber (_ : admissibleTopologies X) := Opens X

instance (t : admissibleTopologies X) : TopologicalSpace (Fiber t) := t.1

variable (X) in
abbrev TotalSpace : Type u := Σ t : admissibleTopologies X, Fiber t

theorem nhdsAdjoint_mem_admissibleTopologies {U : Opens X} {l : Filter (Opens X)}
    (h : ∀ x ∈ U, ∃ U' : Opens X, x ∈ U' ∧ ∃ W ∈ l, U ∈ W ∧ ∀ x' ∈ U', ∀ V ∈ W, x' ∈ V) :
    nhdsAdjoint U l ∈ admissibleTopologies X := by
  letI := nhdsAdjoint U l
  simp only [mem_admissibleTopologies, isOpen_iff_mem_nhds, Prod.forall, mem_nhds_prod_iff]
  intro x V hx
  rcases eq_or_ne U V with rfl | hne
  · rcases h x hx with ⟨U', hU', W, hWl, hUW, hW⟩
    refine ⟨U', U'.isOpen.mem_nhds hU', W, ?_, prod_subset_iff.2 hW⟩
    rw [nhds_nhdsAdjoint_same]
    exact ⟨hUW, hWl⟩
  · refine ⟨V, V.isOpen.mem_nhds hx, {V}, IsOpen.mem_nhds (absurd · hne) rfl, ?_⟩
    rintro ⟨x, V⟩ ⟨hx, rfl⟩
    exact hx

theorem bot_mem_admissibleTopologies : ⊥ ∈ admissibleTopologies X := by
  rw [← (gc_nhds (⊥ : Opens X)).l_bot]
  exact nhdsAdjoint_mem_admissibleTopologies fun _ ↦ False.elim

theorem sSup_admissibleTopologies : sSup (admissibleTopologies X) = .dayKelly _ := by
  refine le_antisymm (sSup_le fun t ht ↦ ?_) fun U hU ↦ ?_
  · rw [← continuous_id_iff_le]
    exact continuous_cod_dayKelly_opens_of_isOpen (IsOpen.preimage continuous_swap ht)
  rw [isOpen_sSup_iff] at hU
  constructor
  · intro V W hle hV
    have : nhdsAdjoint V (𝓟 (Ici V)) ∈ admissibleTopologies X := by
      refine nhdsAdjoint_mem_admissibleTopologies fun x hx ↦ ?_
      exact ⟨V, hx, Ici V, mem_principal_self _, left_mem_Ici, fun x' hx' V' hV' ↦ hV' hx'⟩
    exact hU _ this hV hle
  · intro V hV
    set l : Filter (Opens X) := ⨅ v ∈ V, 𝓟 (Ici v)
    have : nhdsAdjoint (sSup V) l ∈ admissibleTopologies X := by
      refine nhdsAdjoint_mem_admissibleTopologies fun x hx ↦ ?_
      rcases Opens.mem_sSup.1 hx with ⟨W, hWV, hxW⟩
      exact ⟨W, hxW, Ici W, mem_iInf_of_mem W <| mem_iInf_of_mem hWV <| mem_principal_self _,
        le_sSup hWV, fun x' hx' s hs ↦ hs hx'⟩
    specialize hU _ this hV
    simp only [l, iInf_subtype', mem_iInf', mem_principal] at hU
    rcases hU with ⟨t, htf, v, hv, -, rfl, -⟩
    refine ⟨(↑) '' t, Subtype.coe_image_subset _ _, htf.image _, mem_iInter₂.2 fun i hi ↦ hv i ?_⟩
    rw [mem_Ici, sSup_image]
    exact le_iSup₂_of_le i hi le_rfl

theorem dayKelly_mem_admissibleTopologies [ProdQuotientMapSpace X] :
    .dayKelly (Opens X) ∈ admissibleTopologies X := by
  letI := TopologicalSpace.dayKelly (Opens X)
  simp only [mem_admissibleTopologies, isOpen_prod_iff]
  intro x U hx
  rcases exists_dayKelly_isOpen U x hx with ⟨V, hUV, hVo, hVx⟩
  refine ⟨interior (⋂ s ∈ V, s), V, isOpen_interior, hVo, mem_interior_iff_mem_nhds.2 hVx, hUV, ?_⟩
  intro ⟨x', W⟩ ⟨hx', hW⟩
  exact mem_iInter₂.1 (interior_subset hx') _ hW

theorem iff_dayKelly_mem_admissibleTopologies :
    ProdQuotientMapSpace X ↔ .dayKelly (Opens X) ∈ admissibleTopologies X := by
  letI := TopologicalSpace.dayKelly (Opens X)
  refine ⟨@dayKelly_mem_admissibleTopologies _ _, fun h ↦ ⟨fun U x hx ↦ ?_⟩⟩
  rcases isOpen_prod_iff.1 h x U hx with ⟨V, W, hVo, hWo, hxV, hUW, hVW⟩
  refine ⟨W, hUW, hWo, mem_nhds_iff.2 ⟨V, subset_iInter₂ ?_, hVo, hxV⟩⟩
  exact fun w hw x' hx' ↦ hVW (mk_mem_prod hx' hw)

theorem quotientMap_snd_totalSpace :
    letI := TopologicalSpace.dayKelly (Opens X)
    QuotientMap fun x : TotalSpace X ↦ x.2 := by
  letI := TopologicalSpace.dayKelly (Opens X)
  refine ⟨fun x ↦ ⟨⟨⟨⊥, bot_mem_admissibleTopologies⟩, x⟩, rfl⟩, ?_⟩
  unfold instTopologicalSpaceSigma instTopologicalSpaceFiber
  simp_rw [coinduced_iSup, iSup_subtype, coinduced_compose, (· ∘ ·), ← Function.id_def,
    coinduced_id, ← sSup_eq_iSup, sSup_admissibleTopologies]

theorem of_quotientMap_prodMap_id_totalSpace
    (h : letI := TopologicalSpace.dayKelly (Opens X)
      QuotientMap (Prod.map (fun U : TotalSpace X ↦ U.snd) id : TotalSpace X × X → Opens X × X)) :
    ProdQuotientMapSpace X := by
  letI := TopologicalSpace.dayKelly (Opens X)
  rw [iff_dayKelly_mem_admissibleTopologies, mem_admissibleTopologies,
    ← (Homeomorph.prodComm _ _).quotientMap.isOpen_preimage, ← h.isOpen_preimage,
    ← Homeomorph.sigmaProdDistrib.symm.quotientMap.isOpen_preimage,
    isOpen_sigma_iff]
  rintro ⟨t, ht⟩
  exact (mem_admissibleTopologies.1 ht).preimage continuous_swap

end ProdQuotientMapSpace

namespace QuotientMap

theorem prodMap_id {f : X → Y} (hf : QuotientMap f)
    (Z : Type*) [TopologicalSpace Z] [ProdQuotientMapSpace Z] :
    QuotientMap (Prod.map f id : X × Z → Y × Z) := by
  refine quotientMap_iff.2 ⟨hf.surjective.prodMap surjective_id, fun U ↦ ?_⟩
  refine ⟨fun hU ↦ hU.preimage (hf.continuous.prod_map continuous_id), fun hU ↦ ?_⟩
  letI := TopologicalSpace.dayKelly (Opens Z)
  have ho : ∀ y : Y, IsOpen {z | (y, z) ∈ U} :=
    hf.surjective.forall.2 fun x ↦ hU.preimage (Continuous.Prod.mk _)
  set g : Y → Opens Z := fun y ↦ ⟨{z | (y, z) ∈ U}, ho y⟩
  have hg : Continuous g := by
    rw [hf.continuous_iff]
    exact continuous_cod_dayKelly_opens_of_isOpen hU
  have := (ProdQuotientMapSpace.dayKelly_mem_admissibleTopologies (X := Z)).out.preimage
    (continuous_id.prod_map hg)
  exact this.preimage continuous_swap

theorem id_prodMap {f : X → Y} (hf : QuotientMap f)
    (Z : Type*) [TopologicalSpace Z] [ProdQuotientMapSpace Z] :
    QuotientMap (Prod.map id f : Z × X → Z × Y) :=
  (Homeomorph.prodComm _ _).quotientMap.comp <|
    (hf.prodMap_id Z).comp (Homeomorph.prodComm _ _).quotientMap

theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    [ProdQuotientMapSpace X] [ProdQuotientMapSpace Y'] {f : X → Y} {g : X' → Y'}
    (hf : QuotientMap f) (hg : QuotientMap g) : QuotientMap (Prod.map f g) :=
  (hf.prodMap_id Y').comp (hg.id_prodMap X)

theorem prodMap' {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    [ProdQuotientMapSpace X'] [ProdQuotientMapSpace Y] {f : X → Y} {g : X' → Y'}
    (hf : QuotientMap f) (hg : QuotientMap g) : QuotientMap (Prod.map f g) :=
  (hg.id_prodMap Y).comp (hf.prodMap_id X')

end QuotientMap
