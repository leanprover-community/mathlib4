import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.Option

open Function Set Filter TopologicalSpace Topology

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The fiber product `X ×_Y (Y × Z)`,
where `X` is mapped to `Y` by any funcion and `Y × Z` is sent to `Y` by the projection `Prod.fst`
is equivalent to `X × Z`.

This equivalence is useful, e.g., to transfer facts about pullbacks to products. -/
@[simps -fullyApplied apply symm_apply]
def Equiv.pullbackProdFst (f : X → Y) (Z : Type w) :
    ((f : X → Y).Pullback (Prod.fst : Y × Z → Y)) ≃ X × Z where
  toFun a := (a.fst, a.snd.2)
  invFun a := ⟨(a.1, f a.1, a.2), rfl⟩
  left_inv a := Subtype.eq <| Prod.ext rfl <| Prod.ext a.2 rfl
  right_inv _ := rfl

variable  [TopologicalSpace X] [TopologicalSpace Y]

@[fun_prop]
theorem Continuous.pullbackFst (f : X → Z) (g : Y → Z) :
    Continuous (Pullback.fst : f.Pullback g → X) := by
  unfold Pullback.fst; fun_prop

@[fun_prop]
theorem Continuous.pullbackSnd (f : X → Z) (g : Y → Z) :
    Continuous (Pullback.snd : f.Pullback g → Y) := by
  unfold Pullback.snd; fun_prop

/-- The fiber product `X ×_Y (Y × Z)`,
where `X` is mapped to `Y` by any funcion and `Y × Z` is sent to `Y` by the projection `Prod.fst`
is homeomorphic to `X × Z`.

This homeomorphism is useful, e.g., to transfer facts about pullbacks to products. -/
@[simps!]
def Homeomorph.pullbackProdFst (f : X → Y) (hf : Continuous f) (Z : Type*) [TopologicalSpace Z] :
    ((f : X → Y).Pullback (Prod.fst : Y × Z → Y)) ≃ₜ X × Z where
  toEquiv := .pullbackProdFst f Z
  continuous_toFun := by dsimp; fun_prop
  continuous_invFun := by dsimp; fun_prop

def Homeomorph.piOptionHomeomorphProd {ι : Type*} {X : Option ι → Type*}
    [∀ i, TopologicalSpace (X i)] : (∀ i, X i) ≃ₜ X none × (∀ i, X (some i)) where
  toEquiv := .piOptionEquivProd
  continuous_toFun := .prod_mk (by fun_prop) (by fun_prop)
  continuous_invFun := continuous_pi <| Option.rec (by fun_prop) <| by fun_prop

@[simps! -fullyApplied apply symm_apply toEquiv]
def Fin.insertNthHomeomorph {n : ℕ} (X : Fin (n + 1) → Type*) [∀ i, TopologicalSpace (X i)]
    (i : Fin (n + 1)) : (X i × ∀ j, X (i.succAbove j)) ≃ₜ (∀ j, X j) where
  toEquiv := Fin.insertNthEquiv X i
  continuous_invFun := Continuous.prod_mk (continuous_apply _) <|
    continuous_pi fun _ ↦ continuous_apply _
  continuous_toFun := continuous_fst.finInsertNth _  continuous_snd

@[mk_iff]
structure Topology.IsPullbackQuotientMap (f : X → Y) : Prop where
  continuous : Continuous f
  exists_clusterPt_comap {y : Y} {l : Filter Y} (h : ClusterPt y l) :
    ∃ x, f x = y ∧ ClusterPt x (comap f l)

nonrec theorem TopologicalSpace.IsTopologicalBasis.isPullbackQuotientMap_iff
    {B : Set (Set X)} (hB : IsTopologicalBasis B) {f : X → Y} :
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

theorem _root_.IsOpenQuotientMap.isPullbackQuotientMap {f : X → Y} (hf : IsOpenQuotientMap f) :
    IsPullbackQuotientMap f where
  continuous := hf.continuous
  exists_clusterPt_comap {y l} h := by
    rcases hf.surjective y with ⟨x, rfl⟩
    exact ⟨x, rfl, hf.isOpenMap.clusterPt_comap h⟩

theorem _root_.Homeomorph.isPullbackQuotientMap (f : X ≃ₜ Y) : IsPullbackQuotientMap f :=
  f.isOpenQuotientMap.isPullbackQuotientMap

namespace Topology.IsPullbackQuotientMap

protected theorem surjective {f : X → Y} (hf : IsPullbackQuotientMap f) : Surjective f := fun _ ↦
  (hf.exists_clusterPt_comap (.of_le_nhds le_rfl)).imp fun _ ↦ And.left

protected theorem isQuotientMap {f : X → Y} (hf : IsPullbackQuotientMap f) : IsQuotientMap f := by
  refine isQuotientMap_iff.2 ⟨hf.surjective, fun U ↦ ⟨fun h ↦ h.preimage hf.continuous, fun h ↦ ?_⟩⟩
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
  rw [← image_univ, Finset.subset_set_image_iff] at hTs
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

protected theorem comp [TopologicalSpace Z] {f : Y → Z} {g : X → Y}
    (hf : IsPullbackQuotientMap f) (hg : IsPullbackQuotientMap g) :
    IsPullbackQuotientMap (f ∘ g) where
  continuous := hf.continuous.comp hg.continuous
  exists_clusterPt_comap {z l} h := by
    rcases hf.exists_clusterPt_comap h with ⟨y, rfl, hy⟩
    rcases hg.exists_clusterPt_comap hy with ⟨x, rfl, hx⟩
    rw [comap_comap] at hx
    exact ⟨x, rfl, hx⟩

protected theorem pullback [TopologicalSpace Z] {f : X → Y}
    (hf : IsPullbackQuotientMap f) {g : Z → Y} (hg : Continuous g) :
    IsPullbackQuotientMap (Function.Pullback.snd : f.Pullback g → Z) where
  continuous := continuous_snd.comp continuous_subtype_val
  exists_clusterPt_comap {z l} h := by
    rcases hf.exists_clusterPt_comap (h.nhds_inf.map hg.continuousAt tendsto_map) with ⟨x, hxz, hxl⟩
    refine ⟨⟨(x, z), hxz⟩, rfl, ?_⟩
    rw [(IsEmbedding.subtypeVal.basis_nhds
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
    convert (Fin.insertNthHomeomorph Y 0).isPullbackQuotientMap.comp <|
      H₂.comp (Fin.insertNthHomeomorph X 0).symm.isPullbackQuotientMap with x i
    cases i using Fin.cases <;> rfl

protected theorem piMap {ι : Type*} {X Y : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (h : ∀ i, IsPullbackQuotientMap (f i)) :
    IsPullbackQuotientMap (Pi.map f) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    have := (ih fun i ↦ h (e i)).comp (Homeomorph.piCongrLeft e).symm.isPullbackQuotientMap
    convert (Homeomorph.piCongrLeft e).isPullbackQuotientMap.comp this
    ext x i
--    rcases e.surjective i with ⟨i, rfl⟩
    unfold Pi.map
    simp [Homeomorph.piCongrLeft]
  | h_empty => _
  | h_option => _
/-
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have H₁ : IsPullbackQuotientMap (fun (x : ∀ k, X (e.symm k)) i ↦ f _ (x i)) :=
    piMap_fin fun _ ↦ h _
  have H₂ : IsPullbackQuotientMap
      (fun x k ↦ f (e.symm k) (x (e.symm k)) : (∀ i, X i) → (∀ k, Y (e.symm k))) :=
    H₁.comp (Homeomorph.piCongrLeft e.symm).symm.isPullbackQuotientMap
  convert (Homeomorph.piCongrLeft e.symm).isPullbackQuotientMap.comp H₂ with x i
  rcases e.symm.surjective i with ⟨k, rfl⟩
  simp
-/

theorem of_forall_pullback_nhdsAdjoint {f : X → Y} (hf : Continuous f)
    (h : ∀ (Z : Type v) (z : Z) (l : Filter Z) (e : Z ≃ Y), Tendsto e l (𝓝 (e z)) →
      letI : TopologicalSpace Z := nhdsAdjoint z l
      IsQuotientMap (Pullback.snd : f.Pullback e → Z)) :
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
      IsQuotientMap (Pullback.snd : f.Pullback e → Z)) :
    IsPullbackQuotientMap f :=
  of_forall_pullback_nhdsAdjoint hf fun Z z l e he ↦ @h Z (nhdsAdjoint z l) e <| by
    rwa [continuous_nhdsAdjoint_dom]

end IsPullbackQuotientMap

end Topology
