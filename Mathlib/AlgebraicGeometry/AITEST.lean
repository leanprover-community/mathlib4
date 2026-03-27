import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Order

instance {X : Type*} [TopologicalSpace X] [T0Space X] [QuasiSober X] [PrespectralSpace X] :
    T2Space (WithConstructibleTopology X) where
  t2 x y hxy := by
    wlog h : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ U
    · obtain ⟨U, hUo, ⟨hxU, hyU⟩ | ⟨hyU, hxU⟩⟩ := exists_isOpen_xor'_mem (X := X) hxy
      · exact this _ _ hxy ⟨U, hUo, hxU, hyU⟩
      · obtain ⟨u, v, h1, h2, h3, h4, h5⟩ := this y x hxy.symm ⟨U, hUo, hyU, hxU⟩
        exact ⟨v, u, h2, h1, h4, h3, h5.symm⟩
    obtain ⟨U, hUo, ⟨hxU, hyU⟩⟩ := h
    obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis (X := X) |>.exists_subset_of_mem_open hxU hUo
    exact ⟨V, Vᶜ, hVc.isOpen_constructibleTopology_of_isOpen hVo,
      (compl_compl V ▸ hVc).isOpen_constructibleTopology_of_isClosed hVo.isClosed_compl,
      hxV, fun hyV => hyU (hVU hyV), disjoint_compl_right⟩

namespace WithConstructibleTopology

@[match_pattern] def toEquiv {α : Type*} [TopologicalSpace α] : α ≃ WithConstructibleTopology α :=
    Equiv.refl _

@[match_pattern] def ofEquiv {α : Type*} [TopologicalSpace α] : WithConstructibleTopology α ≃ α :=
    Equiv.refl _

lemma ofEquiv_continuous {X : Type*} [TopologicalSpace X] [a : PrespectralSpace X] :
    Continuous (ofEquiv (α := X)) := by
  have := a.1
  constructor
  intro U hU
  have := (TopologicalSpace.IsTopologicalBasis.isOpen_iff this).mp hU
  let Ux (x : U) := Exists.choose (this x x.2)
  let V := ⋃ (x : U), Ux x
  have opV : IsOpen V := by
    apply isOpen_iUnion
    intro x
    exact (Exists.choose_spec (this x x.2)).1.1
  have vu : V = U := by
    apply le_antisymm
    · exact Set.iUnion_subset fun x => (Exists.choose_spec (this x x.2)).2.2
    · intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, (Exists.choose_spec (this z hz)).2.1⟩
  rw [← vu]
  dsimp [V]
  simp only [Set.iUnion_coe_set, Set.preimage_iUnion]
  apply isOpen_iUnion
  intro x
  apply isOpen_iUnion
  intro hx
  have := Exists.choose_spec (this x hx)
  dsimp [Ux]
  apply IsCompact.isOpen_constructibleTopology_of_isOpen this.1.2 this.1.1

def lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
  WithConstructibleTopology X → WithConstructibleTopology Y := toEquiv.toFun ∘ f ∘ toEquiv.invFun

lemma lift_continuous {X Y : Type*}
    [TopologicalSpace X] [T0Space X] [QuasiSober X] [PrespectralSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] [PrespectralSpace Y]
    (f : SpectralMap X Y) : Continuous (lift f) := by
  erw [continuous_generateFrom_iff]
  intro U hU
  simp only [constructibleTopologySubbasis] at hU
  obtain h | h := hU
  · have a := f.2.2 h.1 h.2
    have b := f.2.1.1 U h.1
    have := IsCompact.isOpen_constructibleTopology_of_isOpen a b
    convert this
  · expose_names
    have o : @IsOpen Y inst_4 (U)ᶜ := by simp_all
    have a := f.2.2 o h.2
    have : IsClosed (f.toFun ⁻¹' U) := IsClosed.preimage f.2.1 h.1
    convert IsCompact.isOpen_constructibleTopology_of_isClosed a this using 1

lemma isCompact_of_preimage_singleton {X Y : Type*}
    [TopologicalSpace X] [T0Space X] [QuasiSober X] [PrespectralSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] [PrespectralSpace Y]
    (f : X → Y) (hf : IsSpectralMap f) (y : Y) :
    IsCompact (f ⁻¹' {y}) := by
  convert
    ((isClosed_singleton).preimage (lift_continuous ⟨f, hf⟩)).isCompact.image ofEquiv_continuous
  aesop

end WithConstructibleTopology

class IsLocallySpectral (X : Type*) [TopologicalSpace X] [T0Space X] [QuasiSober X]
    [PrespectralSpace X] : Prop where
  exists_spectral_nhd' (x : X) : ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ QuasiSeparatedSpace U ∧ x ∈ U

variable {X : Type*} [TopologicalSpace X] [T0Space X] [QuasiSober X] [PrespectralSpace X]

lemma IsLocallySpectral.exists_spectral_nhd [q : IsLocallySpectral X] (x : X) :
  ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ QuasiSeparatedSpace U ∧ x ∈ U := q.exists_spectral_nhd' x

variable {Y : Type*} [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] [PrespectralSpace Y]
    [IsLocallySpectral Y]

/-
lemma zsjdhh {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsQuasiSeparated U) (hV : IsOpen V) (hV' : IsCompact V) : IsQuasiSeparated (U ∩ V) := by

  sorry-/

open Topology
lemma IsSpectralMap.of_openEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [QuasiSeparatedSpace Y] {f : X → Y} (hf : IsOpenEmbedding f) :
    IsSpectralMap f := by
  constructor
  · exact hf.continuous
  · intro U hU hU'
    have : IsCompact (U ∩ (Set.range f)) := by
      have : IsCompact (Set.range f) := by
        convert CompactSpace.isCompact_univ.image hf.continuous
        exact Set.image_univ.symm
      /-
      Suppose we only know that f '' ⊤ is quasiseparated. Then we wish to know if f '' ⊤ ∩
      -/
      apply IsCompact.inter_of_isOpen hU' this hU hf.isOpen_range
    have := hf.isCompact_preimage' this (by simp)
    convert this using 1
    exact Set.preimage_inter_range.symm
open Set


variable [IsLocallySpectral X]

/--
A finite union of quasi-separated compact opens is quasi-separated, provided the pairwise
intersections are compact (and compact opens form a topological basis).

This is the topological analogue of Stacks Project Tag 01KS. The key step is showing that
if `W` is compact open with `W ⊆ ⋃ i, f i`, then `W ∩ f k` is compact. This uses the
`PrespectralSpace` hypothesis: we cover `W` by basis compact opens, each contained in some
`f j`, extract a finite subcover by compactness of `W`, and then each piece intersected
with `f k` is compact by quasi-separatedness of `f j`.
-/
lemma testing {X : Type*} [TopologicalSpace X] [PrespectralSpace X]
    {ι : Type*} {f : ι → Set X} [Finite ι]
    (h : ∀ (i : ι), IsOpen (f i) ∧ IsQuasiSeparated (f i) ∧ IsCompact (f i))
    (hpair : ∀ i j, IsCompact (f i ∩ f j)) :
    IsQuasiSeparated (⋃ i, f i) := by
  intro U V hUsub hUo hUc hVsub hVo hVc
  -- Key claim: for W compact open ⊆ ⋃ f i, W ∩ f k is compact
  suffices key : ∀ (W : Set X), W ⊆ ⋃ i, f i → IsOpen W → IsCompact W →
      ∀ k, IsCompact (W ∩ f k) by
    -- Decompose U ∩ V = ⋃ i, (U ∩ f i) ∩ (V ∩ f i)
    have cover : U ∩ V = ⋃ i, (U ∩ V ∩ f i) := by
      rw [← Set.inter_iUnion, Set.inter_eq_left.mpr (inter_subset_left.trans hUsub)]
    rw [cover]
    apply isCompact_iUnion; intro i
    have : U ∩ V ∩ f i = (U ∩ f i) ∩ (V ∩ f i) := by tauto_set
    rw [this]
    exact (h i).2.1 _ _ inter_subset_right (hUo.inter (h i).1) (key U hUsub hUo hUc i)
      inter_subset_right (hVo.inter (h i).1) (key V hVsub hVo hVc i)
  -- Prove the key claim
  intro W hWsub hWo hWc k
  have basis := PrespectralSpace.isTopologicalBasis (X := X)
  -- For each x ∈ W, find j(x) and a basis compact open B(x) ⊆ W ∩ f(j(x))
  have hx_data : ∀ x : ↥W, ∃ j : ι, ∃ B : Set X,
      IsOpen B ∧ IsCompact B ∧ x.1 ∈ B ∧ B ⊆ W ∧ B ⊆ f j := by
    intro ⟨x, hxW⟩
    obtain ⟨j, hxfj⟩ := mem_iUnion.mp (hWsub hxW)
    obtain ⟨B, ⟨hBo, hBc⟩, hxB, hBsub⟩ :=
      basis.exists_subset_of_mem_open (show x ∈ W ∩ f j from ⟨hxW, hxfj⟩) (hWo.inter (h j).1)
    exact ⟨j, B, hBo, hBc, hxB, hBsub.trans inter_subset_left, hBsub.trans inter_subset_right⟩
  choose j B hBo hBc hxB hBW hBf using hx_data
  -- Extract finite subcover from compactness of W
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover B (fun x => hBo x)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩)
  -- W ∩ f k = ⋃ x ∈ t, (B x ∩ f k) since each B x ⊆ W
  have eq : W ∩ f k = ⋃ x ∈ (t : Set ↥W), (B x ∩ f k) := by
    ext z; simp only [mem_inter_iff, mem_iUnion, Finset.mem_coe]; constructor
    · intro ⟨hzW, hzfk⟩
      obtain ⟨x, hxt, hzBx⟩ := mem_iUnion₂.mp (ht hzW)
      exact ⟨x, hxt, hzBx, hzfk⟩
    · rintro ⟨x, _, hzBx, hzfk⟩
      exact ⟨hBW x hzBx, hzfk⟩
  rw [eq]
  -- Finite union of compact sets is compact
  exact t.finite_toSet.isCompact_biUnion fun x _ => by
    -- B x ∩ f k is compact: use QS of f(j x) with B x and f k ∩ f(j x)
    have h_qs := (h (j x)).2.1 (B x) (f k ∩ f (j x))
      (hBf x) (hBo x) (hBc x)
      inter_subset_right ((h k).1.inter (h (j x)).1) (hpair k (j x))
    -- B x ∩ (f k ∩ f(j x)) = B x ∩ f k since B x ⊆ f(j x)
    rwa [← Set.inter_assoc, inter_eq_left.mpr (inter_subset_left.trans (hBf x))] at h_qs

lemma IsLocallySpectral.fiber (f : X → Y) (hf : IsSpectralMap f) (y : Y) :
    f ⁻¹' {y} = ⋂ s ∈ {x ∈ 𝓝 y | IsOpen x ∧ IsCompact x}, f ⁻¹' s := sorry



lemma IsLocallySpectral.isCompact_of_preimage_singleton (f : X → Y) (hf : IsSpectralMap f) (y : Y) :
    IsCompact (f ⁻¹' {y}) := by
  obtain ⟨U, hU⟩ := IsLocallySpectral.exists_spectral_nhd y
  -- Step 1: Get a spectral neighborhood U of y in Y
  obtain ⟨U, hUo, hUc, hUqs, hyU⟩ := IsLocallySpectral.exists_spectral_nhd y
  -- Step 2: f⁻¹(U) is compact and open
  have hfUc : IsCompact (f ⁻¹' U) := hf.isCompact_preimage_of_isOpen hUo hUc
  have hfUo : IsOpen (f ⁻¹' U) := hUo.preimage hf.continuous
  -- Step 3: Set up typeclass instances on f⁻¹(U) and U
  have oe_fU := hfUo.isOpenEmbedding_subtypeVal
  have oe_U := hUo.isOpenEmbedding_subtypeVal
  have : CompactSpace ↥(f ⁻¹' U) := isCompact_iff_compactSpace.mp hfUc
  have : T0Space ↥(f ⁻¹' U) := oe_fU.isEmbedding.t0Space
  have : QuasiSober ↥(f ⁻¹' U) := oe_fU.quasiSober
  have : PrespectralSpace ↥(f ⁻¹' U) := oe_fU.prespectralSpace
  have : T0Space ↥U := oe_U.isEmbedding.t0Space
  have : QuasiSober ↥U := oe_U.quasiSober
  have : PrespectralSpace ↥U := oe_U.prespectralSpace
  -- KEY SORRY: need f⁻¹(U) quasi-separated for compactSpace_withConstructibleTopology.
  -- For schemes this follows from the morphism being quasi-separated.
  have : QuasiSeparatedSpace ↥(f ⁻¹' U) := by
    constructor
    intro A B hA1 hA2 hB1 hB2

    /-
    `f ⁻¹ U` is covered by spectral opens since it is locally spectral - we just take the cover
    indexed by all the points in `f ⁻¹ U`

    Hence, we must have that `f ⁻¹ U` is covered by a finite number of quasiseparated sets,
    and hence must itself be quasiseparated?

    I don't think this is true. Indeed, a quasicompact morphism may not in general be
    quasiseparated
    -/


    sorry
  -- Step 4: Define the restriction g : f⁻¹(U) → U and show it is spectral
  let g : ↥(f ⁻¹' U) → ↥U := fun x => ⟨f x.val, x.prop⟩
  have hgc : Continuous g :=
    Continuous.subtype_mk (hf.continuous.comp continuous_subtype_val) _
  have hg : IsSpectralMap g := by
    refine ⟨hgc, fun S hSo hSc => ?_⟩
    -- S is a compact open of ↥U, hence corresponds to a compact open of Y contained in U
    have hSo' : IsOpen (Subtype.val '' S : Set Y) := oe_U.isOpenMap _ hSo
    have hSc' : IsCompact (Subtype.val '' S : Set Y) := hSc.image continuous_subtype_val
    -- f⁻¹(S') is compact since f is spectral
    have hK : IsCompact (f ⁻¹' (Subtype.val '' S)) :=
      hf.isCompact_preimage_of_isOpen hSo' hSc'
    -- g⁻¹(S) = Subtype.val⁻¹(f⁻¹(S')) and f⁻¹(S') ⊆ f⁻¹(U) = range Subtype.val
    have hKsub : f ⁻¹' (Subtype.val '' S) ⊆ Set.range (Subtype.val : ↥(f ⁻¹' U) → X) := by
      rw [Subtype.range_coe]
      exact Set.preimage_mono (Subtype.coe_image_subset U S)
    suffices g ⁻¹' S = Subtype.val ⁻¹' (f ⁻¹' (Subtype.val '' S)) by
      rw [this]
      exact oe_fU.toIsInducing.isCompact_preimage' hK hKsub
    ext ⟨x, hx⟩
    simp only [Set.mem_preimage, g]
    constructor
    · intro h
      exact ⟨⟨f x, hx⟩, h, rfl⟩
    · rintro ⟨⟨v, hv⟩, hS, hye⟩
      have : v = f x := hye
      subst this; exact hS
  -- Step 5: Apply the compact + quasi-separated version to g
  have key := WithConstructibleTopology.isCompact_of_preimage_singleton g hg ⟨y, hyU⟩
  -- Step 6: Transfer back via Subtype.val
  have hsub : f ⁻¹' {y} ⊆ f ⁻¹' U := Set.preimage_mono (Set.singleton_subset_iff.mpr hyU)
  convert key.image continuous_subtype_val using 1
  ext x; constructor
  · intro hx
    refine ⟨⟨x, hsub hx⟩, ?_, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, g]
    exact Subtype.ext (Set.mem_singleton_iff.mp hx)
  · rintro ⟨⟨a, ha⟩, hga, rfl⟩
    simpa [g] using hga
