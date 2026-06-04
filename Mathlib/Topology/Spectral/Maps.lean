/-
Copyright (c) 2026 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Hom

/-!
# Properties of maps between spectral spaces

This file proves properties of maps between spectral spaces. The results are stated in terms of
individual typeclasses rather than for spectral spaces directly; they apply in particular to
spectral spaces, which satisfy all the required hypotheses.

## Main declarations

* `IsSpectralMap.constructibleTopology_eq_induced_of_isEmbedding`: For a spectral embedding
  `f : X → Y`, the constructible topology on `X` is the same as the topology induced by the
  constructible topology on `Y` via `f`.
* `isSpectralMap_iff_continuous_and_continuous_withConstructibleTopology`: A map `f : X → Y` is
  spectral if and only if it is continuous with respect to both the original topologies and the
  constructible topologies on `X` and `Y`.
* `IsEmbedding.isOpen_and_isCompact_iff_exists_of_isClosed_withConstructibleTopology_range`: For
  an embedding `f : X → Y` whose range is closed in the constructible topology on `Y`, a subset
  `s` of `X` is compact open if and only if it is the preimage of a compact open set in `Y`.
* `IsEmbedding.compactSpace_of_isClosed_withConstructibleTopology_range`: If `f : X → Y` is an
  embedding whose range is closed in the constructible topology on `Y`, then `X` is compact.
* `IsEmbedding.quasiSeparatedSpace_of_isClosed_withConstructibleTopology_range`: If `f : X → Y`
  is an embedding whose range is closed in the constructible topology on `Y`, then `X` is
  quasi-separated.
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [T : TopologicalSpace Y]

open TopologicalSpace Topology

lemma Topology.IsEmbedding.exists_of_isOpen_isCompact [PrespectralSpace Y]
    {f : X → Y} (hf : IsEmbedding f) {s : Set X} (hs1 : IsOpen s) (hs2 : IsCompact s) :
    ∃ o : Set Y, IsOpen o ∧ IsCompact o ∧ s = f ⁻¹' o := by
  obtain ⟨S, hS⟩ := eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _ (hf.eq_induced ▸
    IsTopologicalBasis.induced f (PrespectralSpace.isTopologicalBasis (X := Y))) s hs2 hs1
  have : ∀ s ∈ S, ∃ o : Set Y, IsOpen o ∧ IsCompact o ∧ s = f ⁻¹' o :=
    fun ⟨s, o, ⟨ho1, ho2⟩, hfos⟩ hsS => ⟨o, ho1, ho2, hfos.symm⟩
  choose! U hU1 hU2 hU3 using this
  refine ⟨⋃ s ∈ S, U s, isOpen_biUnion hU1, Finset.isCompact_biUnion S hU2, ?_⟩
  · exact (Set.sUnion_image _ _ ▸ hS) ▸ Set.biUnion_eq_iUnion _ _ ▸ Set.biUnion_eq_iUnion _ _ ▸
      Set.preimage_iUnion.symm ▸ Set.iUnion_congr fun ⟨t, ht⟩ => hU3 t ht

lemma IsSpectralMap.constructibleTopology_eq_induced_of_isEmbedding
    [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [PrespectralSpace Y]
    {f : X → Y} (hf1 : IsEmbedding f) (hf2 : IsSpectralMap f) :
    constructibleTopology X = induced f (constructibleTopology Y) := by
  change generateFrom (_ ∪ _) = induced f (generateFrom (_ ∪ _))
  refine induced_generateFrom_eq ▸ eq_of_le_of_ge (le_generateFrom fun s ⟨t, ht, hts⟩ => ?_)
    (le_generateFrom fun s hs => ?_)
  · refine ht.elim (fun ⟨ht1, ht2⟩ => ?_) (fun ⟨ht1, ht2⟩ => ?_)
    · exact hts ▸ (TopologicalSpace.le_def.1 <| constructibleTopology_le X) _
        (ht1.preimage hf1.continuous)
    · exact hts ▸ (isOpen_generateFrom_of_mem <|
        Or.intro_right _ ⟨ht1.preimage hf2.1, t.preimage_compl ▸ hf2.2 ht1.isOpen_compl ht2⟩)
  · refine isOpen_generateFrom_of_mem <| hs.elim (fun ⟨hs1, hs2⟩ => ?_) (fun ⟨hs1, hs2⟩ => ?_)
    · obtain ⟨o, ho1, ho2, hsfo⟩ := hf1.exists_of_isOpen_isCompact hs1 hs2
      exact ⟨o, Or.intro_left _ ⟨ho1, ho2⟩, hsfo.symm⟩
    · obtain ⟨t, ht1, ht2, hoft⟩ := hf1.exists_of_isOpen_isCompact hs1.isOpen_compl hs2
      exact ⟨tᶜ, Or.intro_right _ ⟨ht1.isClosed_compl, (compl_compl t).symm ▸ ht2⟩,
        t.preimage_compl.symm ▸ hoft ▸ compl_compl s⟩

lemma IsSpectralMap.continuous_withConstructibleTopology [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {f : X → Y} (hf : IsSpectralMap f) :
    Continuous (X := WithConstructibleTopology X) (Y := WithConstructibleTopology Y) f := by
  refine continuous_generateFrom_iff.2 fun s hs =>
    hs.elim (fun ⟨hs1, hs2⟩ => ?_) (fun ⟨hs1, hs2⟩ => ?_)
  · exact isOpen_generateFrom_of_mem <| Or.intro_left _ ⟨hf.1.isOpen_preimage s hs1, hf.2 hs1 hs2⟩
  · exact isOpen_generateFrom_of_mem <| Or.intro_right _
      ⟨hs1.preimage hf.1, s.preimage_compl ▸ hf.2 hs1.isOpen_compl hs2⟩

lemma isCompact_preimage_withConstructibleTopology_of_continuous
    [CompactSpace X] [QuasiSober X] [QuasiSeparatedSpace X]
    [PrespectralSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] {f : X → Y}
    (hf : Continuous (X := WithConstructibleTopology X) (Y := WithConstructibleTopology Y) f)
    {s : Set Y} (hs1 : IsOpen s) (hs2 : IsCompact s) :
    IsCompact (X := WithConstructibleTopology X) (f ⁻¹' s) :=
  IsClosed.isCompact <| IsClosed.preimage hf <|
    (@isOpen_compl_iff _ _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
      Or.intro_right _ ⟨hs1.isClosed_compl, (compl_compl s).symm ▸ hs2⟩

lemma isSpectralMap_of_continuous_of_continuous_withConstructibleTopology
    [CompactSpace X] [QuasiSober X] [QuasiSeparatedSpace X] [PrespectralSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {f : X → Y} (hf1 : Continuous f)
    (hf2 : Continuous (X := WithConstructibleTopology X) (Y := WithConstructibleTopology Y) f) :
    IsSpectralMap f :=
  ⟨hf1, fun _ hs1 hs2 => isCompact_of_le_of_isCompact (constructibleTopology_le X) <|
    isCompact_preimage_withConstructibleTopology_of_continuous hf2 hs1 hs2⟩

lemma isSpectralMap_iff_continuous_and_continuous_withConstructibleTopology
    [CompactSpace X] [QuasiSober X] [QuasiSeparatedSpace X] [PrespectralSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X → Y) :
    IsSpectralMap f ↔ Continuous f ∧
      Continuous (X := WithConstructibleTopology X) (Y := WithConstructibleTopology Y) f :=
  ⟨fun hf => ⟨hf.toContinuous, hf.continuous_withConstructibleTopology⟩,
    fun ⟨hf1, hf2⟩ => isSpectralMap_of_continuous_of_continuous_withConstructibleTopology hf1 hf2⟩

namespace Topology.IsEmbedding

lemma isOpen_and_isCompact_iff_exists_of_isClosed_withConstructibleTopology_range [CompactSpace Y]
    [QuasiSober Y] [QuasiSeparatedSpace Y] [PrespectralSpace Y] {f : X → Y} (hf : IsEmbedding f)
    (hfX : IsClosed (X := WithConstructibleTopology Y) (Set.range f)) (s : Set X) :
    (IsOpen s ∧ IsCompact s) ↔ ∃ o : Set Y, IsOpen o ∧ IsCompact o ∧ s = f ⁻¹' o := by
  refine ⟨fun ⟨hs1, hs2⟩ => hf.exists_of_isOpen_isCompact hs1 hs2,
    fun ⟨o, ho1, ho2, hsfo⟩ => ⟨hsfo ▸ IsOpen.preimage hf.continuous ho1, ?_⟩⟩
  · have h1 : IsClosed (X := WithConstructibleTopology Y) o :=
      isOpen_compl_iff.1 <| isOpen_generateFrom_of_mem <|
        Or.intro_right _ ⟨ho1.isClosed_compl, (compl_compl o).symm ▸ ho2⟩
    have h2 : IsCompact (f '' s) :=
      (hsfo ▸ Set.image_preimage_eq_range_inter.symm) ▸
        (isCompact_of_le_of_isCompact (constructibleTopology_le Y) (hfX.inter h1).isCompact)
    exact (hf.isCompact_iff).2 h2

lemma compactSpace_of_isClosed_withConstructibleTopology_range [CompactSpace Y] [QuasiSober Y]
    [QuasiSeparatedSpace Y] [PrespectralSpace Y] {f : X → Y} (hf : IsEmbedding f)
    (hfX : IsClosed (X := WithConstructibleTopology Y) (Set.range f)) : CompactSpace X :=
  ⟨((hf.isOpen_and_isCompact_iff_exists_of_isClosed_withConstructibleTopology_range hfX Set.univ).2
    ⟨Set.univ, isOpen_univ, isCompact_univ, Set.preimage_univ.symm⟩).2⟩

lemma quasiSeparatedSpace_of_isClosed_withConstructibleTopology_range
    [CompactSpace Y] [QuasiSober Y] [QuasiSeparatedSpace Y] [PrespectralSpace Y] {f : X → Y}
    (hf : IsEmbedding f) (hfX : IsClosed (X := WithConstructibleTopology Y) (Set.range f)) :
    QuasiSeparatedSpace X := by
  refine ⟨fun s t hs1 hs2 ht1 ht2 => ?_⟩
  · obtain ⟨u, hu1, hu2, hsfu⟩ :=
      (hf.isOpen_and_isCompact_iff_exists_of_isClosed_withConstructibleTopology_range hfX s).1
        ⟨hs1, hs2⟩
    obtain ⟨v, hv1, hv2, htfv⟩ :=
      (hf.isOpen_and_isCompact_iff_exists_of_isClosed_withConstructibleTopology_range hfX t).1
        ⟨ht1, ht2⟩
    exact hsfu ▸ htfv ▸ Set.preimage_inter ▸
      ((hf.isOpen_and_isCompact_iff_exists_of_isClosed_withConstructibleTopology_range
        hfX (f ⁻¹' (u ∩ v))).2 ⟨u ∩ v, IsOpen.inter hu1 hv1,
          QuasiSeparatedSpace.inter_isCompact u v hu1 hu2 hv1 hv2, rfl⟩).2

end Topology.IsEmbedding
