/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.
This implies that `f` is topologically proper (`AlgebraicGeometry.Scheme.Hom.isProperMap`).

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
class UniversallyClosed (f : X ⟶ Y) : Prop where
  universally_isClosedMap : universally (topologically @IsClosedMap) f

@[deprecated (since := "2026-01-20")]
alias UniversallyClosed.out := UniversallyClosed.universally_isClosedMap

lemma Scheme.Hom.isClosedMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f := UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd

theorem universallyClosed_eq : @UniversallyClosed = universally (topologically @IsClosedMap) := by
  ext X Y f; rw [universallyClosed_iff]

instance (priority := 900) [IsClosedImmersion f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsClosedImmersion f' :=
    MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isClosedEmbedding.isClosedMap

theorem universallyClosed_respectsIso : RespectsIso @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)

instance universallyClosed_isStableUnderBaseChange : IsStableUnderBaseChange @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsClosedMap)

instance isClosedMap_isStableUnderComposition :
    IsStableUnderComposition (topologically @IsClosedMap) where
  comp_mem f g hf hg := IsClosedMap.comp (f := f) (g := g) hg hf

instance universallyClosed_isStableUnderComposition :
    IsStableUnderComposition @UniversallyClosed := by
  rw [universallyClosed_eq]
  infer_instance

lemma UniversallyClosed.of_comp_surjective {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Surjective f] : UniversallyClosed g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have := UniversallyClosed.universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsClosedMap.of_comp_surjective (MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›).1
    (Scheme.Hom.continuous _) this

instance universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g) :=
  comp_mem _ _ _ hf hg

instance : MorphismProperty.IsMultiplicative @UniversallyClosed where
  id_mem _ := inferInstance

instance universallyClosed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

instance universallyClosed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

instance universallyClosed_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isClosedMap_iff_restrictPreimage.mpr H

instance (f : X ⟶ Y) (V : Y.Opens) [UniversallyClosed f] : UniversallyClosed (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

open Scheme.Pullback _root_.PrimeSpectrum MvPolynomial in
/-- If `X` is universally closed over a field, then `X` is quasi-compact. -/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let Z : Set (pullback f q :) := (⨆ i, fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i) : (pullback f q).Opens)ᶜ
  have hZ : IsClosed Z := by
    simp only [Z, isClosed_compl_iff, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    exact isOpen_iUnion fun i ↦ (fT.continuous.1 _ (Ti i).2).inter (p.continuous.1 _ (U i).2)
  let Zc : T.Opens := ⟨(fT '' Z)ᶜ, (fT.isClosedMap _ hZ).isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.I₀ K →ₐ[K] K := MvPolynomial.aeval (fun _ ↦ 1)
  let t : T := Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht (i : 𝒰.I₀) : t ∈ Ti i := show ψ (.X i) ≠ 0 by simp [ψ]
  have htZc : t ∈ Zc := by
    intro ⟨z, hz, hzt⟩
    suffices ∃ i, fT z ∈ Ti i ∧ p z ∈ U i from hz (by simpa)
    exact ⟨𝒰.idx (p z), hzt ▸ ht _, by simpa [U] using 𝒰.covers (p z)⟩
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ := Opens.isBasis_iff_nbhd.mp isBasis_basic_opens htZc
  let σ : Finset 𝒰.I₀ := MvPolynomial.vars g
  let φ : MvPolynomial 𝒰.I₀ K →+* MvPolynomial 𝒰.I₀ K :=
    (MvPolynomial.aeval fun i : 𝒰.I₀ ↦ if i ∈ σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := Spec.map (CommRingCat.ofHom φ) t
  have ht'g : t' ∈ PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htU'
  have h : t' ∉ fT '' Z := hU'le ht'g
  suffices ⋃ i ∈ σ, (U i).1 = Set.univ from
    ⟨this ▸ Finset.isCompact_biUnion _ fun i _ ↦ isCompact_range (𝒰.f i).continuous⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, rfl, hzr⟩ := exists_preimage_pullback x t' (Subsingleton.elim (f x) (q t'))
  suffices ∀ i, t ∈ (Ti i).comap ⟨_, continuous_comap φ⟩ → p z ∉ U i from
    ⟨z, by simpa [Z, p, fT, hzr], hzr⟩
  intro i hi₁ hi₂
  rw [comap_basicOpen, show φ (.X i) = 0 by simpa [φ] using (hx i · hi₂), basicOpen_zero] at hi₁
  cases hi₁

set_option backward.isDefEq.respectTransparency false in
@[stacks 04XU]
lemma Scheme.Hom.isProperMap (f : X ⟶ Y) [UniversallyClosed f] : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f.continuous, f.isClosedMap, fun y ↦ ?_⟩
  have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
  rw [← Scheme.range_fromSpecResidueField, ← Scheme.Pullback.range_fst]
  exact isCompact_range (Scheme.Hom.continuous _)

instance (priority := 900) [UniversallyClosed f] : QuasiCompact f where
  isCompact_preimage _ _ := f.isProperMap.isCompact_preimage

lemma universallyClosed_eq_universallySpecializing :
    @UniversallyClosed = (topologically @SpecializingMap).universally ⊓ @QuasiCompact := by
  rw [← universally_eq_iff (P := @QuasiCompact).mpr inferInstance, ← universally_inf]
  apply le_antisymm
  · rw [← universally_eq_iff (P := @UniversallyClosed).mpr inferInstance]
    exact universally_mono fun X Y f H ↦ ⟨f.isClosedMap.specializingMap, inferInstance⟩
  · rw [universallyClosed_eq]
    exact universally_mono fun X Y f ⟨h₁, h₂⟩ ↦ (isClosedMap_iff_specializingMap _).mpr h₁

instance (priority := low) Surjective.of_universallyClosed_of_isDominant
    [UniversallyClosed f] [IsDominant f] : Surjective f := by
  rw [surjective_iff, ← Set.range_eq_univ, ← f.denseRange.closure_range,
    f.isClosedMap.isClosed_range.closure_eq]

end AlgebraicGeometry
