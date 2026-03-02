/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.Algebra.Category.Ring.EqualizerPushout
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Category.TopCat.EffectiveEpi
public import Mathlib.CategoryTheory.EffectiveEpi.Preserves

/-!
# Effective epimorphisms in the category of schemes

We collect results about effective epimorphisms in the category of schemes.

## Main results

* `AffineScheme.effectiveEpi_of_flat_of_surjective`: A flat surjective morphism between affine
schemes is an effective epimorphism in the category of affine schemes.

For a surjective and flat morphism `π : X ⟶ Y` between affine schemes, we prove the following.
* `exists_of_flat`: Any morphism `g : X ⟶ S` of schemes whose two pullbacks to `X ×[Y] X` agree
  descends to a morphism `f : Y ⟶ S` with `π ≫ f = g`.
* `effectiveEpi_Spec_of_flat_of_surjective`: The map `π : X ⟶ Y` is an effective epimorphism in the
  category of schemes.

## Reference

* https://stacks.math.columbia.edu/tag/023Q

-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section AffineScheme

/-- A flat surjective morphism is an effective epimorphism in the category of affine schemes. -/
lemma AffineScheme.effectiveEpi_of_flat_of_surjective {X Y : AffineScheme.{u}} (f : X ⟶ Y)
    [Flat f.hom] [Surjective f.hom] :
    EffectiveEpi f := by
  apply AffineScheme.equivCommRingCat.functor.effectiveEpi_of_map
  apply CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f.hom).mp ⟨‹_›, ‹_›⟩

end AffineScheme

section Scheme

/-- If `π : X ⟶ Y` is a surjective morphism of schemes, then any morphism `f : X ⟶ S` of schemes
whose two pullbacks to `X ×[Y] X` agree descends to a function `u : ↥Y → ↥S` (as types) with
`u ∘ ⇑π.base.hom = ⇑f.base.hom`. See `exists_of_flat` for the scheme morphism version. -/
lemma exists_base_hom_of_surjective {X Y S : Scheme.{u}} {π : X ⟶ Y} [Surjective π]
    {f : X ⟶ S} (h : pullback.fst π π ≫ f = pullback.snd π π ≫ f) :
    ∃ (u : ↥Y → ↥S), u ∘ ⇑π.base.hom = ⇑f.base.hom := by
  let : RegularEpi (Scheme.forget.map π) := by
    have := (isSplitEpi_iff_surjective (Scheme.forget.map π)).mpr ‹Surjective π›.surj
    exact regularEpiOfEffectiveEpi (Scheme.forget.map π)
  refine ⟨_, types_comp _ _ ▸ Cofork.IsColimit.π_desc' this.isColimit _ ?_⟩
  change pullback.fst _ _ ≫ Scheme.forget.map f = pullback.snd _ _ ≫ Scheme.forget.map f
  apply ((epi_iff_surjective _).mpr
    (Scheme.pullbackComparison_forget_surjective _ _)).left_cancellation
  simp only [← Category.assoc, pullbackComparison_comp_fst, ← Functor.map_comp, h,
    pullbackComparison_comp_snd]

/-- If `π : X ⟶ Y` is a flat, surjective and quasi-compact morphism of schemes, then any morphism
`f : X ⟶ S` of schemes whose two pullbacks to `X ×[Y] X` agree descends to a continuous map
`u : Y.carrier ⟶ S.carrier` with `π.base ≫ u = f.base`. See `exists_of_flat` for the scheme
morphism version. -/
lemma exists_base_of_surjective {X Y S : Scheme.{u}} {π : X ⟶ Y}
    [Flat π] [Surjective π] [QuasiCompact π]
    {f : X ⟶ S} (h : pullback.fst π π ≫ f = pullback.snd π π ≫ f) :
    ∃ (u : Y.carrier ⟶ S.carrier), π.base ≫ u = f.base := by
  have h' {Z : TopCat} (g₁ g₂ : Z ⟶ X.carrier) (hg : g₁ ≫ π.base = g₂ ≫ π.base) :
      g₁ ≫ f.base = g₂ ≫ f.base := by
    apply TopCat.hom_ext
    apply ContinuousMap.coe_injective
    simp only [TopCat.hom_comp, ContinuousMap.coe_comp]
    rw [(exists_base_hom_of_surjective h).choose_spec.symm, Function.comp_assoc]
    congr 1
    exact congrArg ContinuousMap.toFun ((TopCat.hom_comp _ _).trans (congrArg TopCat.Hom.hom hg))
  exact ⟨(TopCat.effectiveEpiStructOfQuotientMap _ (Flat.isQuotientMap_of_surjective π)).desc _ h',
    (TopCat.effectiveEpiStructOfQuotientMap _ (Flat.isQuotientMap_of_surjective π)).fac _ h'⟩

/-- If `π : X ⟶ Y` is a surjective and flat morphism between affine schemes, then any morphism
`f : X ⟶ S` to an affine scheme `S` whose two pullbacks to `X ×[Y] X` agree descends to a morphism
`u : Y ⟶ S` with `π ≫ u = f`. See `exists_of_flat` for the general form with an arbitrary target. -/
lemma of_isAffine_target {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hg : pullback.fst π π ≫ f = pullback.snd π π ≫ f)
    [IsAffine S] :
    ∃ u : Y ⟶ S, π ≫ u = f := by
  have : EffectiveEpi (AffineScheme.ofHom π) :=
    @AffineScheme.effectiveEpi_of_flat_of_surjective _ _ _ (by simpa) (by simpa)
  let u : AffineScheme.of Y ⟶ AffineScheme.of S := by
    apply EffectiveEpi.desc (AffineScheme.ofHom π) (AffineScheme.ofHom f)
    intro _ g₁ g₂ hg₁₂
    apply InducedCategory.hom_ext
    have hg₁₂' : g₁.hom ≫ π = g₂.hom ≫ π := by
      simpa using congrArg InducedCategory.Hom.hom hg₁₂
    simpa using congrArg (fun k => pullback.lift _ _ hg₁₂' ≫ k) hg
  have : (AffineScheme.ofHom π ≫ u).hom = (AffineScheme.ofHom f).hom := by simp [u]
  exact ⟨u.hom, by simpa⟩

open pullback in
/-- If `π : X ⟶ Y` is surjective and flat between affine schemes, then any morphism `f : X ⟶ S` of
schemes whose two pullbacks to `X ×[Y] X` agree descends Zariski locally on `Y`: there exists an
open cover `𝒰` of `Y` such that for each `i` there is `u : 𝒰.X i ⟶ S` with
`pullback.fst π (𝒰.f i) ≫ f = pullback.snd π (𝒰.f i) ≫ u`. -/
lemma exists_openCover_exists {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hg : pullback.fst π π ≫ f = pullback.snd π π ≫ f) :
    ∃ (𝒰 : OpenCover.{u} Y),
      ∀ i : 𝒰.I₀, ∃ (u : 𝒰.X i ⟶ S), pullback.fst π (𝒰.f i) ≫ f = pullback.snd _ _ ≫ u := by
  obtain ⟨b, hfac⟩ := exists_base_of_surjective hg
  let 𝒰 := Y.openCoverOfIsOpenCover _ <| Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap b.hom)
  refine ⟨𝒰, fun i ↦ ?_⟩
  have : IsAffine (𝒰.X i) := i.2.1
  let f' : pullback π (𝒰.f i) ⟶ i.1.2.1 := by
    apply IsOpenImmersion.lift (Scheme.Opens.ι i.1.2.1) (pullback.fst _ _ ≫ f)
    dsimp
    rw [← hfac, ← TopCat.coe_comp, ← Scheme.Hom.comp_base_assoc, pullback.condition]
    simp only [Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp,
      range_eq_univ, Set.image_univ, Opens.range_ι, Set.image_subset_iff]
    exact le_trans (by simp [𝒰]) i.2.2
  have h1 : fst (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ fst π π := by simp
  have h2 : snd (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ snd π π := by simp
  obtain ⟨u, hu⟩ := of_isAffine_target (pullback.snd π (𝒰.f i)) f' <| by
    simp only [← cancel_mono (Scheme.Opens.ι i.1.2.1),
      Category.assoc, IsOpenImmersion.lift_fac, f', reassoc_of% h1, reassoc_of% h2, hg]
  refine ⟨u ≫ Scheme.Opens.ι _, ?_⟩
  simp [reassoc_of% hu, f']

/-- If `π : X ⟶ Y` is a surjective and flat morphism between affine schemes, then any morphism
`g : X ⟶ S` of schemes whose two pullbacks to `X ×[Y] X` agree descends to a morphism `f : Y ⟶ S`
with `π ≫ f = g`. -/
lemma exists_of_flat {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π] (g : X ⟶ S) (hg : pullback.fst π π ≫ g = pullback.snd π π ≫ g) :
    ∃ (f : Y ⟶ S), π ≫ f = g := by
  obtain ⟨𝒰, h⟩ := exists_openCover_exists π g hg
  choose u hfac using h
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    have : Epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)) :=
      Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)),
      ← cancel_epi (pullback.congrHom rfl pullback.condition.symm).hom]
    conv_rhs => simp only [pullback.congrHom_hom, limit.lift_π_assoc, PullbackCone.mk_pt,
      cospan_right, PullbackCone.mk_π_app, Category.comp_id]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc,
      ← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc, ← pullback.condition_assoc,
      ← hfac i, ← pullback.condition_assoc, ← hfac j]
    simp
  · apply Cover.hom_ext (𝒰.pullback₁ π)
    intro i
    simp [pullback.condition_assoc, hfac]

/-- If `π : X ⟶ Y` is a flat and surjective morphism between affine schemes, the cofork formed by
the two projections `X ×[Y] X ⟶ X` followed by `X ⟶ Y` is a colimit. -/
noncomputable def isColimitCoforkSpecPullbackOfFlatOfSurjective
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y) [Surjective π] [Flat π] :
    IsColimit (Cofork.ofπ π pullback.condition) := by
  apply Cofork.IsColimit.mk'
  intro s
  refine ⟨(exists_of_flat _ _ s.condition).choose,
    ⟨by simp [(exists_of_flat _ _ s.condition).choose_spec], ?_⟩⟩
  intro _ h
  haveI : Epi π := Flat.epi_of_flat_of_surjective π
  apply (cancel_epi π).mp
  trans s.ι.app WalkingParallelPair.one
  · simpa using h
  · simpa using (exists_of_flat _ _ s.condition).choose_spec.symm

/-- If `π : X ⟶ Y` is a flat and surjective morphism between affine schemes, then `π` is an
effective epimorphism in the category of schemes. -/
@[stacks 023Q]
lemma effectiveEpi_Spec_of_flat_of_surjective
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y) [Surjective π] [Flat π] :
    EffectiveEpi π :=
  effectiveEpi_of_kernelPair _ (isColimitCoforkSpecPullbackOfFlatOfSurjective π)

end Scheme

end AlgebraicGeometry
