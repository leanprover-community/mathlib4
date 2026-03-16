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

For a surjective and flat morphism `π : X ⟶ Y` between affine schemes, we prove the following.
* `exists_comp_eq_of_flat_of_isAffine`: Any morphism `f : X ⟶ S` of schemes whose two pullbacks to
  `X ×[Y] X` agree descends to a morphism `u : Y ⟶ S` with `π ≫ u = f`.
* `isRegularEpi_of_flat_of_surjective_of_isAffine`: The map `π : X ⟶ Y` is a regular epimorphism
  in the category of schemes. This implies `EffectiveEpi π` by `inferInstance`.

## Reference

* https://stacks.math.columbia.edu/tag/023Q

-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Scheme

/-- The underlying continuous map of a flat, surjective and quasi-compact morphism of schemes is an
effective epimorphism in the category of topological spaces. -/
instance effectiveEpi_base_of_flat {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
    [QuasiCompact f] : EffectiveEpi f.base := by
  rw [TopCat.effectiveEpi_iff_isQuotientMap]
  exact Flat.isQuotientMap_of_surjective _

namespace EffectiveEpiConstruction

/-- If `π : X ⟶ Y` is a surjective and flat morphism between affine schemes, then any morphism
`f : X ⟶ S` to an affine scheme `S` whose two pullbacks to `X ×[Y] X` agree descends to a morphism
`u : Y ⟶ S` with `π ≫ u = f`. -/
private lemma of_isAffine_target {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hf : pullback.fst π π ≫ f = pullback.snd π π ≫ f)
    [IsAffine S] :
    ∃ u : Y ⟶ S, π ≫ u = f := by
  have : EffectiveEpi (AffineScheme.ofHom π) := by
    apply AffineScheme.equivCommRingCat.functor.effectiveEpi_of_map
    apply CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp ⟨‹_›, ‹_›⟩
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair
    (AffineScheme.ofHom π)
    (IsPullback.of_map (f := AffineScheme.ofHom (pullback.fst π π)) (AffineScheme.forgetToScheme)
      (InducedCategory.Hom.ext pullback.condition) (.of_hasPullback _ _))
    (AffineScheme.ofHom f) (InducedCategory.Hom.ext hf)
  use u.hom, InducedCategory.Hom.ext_iff.mp hu

set_option backward.isDefEq.respectTransparency false in
open pullback in
/-- If `π : X ⟶ Y` is surjective and flat between affine schemes, then any morphism `f : X ⟶ S` of
schemes whose two pullbacks to `X ×[Y] X` agree descends Zariski locally on `Y`: there exists an
open cover `𝒰` of `Y` such that for each `i` there is `u : 𝒰.X i ⟶ S` with
`pullback.fst π (𝒰.f i) ≫ f = pullback.snd π (𝒰.f i) ≫ u`. -/
private lemma exists_openCover_exists {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hf : pullback.fst π π ≫ f = pullback.snd π π ≫ f) :
    ∃ (𝒰 : OpenCover.{u} Y),
      ∀ i : 𝒰.I₀, ∃ (u : 𝒰.X i ⟶ S), pullback.fst π (𝒰.f i) ≫ f = pullback.snd _ _ ≫ u := by
  obtain ⟨b, hfac⟩ : ∃ (u : Y.carrier ⟶ S.carrier), π.base ≫ u = f.base := by
    apply IsRegularEpi.exists_of_isKernelPair _ (IsPullback.of_hasPullback _ _)
    have := congr(Scheme.forgetToTop.map $hf)
    rwa [Functor.map_comp, Functor.map_comp, ← pullbackComparison_comp_fst_assoc,
      ← pullbackComparison_comp_snd_assoc, cancel_epi] at this
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
    exact trans (by simp [𝒰]) i.2.2
  have h1 : fst (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ fst π π := by simp
  have h2 : snd (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ snd π π := by simp
  obtain ⟨u, hu⟩ := of_isAffine_target (pullback.snd π (𝒰.f i)) f' <| by
    simp only [← cancel_mono (Scheme.Opens.ι i.1.2.1),
      Category.assoc, IsOpenImmersion.lift_fac, f', reassoc_of% h1, reassoc_of% h2, hf]
  refine ⟨u ≫ Scheme.Opens.ι _, ?_⟩
  simp [reassoc_of% hu, f']

end EffectiveEpiConstruction

set_option backward.isDefEq.respectTransparency false in
/-- If `π : X ⟶ Y` is a flat and surjective morphism between affine schemes, then `π` is a
regular epimorphism in the category of schemes. -/
@[stacks 023Q]
lemma isRegularEpi_of_flat_of_surjective_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y) [Surjective π] [Flat π] :
    IsRegularEpi π := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  refine .of_epi_of_exists fun Z f hf ↦ ?_
  obtain ⟨𝒰, h⟩ := EffectiveEpiConstruction.exists_openCover_exists π f hf
  choose u hfac using h
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    have : Epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)) :=
      Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)),
      ← cancel_epi (pullback.congrHom rfl pullback.condition.symm).hom]
    conv_rhs =>
      simp only [pullback.congrHom_hom, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right,
      PullbackCone.mk_π_app, Category.comp_id]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc,
      ← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc, ← pullback.condition_assoc,
      ← hfac i, ← pullback.condition_assoc, ← hfac j]
    simp
  · apply Cover.hom_ext (𝒰.pullback₁ π)
    intro i
    simp [pullback.condition_assoc, hfac]

end Scheme

end AlgebraicGeometry
