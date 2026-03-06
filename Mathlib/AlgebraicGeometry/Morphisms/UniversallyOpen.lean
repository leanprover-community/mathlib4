/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Universally open morphism

A morphism of schemes `f : X ⟶ Y` is universally open if `X ×[Y] Y' ⟶ Y'` is an open map
for all base change `Y' ⟶ Y`.

We show that being universally open is local at the target, and is stable under compositions and
base changes.

-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally open if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) an open map.
-/
@[mk_iff]
class UniversallyOpen (f : X ⟶ Y) : Prop where
  universally_isOpenMap : universally (topologically @IsOpenMap) f

@[deprecated (since := "2026-01-20")]
alias UniversallyOpen.out := UniversallyOpen.universally_isOpenMap

lemma Scheme.Hom.isOpenMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyOpen f] :
    IsOpenMap f := UniversallyOpen.universally_isOpenMap _ _ _ IsPullback.of_id_snd

namespace UniversallyOpen

theorem eq : @UniversallyOpen = universally (topologically @IsOpenMap) := by
  ext X Y f; rw [universallyOpen_iff]

instance (priority := 900) [IsOpenImmersion f] : UniversallyOpen f := by
  rw [eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsOpenImmersion f' := MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isOpenEmbedding.isOpenMap

instance : RespectsIso @UniversallyOpen :=
  eq.symm ▸ inferInstance

instance : IsStableUnderBaseChange @UniversallyOpen :=
  eq.symm ▸ inferInstance

instance : IsStableUnderComposition (topologically @IsOpenMap) where
  comp_mem f g hf hg := IsOpenMap.comp (f := f) (g := g) hg hf

instance : IsStableUnderComposition @UniversallyOpen := by
  rw [eq]
  infer_instance

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyOpen f] [hg : UniversallyOpen g] : UniversallyOpen (f ≫ g) :=
  comp_mem _ _ _ hf hg

instance : MorphismProperty.IsMultiplicative @UniversallyOpen where
  id_mem _ := inferInstance

instance fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g] :
    UniversallyOpen (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

instance snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f] :
    UniversallyOpen (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

instance : IsZariskiLocalAtTarget @UniversallyOpen := by
  rw [eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isOpenMap_iff_restrictPreimage.mpr H

instance : IsZariskiLocalAtSource @UniversallyOpen := by
  rw [eq]
  exact universally_isZariskiLocalAtSource _

end UniversallyOpen

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- A generalizing morphism, locally of finite presentation is open. -/
@[stacks 01U1]
lemma isOpenMap_of_generalizingMap [LocallyOfFinitePresentation f]
    (hf : GeneralizingMap f) : IsOpenMap f := by
  change topologically IsOpenMap f
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically IsOpenMap) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback (P := topologically GeneralizingMap)
      (iY := Y.affineCover.f i) (IsPullback.of_hasPullback ..) hf
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := topologically IsOpenMap) X.affineCover]
    intro i
    refine this f _ _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtSource.comp (P := topologically GeneralizingMap) hf _
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  convert PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  · rwa [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  · apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance

/-- Any flat morphism is generalizing. -/
lemma Flat.generalizingMap [Flat f] : GeneralizingMap f := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp
  convert Algebra.HasGoingDown.of_flat
  exact HasRingHomProperty.appLE @Flat f ‹_› U V e

/-- A flat morphism, locally of finite presentation is universally open. -/
@[stacks 01UA]
instance (priority := low) UniversallyOpen.of_flat [Flat f] [LocallyOfFinitePresentation f] :
    UniversallyOpen f :=
  ⟨universally_mk' _ _ fun _ _ ↦ isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)⟩

set_option backward.isDefEq.respectTransparency false in
nonrec instance (priority := low) [IsIntegral Y] [Subsingleton Y] :
    UniversallyOpen f := by
  wlog hX : ∃ S, X = Spec S generalizing X
  · refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦ this _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  wlog hY : ∃ K, Y = Spec K ∧ IsField K generalizing Y
  · have inst : Subsingleton (Spec Γ(Y, ⊤)) := Y.isoSpec.inv.homeomorph.subsingleton
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ Y.isoSpec.hom).mp
      (this _ ⟨_, rfl, isField_of_isIntegral_of_subsingleton _⟩)
  obtain ⟨K, rfl, hK⟩ := hY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ⟨universally_mk' _ _ fun {T} g _ ↦ ?_⟩
  wlog hT : ∃ R, T = Spec R generalizing T
  · refine (IsZariskiLocalAtTarget.iff_of_openCover T.affineCover).mpr fun i ↦ ?_
    refine (MorphismProperty.cancel_left_of_respectsIso _
      ((pullbackRightPullbackFstIso ..).inv ≫ (pullbackSymmetry ..).hom) _).mp ?_
    simpa [Scheme.Cover.pullbackHom] using this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hT
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  refine (MorphismProperty.cancel_left_of_respectsIso _ (pullbackSpecIso K R S).inv _).mp ?_
  convert_to topologically _ (Spec.map <| CommRingCat.ofHom (algebraMap R (TensorProduct K R S)))
  · exact pullbackSpecIso_inv_fst ..
  let := hK.toField
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

end AlgebraicGeometry
