/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.LocalAtTarget

#align_import algebraic_geometry.morphisms.universally_closed from "leanprover-community/mathlib"@"a8ae1b3f7979249a0af6bc7cf20c1f6bf656ca73"

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

open AlgebraicGeometry.MorphismProperty (topologically)

/-- A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
class UniversallyClosed (f : X ⟶ Y) : Prop where
  out : universally (topologically @IsClosedMap) f
#align algebraic_geometry.universally_closed AlgebraicGeometry.UniversallyClosed

theorem universallyClosed_eq : @UniversallyClosed = universally (topologically @IsClosedMap) := by
  ext X Y f; rw [universallyClosed_iff]
#align algebraic_geometry.universally_closed_eq AlgebraicGeometry.universallyClosed_eq

theorem universallyClosed_respectsIso : RespectsIso @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)
#align algebraic_geometry.universally_closed_respects_iso AlgebraicGeometry.universallyClosed_respectsIso

theorem universallyClosed_stableUnderBaseChange : StableUnderBaseChange @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_stableUnderBaseChange (topologically @IsClosedMap)
#align algebraic_geometry.universally_closed_stable_under_base_change AlgebraicGeometry.universallyClosed_stableUnderBaseChange

instance isClosedMap_isStableUnderComposition :
    IsStableUnderComposition (topologically @IsClosedMap) where
  comp_mem f g hf hg := IsClosedMap.comp (f := f.1.base) (g := g.1.base) hg hf

instance universallyClosed_isStableUnderComposition :
    IsStableUnderComposition @UniversallyClosed := by
  rw [universallyClosed_eq]
  infer_instance
#align algebraic_geometry.universally_closed_stable_under_composition AlgebraicGeometry.universallyClosed_isStableUnderComposition

instance universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g) :=
  comp_mem _ _ _ hf hg
#align algebraic_geometry.universally_closed_type_comp AlgebraicGeometry.universallyClosedTypeComp

theorem topologically_isClosedMap_respectsIso : RespectsIso (topologically @IsClosedMap) := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f hf
  have : IsIso f := hf
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso f))).isClosedMap

instance universallyClosedFst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst : pullback f g ⟶ _) :=
  universallyClosed_stableUnderBaseChange.fst f g hg
#align algebraic_geometry.universally_closed_fst AlgebraicGeometry.universallyClosedFst

instance universallyClosedSnd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd : pullback f g ⟶ _) :=
  universallyClosed_stableUnderBaseChange.snd f g hf
#align algebraic_geometry.universally_closed_snd AlgebraicGeometry.universallyClosedSnd

theorem universallyClosed_isLocalAtTarget : PropertyIsLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universally_isLocalAtTarget_of_morphismRestrict
  · exact topologically_isClosedMap_respectsIso
  · intro X Y f ι U hU H
    simp_rw [topologically, morphismRestrict_val_base] at H
    exact (isClosedMap_iff_isClosedMap_of_iSup_eq_top hU).mpr H
#align algebraic_geometry.universally_closed_is_local_at_target AlgebraicGeometry.universallyClosed_isLocalAtTarget

theorem UniversallyClosed.openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} Y) :
    UniversallyClosed f ↔ ∀ i, UniversallyClosed (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  universallyClosed_isLocalAtTarget.openCover_iff f 𝒰
#align algebraic_geometry.universally_closed.open_cover_iff AlgebraicGeometry.UniversallyClosed.openCover_iff

end AlgebraicGeometry

theorem PrimeSpectrum.isClosed_range_of_stableUnderSpecialization
    {R S} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : StableUnderSpecialization (Set.range (comap f))) :
    IsClosed (Set.range <| comap f) := by
  refine (isClosed_iff_zeroLocus _).mpr ⟨RingHom.ker f, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact Ideal.comap_mono (f := f) bot_le
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) hp
    obtain ⟨q, hq', rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f (I := ⊥) q hq
    exact hf ((le_iff_specializes _ _).mp hqp) ⟨⟨q, hq'.1.1⟩, rfl⟩

theorem AlgebraicGeometry.isClosed_map_of_specializingMap {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [CompactSpace X] (hf : SpecializingMap f.1.base) : IsClosedMap f.1.base := by
  intro Z hZ
  have := hZ.stableUnderSpecialization.image hf


theorem AlgebraicGeometry.compactSpace_iff_exists_surjective (X : Scheme.{u}) :
    CompactSpace X ↔ ∃ (R : CommRingCat) (f : Spec R ⟶ X), Function.Surjective f.1.base := by
  constructor
  · intro H
    let R : X.affineCover.finiteSubcover.J → CommRingCat := fun i ↦ X.affineOpenCover.obj i.1
    have := CommRingCat.piFanIsLimit R
    have :=
    have := isColimitOfPreserves Scheme.Spec (CommRingCat.piFanIsLimit R).op


theorem AlgebraicGeometry.foobar {X : Scheme.{u}} [CompactSpace X] (Z : Scheme) : IsClosedMap f.1.base := by
  intro Z hZ
  have := hZ.stableUnderSpecialization.image hf

theorem AlgebraicGeometry.isClosed_map_of_specializingMap {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [CompactSpace X] (hf : SpecializingMap f.1.base) : IsClosedMap f.1.base := by
  intro Z hZ
  have := hZ.stableUnderSpecialization.image hf
