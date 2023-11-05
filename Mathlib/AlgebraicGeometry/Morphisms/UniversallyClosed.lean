/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
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

theorem universallyClosed_eq : @UniversallyClosed = universally (topologically @IsClosedMap) := by
  ext X Y f; rw [UniversallyClosed_iff]

theorem universallyClosed_respectsIso : RespectsIso @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)

theorem universallyClosed_stableUnderBaseChange : StableUnderBaseChange @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_stableUnderBaseChange (topologically @IsClosedMap)

theorem universallyClosed_stableUnderComposition : StableUnderComposition @UniversallyClosed := by
  rw [universallyClosed_eq]
  exact StableUnderComposition.universally (fun X Y Z f g hf hg =>
    @IsClosedMap.comp _ _ _ _ _ _ g.1.base f.1.base hg hf)

instance universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g) :=
  universallyClosed_stableUnderComposition f g hf hg

instance universallyClosedFst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst : pullback f g ⟶ _) :=
  universallyClosed_stableUnderBaseChange.fst f g hg

instance universallyClosedSnd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd : pullback f g ⟶ _) :=
  universallyClosed_stableUnderBaseChange.snd f g hf

theorem morphismRestrict_base {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    ⇑(f ∣_ U).1.base = U.1.restrictPreimage f.1.1 :=
  funext fun x => Subtype.ext <| morphismRestrict_base_coe f U x

theorem universallyClosed_is_local_at_target : PropertyIsLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universallyIsLocalAtTargetOfMorphismRestrict
  · exact StableUnderComposition.respectsIso (fun X Y Z f g hf hg =>
        @IsClosedMap.comp _ _ _ _ _ _ g.1.base f.1.base hg hf)
      (fun f => (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso f)).isClosedMap)
  · intro X Y f ι U hU H
    simp_rw [topologically, morphismRestrict_base] at H
    exact (isClosedMap_iff_isClosedMap_of_iSup_eq_top hU).mpr H

theorem UniversallyClosed.openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} Y) :
    UniversallyClosed f ↔ ∀ i, UniversallyClosed (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  universallyClosed_is_local_at_target.openCover_iff f 𝒰

end AlgebraicGeometry
