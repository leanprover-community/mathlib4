/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
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

instance topologically_isClosedMap_respectsIso : RespectsIso (topologically @IsClosedMap) := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f hf
  have : IsIso f := hf
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso f))).isClosedMap

instance universallyClosed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst f g) :=
  universallyClosed_stableUnderBaseChange.fst f g hg
#align algebraic_geometry.universally_closed_fst AlgebraicGeometry.universallyClosed_fst

instance universallyClosed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd f g) :=
  universallyClosed_stableUnderBaseChange.snd f g hf
#align algebraic_geometry.universally_closed_snd AlgebraicGeometry.universallyClosed_snd

instance universallyClosed_isLocalAtTarget : IsLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universally_isLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_val_base] at H
  exact (isClosedMap_iff_isClosedMap_of_iSup_eq_top hU).mpr H
#align algebraic_geometry.universally_closed_is_local_at_target AlgebraicGeometry.universallyClosed_isLocalAtTarget

end AlgebraicGeometry
