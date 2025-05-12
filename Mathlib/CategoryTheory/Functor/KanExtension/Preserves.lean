/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of Kan extensions

Given functors `F : A ⥤ B`, `L : B ⥤ C`, and `G : B ⥤ D`,
we introduce a typeclass `G.PreservesLeftKanExtension F L`, which encodes the fact that
the left Kan extension of `F` along `L` is preserved by the functor `G`.

When the Kan extension is pointwise, It suffices that `G` preserves colimits of the relevant
diagrams.

TODO: better namespaces

-/

namespace CategoryTheory.Functor

variable {A B C D: Type*} [Category A] [Category B] [Category C] [Category D]
  (G : B ⥤ D) (F : A ⥤ B) (L : A ⥤ C)

section LeftKanExtension

/-- TODO -/
class PreservesLeftKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α],
    IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom

attribute [instance] PreservesLeftKanExtension.preserves

/-- TODO -/
class PreservesPointwiseLeftKanExtensionAt (c : C) where
  preserves : ∀ (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c →
    (LeftExtension.whiskerRight L F G|>.obj E).IsPointwiseLeftKanExtensionAt c

/-- TODO -/
abbrev PreservesPointwiseLeftKanExtension := ∀ c : C, PreservesPointwiseLeftKanExtensionAt G F L c

/-- Given a pointwise left kan extension of `F` at `L`, exhibits
`(LeftExtension.whiskerRight L F G).obj E` as a pointwise left Kan extension of `F ⋙ G` at `L`. -/
def PreservesPointwiseLeftKanExtension.preserves [h : PreservesPointwiseLeftKanExtension G F L]
    (E : LeftExtension L F) (hE : E.IsPointwiseLeftKanExtension) :
    LeftExtension.whiskerRight L F G|>.obj E|>.IsPointwiseLeftKanExtension := fun c ↦
  (h c).preserves E (hE c)

/-- The cocone at a point of the whiskering right by `G`of an extension is isomorphic to the
action of `G` on the cocone at that point for the original extension. -/
@[simps!]
def coconeAtWhiskerRightIso (E : LeftExtension L F) (c : C) :
    ((LeftExtension.whiskerRight L F G).obj E).coconeAt c ≅ G.mapCocone (E.coconeAt c) :=
  Limits.Cocones.ext (Iso.refl _)

instance hasLeftKanExtension_of_preserves [L.HasLeftKanExtension F]
    [PreservesLeftKanExtension G F L] : L.HasLeftKanExtension (F ⋙ G) :=
  @HasLeftKanExtension.mk _ _ _ _ _ _ _ _ _ _ <|
    letI : (L.leftKanExtension F).IsLeftKanExtension <| L.leftKanExtensionUnit F := by infer_instance
    PreservesLeftKanExtension.preserves (L.leftKanExtension F) (L.leftKanExtensionUnit F)

instance hasPointwiseLeftKanExtension_of_preserves [L.HasPointwiseLeftKanExtension F]
    [PreservesPointwiseLeftKanExtension G F L] : L.HasPointwiseLeftKanExtension (F ⋙ G) :=
  (PreservesPointwiseLeftKanExtension.preserves G F L _
    <| pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).hasPointwiseLeftKanExtension

/-- Extract an isomorphism `(leftKanExtension L F) ⋙ G ≅ leftKanExtension L (F ⋙ G)` when `G`
preserves left Kan extensions. -/
@[simps!]
noncomputable def leftKanExtensionCompIsoOfPreserves [PreservesLeftKanExtension G F L]
    [L.HasLeftKanExtension F] :
    L.leftKanExtension F ⋙ G ≅ L.leftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.leftKanExtension F ⋙ G)
    (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.leftKanExtension <| F ⋙ G)
    (L.leftKanExtensionUnit <| F ⋙ G)

/-- A functor that preserves the colimit of `(CostructuredArrow.proj L c ⋙ F)` preserves
the pointwise left kan extension of `F` along `L` at c. -/
noncomputable instance preservesPointwiseLeftKanExtensionAtOfPreservesColimit (c : C)
    [Limits.PreservesColimit (CostructuredArrow.proj L c ⋙ F) G] :
    G.PreservesPointwiseLeftKanExtensionAt F L c where
  preserves E p :=
    Limits.IsColimit.ofIsoColimit
      (Limits.PreservesColimit.preserves p).some
      (coconeAtWhiskerRightIso G _ _ E c).symm

/-- If there is a pointwise left Kan extension of `F` along `L`, and if `G` preserves them,
then `G` preserves left Kan extensions of `F` along `L`. -/
noncomputable instance preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseLeftKanExtension L F] [G.PreservesPointwiseLeftKanExtension F L] :
    G.PreservesLeftKanExtension F L where
  preserves F' α _ :=
    (LeftExtension.isPointwiseLeftKanExtensionEquivOfIso (LeftExtension.whiskerRightIsoMk G α) <|
      PreservesPointwiseLeftKanExtension.preserves G F L _ <|
        isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α).isLeftKanExtension

/-- Extract an isomorphism
`(pointwiseLeftKanExtension L F) ⋙ G ≅ pointwiseLeftKanExtension L (F ⋙ G)` when `G` preserves
left Kan extensions. -/
@[simps!]
noncomputable def pointwiseLeftKanExtensionCompIsoOfPreserves [PreservesPointwiseLeftKanExtension G F L]
    [L.HasPointwiseLeftKanExtension F] :
    L.pointwiseLeftKanExtension F ⋙ G ≅ L.pointwiseLeftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.pointwiseLeftKanExtension F ⋙ G)
    (whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.pointwiseLeftKanExtension <| F ⋙ G)
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

/-- `G.PreservesLeftKanExtensions L` means that `G : B ⥤ D` preserves all left Kan extensions along
`L : A ⥤ C` of every functor `A ⥤ B`. -/
abbrev preservesLeftKanExtensions := ∀ (F : A ⥤ B), G.PreservesLeftKanExtension F L

/-- `G.PreservesPointwiseLeftKanExtensions L` means that `G : B ⥤ D` preserves all pointwise left Kan
extensions along `L : A ⥤ C` of every functor `A ⥤ B`. -/
abbrev preservesPointwiseLeftKanExtensions := ∀ (F : A ⥤ B), G.PreservesPointwiseLeftKanExtension F L

end LeftKanExtension

section RightKanExtension

/-- TODO -/
class PreservesRightKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α],
    IsRightKanExtension (F' ⋙ G) <| (Functor.associator _ _ _).inv ≫ whiskerRight α G

attribute [instance] PreservesRightKanExtension.preserves

/-- TODO -/
class PreservesPointwiseRightKanExtensionAt (c : C) where
  preserves : ∀ (E : RightExtension L F), E.IsPointwiseRightKanExtensionAt c →
    (RightExtension.whiskerRight L F G|>.obj E).IsPointwiseRightKanExtensionAt c

/-- TODO -/
abbrev PreservesPointwiseRightKanExtension := ∀ c : C, PreservesPointwiseRightKanExtensionAt G F L c

/-- Given a pointwise left kan extension of `F` at `L`, exhibits
`(RightExtension.whiskerRight L F G).obj E` as a pointwise left Kan extension of `F ⋙ G` at `L`. -/
def PreservesPointwiseRightKanExtension.preserves [h : PreservesPointwiseRightKanExtension G F L]
    (E : RightExtension L F) (hE : E.IsPointwiseRightKanExtension) :
    RightExtension.whiskerRight L F G|>.obj E|>.IsPointwiseRightKanExtension := fun c ↦
  (h c).preserves E (hE c)

/-- The cocone at a point of the whiskering right by `G`of an extension is isomorphic to the
action of `G` on the cocone at that point for the original extension. -/
@[simps!]
def coneAtWhiskerRightIso (E : RightExtension L F) (c : C) :
    (RightExtension.whiskerRight L F G|>.obj E).coneAt c ≅ G.mapCone (E.coneAt c) :=
  Limits.Cones.ext (Iso.refl _)

instance hasRightKanExtension_of_preserves [L.HasRightKanExtension F]
    [PreservesRightKanExtension G F L] : L.HasRightKanExtension (F ⋙ G) :=
  @HasRightKanExtension.mk _ _ _ _ _ _ _ _ _ _ <|
    letI : (L.rightKanExtension F).IsRightKanExtension <| L.rightKanExtensionCounit F := by infer_instance
    PreservesRightKanExtension.preserves (L.rightKanExtension F) (L.rightKanExtensionCounit F)

instance hasPointwiseRightKanExtension_of_preserves [L.HasPointwiseRightKanExtension F]
    [PreservesPointwiseRightKanExtension G F L] : L.HasPointwiseRightKanExtension (F ⋙ G) :=
  (PreservesPointwiseRightKanExtension.preserves G F L _
    <| pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).hasPointwiseRightKanExtension

/-- Extract an isomorphism `(rightKanExtension L F) ⋙ G ≅ rightKanExtension L (F ⋙ G)` when `G`
preserves left Kan extensions. -/
@[simps!]
noncomputable def rightKanExtensionCompIsoOfPreserves [PreservesRightKanExtension G F L]
    [L.HasRightKanExtension F] :
    L.rightKanExtension F ⋙ G ≅ L.rightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.rightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G)
    (L.rightKanExtension <| F ⋙ G)
    (L.rightKanExtensionCounit <| F ⋙ G)

/-- A functor that preserves the colimit of `(CostructuredArrow.proj L c ⋙ F)` preserves
the pointwise left kan extension of `F` along `L` at c. -/
noncomputable instance preservesPointwiseRightKanExtensionAtOfPreservesColimit (c : C)
    [Limits.PreservesLimit (StructuredArrow.proj c L ⋙ F) G] :
    G.PreservesPointwiseRightKanExtensionAt F L c where
  preserves E p :=
    Limits.IsLimit.ofIsoLimit
      (Limits.PreservesLimit.preserves p).some
      (coneAtWhiskerRightIso G _ _ E c).symm

/-- If there is a pointwise left Kan extension of `F` along `L`, and if `G` preserves them,
then `G` preserves left Kan extensions of `F` along `L`. -/
noncomputable instance preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseRightKanExtension L F] [G.PreservesPointwiseRightKanExtension F L] :
    G.PreservesRightKanExtension F L where
  preserves F' α _ :=
    (RightExtension.isPointwiseRightKanExtensionEquivOfIso (RightExtension.whiskerRightIsoMk G α) <|
      PreservesPointwiseRightKanExtension.preserves G F L _ <|
        isPointwiseRightKanExtensionOfIsRightKanExtension F' α).isRightKanExtension

/-- Extract an isomorphism
`(pointwiseRightKanExtension L F) ⋙ G ≅ pointwiseRightKanExtension L (F ⋙ G)` when `G` preserves
left Kan extensions. -/
@[simps!]
noncomputable def pointwiseRightKanExtensionCompIsoOfPreserves [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F] :
    L.pointwiseRightKanExtension F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.pointwiseRightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G)
    (L.pointwiseRightKanExtension <| F ⋙ G)
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G)

end RightKanExtension

end CategoryTheory.Functor
