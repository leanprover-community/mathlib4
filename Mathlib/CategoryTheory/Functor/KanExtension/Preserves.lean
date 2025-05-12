/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of Kan extensions

Given functors `F : A ⥤ B`, `L : B ⥤ C`, and `G : B ⥤ D`,
we introduce a typeclass `G.PreservesLeftKanExtension F L`, which encodes the fact that
the left/right Kan extension of `F` along `L` is preserved by the functor `G`.

When the Kan extension is pointwise, It suffices that `G` preserves (co)limits of the relevant
diagrams.

-/

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  (G : B ⥤ D) (F : A ⥤ B) (L : A ⥤ C)

section LeftKanExtension

/-- `G.PreservesLeftKanExtension F L` asserts that `G` preserves all left kan extensions
of `F` along `L`. -/
class PreservesLeftKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α],
    IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom

attribute [instance] PreservesLeftKanExtension.preserves

/-- `G.PreservesLeftKanExtensionAt F L c` asserts that `G` preserves pointwise all left kan
extensions of `F` along `L` at the point `c`. -/
class PreservesPointwiseLeftKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : ∀ (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c →
    (LeftExtension.whiskerRight L F G|>.obj E).IsPointwiseLeftKanExtensionAt c

/-- `G.PreservesLeftKanExtension F L` asserts that `G` preserves all pointwise left kan extensions
of `F` along `L`. -/
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
def LeftExtension.coconeAtWhiskerRightIso (E : LeftExtension L F) (c : C) :
    ((LeftExtension.whiskerRight L F G).obj E).coconeAt c ≅ G.mapCocone (E.coconeAt c) :=
  Limits.Cocones.ext (Iso.refl _)

instance hasLeftKanExtension_of_preserves [L.HasLeftKanExtension F]
    [PreservesLeftKanExtension G F L] : L.HasLeftKanExtension (F ⋙ G) :=
  @HasLeftKanExtension.mk _ _ _ _ _ _ _ _ _ _ <|
    letI : (L.leftKanExtension F).IsLeftKanExtension <| L.leftKanExtensionUnit F := by
      infer_instance
    PreservesLeftKanExtension.preserves (L.leftKanExtension F) (L.leftKanExtensionUnit F)

instance hasPointwiseLeftKanExtension_of_preserves [L.HasPointwiseLeftKanExtension F]
    [PreservesPointwiseLeftKanExtension G F L] : L.HasPointwiseLeftKanExtension (F ⋙ G) :=
  (PreservesPointwiseLeftKanExtension.preserves G F L _
    <| pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).hasPointwiseLeftKanExtension

/-- Extract an isomorphism `(leftKanExtension L F) ⋙ G ≅ leftKanExtension L (F ⋙ G)` when `G`
preserves left Kan extensions. -/
noncomputable def leftKanExtensionCompIsoOfPreserves [PreservesLeftKanExtension G F L]
    [L.HasLeftKanExtension F] :
    L.leftKanExtension F ⋙ G ≅ L.leftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.leftKanExtension F ⋙ G)
    (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.leftKanExtension <| F ⋙ G)
    (L.leftKanExtensionUnit <| F ⋙ G)

section

variable [PreservesLeftKanExtension G F L] [L.HasLeftKanExtension F]

@[reassoc (attr := simp)]
lemma leftKanExtensionCompIsoOfPreserves_fac :
    whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L (leftKanExtensionCompIsoOfPreserves G F L).hom =
    (L.leftKanExtensionUnit <| F ⋙ G) := by
  simpa [leftKanExtensionCompIsoOfPreserves] using descOfIsLeftKanExtension_fac
    (α := whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (β := L.leftKanExtensionUnit (F ⋙ G))

@[reassoc (attr := simp)]
lemma leftKanExtensionCompIsoOfPreserves_fac_app (a : A) :
    G.map ((L.leftKanExtensionUnit F).app a) ≫
      (G.leftKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) =
    (L.leftKanExtensionUnit (F ⋙ G)).app a := by
  simpa [- leftKanExtensionCompIsoOfPreserves_fac] using congrArg (fun t ↦ t.app a)
    (leftKanExtensionCompIsoOfPreserves_fac G F L)

end

/-- A functor that preserves the colimit of `(CostructuredArrow.proj L c ⋙ F)` preserves
the pointwise left kan extension of `F` along `L` at c. -/
noncomputable instance preservesPointwiseLeftKanExtensionAtOfPreservesColimit (c : C)
    [Limits.PreservesColimit (CostructuredArrow.proj L c ⋙ F) G] :
    G.PreservesPointwiseLeftKanExtensionAt F L c where
  preserves E p :=
    Limits.IsColimit.ofIsoColimit
      (Limits.PreservesColimit.preserves p).some
      (E.coconeAtWhiskerRightIso G _ _ c).symm

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
noncomputable def pointwiseLeftKanExtensionCompIsoOfPreserves
    [PreservesPointwiseLeftKanExtension G F L]
    [L.HasPointwiseLeftKanExtension F] :
    L.pointwiseLeftKanExtension F ⋙ G ≅ L.pointwiseLeftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.pointwiseLeftKanExtension F ⋙ G)
    (whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.pointwiseLeftKanExtension <| F ⋙ G)
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

section

variable [PreservesPointwiseLeftKanExtension G F L] [L.HasPointwiseLeftKanExtension F]

@[reassoc (attr := simp)]
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_fac :
    whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L (pointwiseLeftKanExtensionCompIsoOfPreserves G F L).hom =
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G) := by
  simpa [pointwiseLeftKanExtensionCompIsoOfPreserves] using descOfIsLeftKanExtension_fac
    (α := whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (β := L.pointwiseLeftKanExtensionUnit (F ⋙ G))

@[reassoc (attr := simp)]
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app (a : A) :
    G.map ((L.pointwiseLeftKanExtensionUnit F).app a) ≫
      (G.pointwiseLeftKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) =
    (L.pointwiseLeftKanExtensionUnit (F ⋙ G)).app a := by
  simpa [- pointwiseLeftKanExtensionCompIsoOfPreserves_fac] using congrArg (fun t ↦ t.app a)
    (pointwiseLeftKanExtensionCompIsoOfPreserves_fac G F L)

end

/-- `G.PreservesLeftKanExtensions L` means that `G : B ⥤ D` preserves all left Kan extensions along
`L : A ⥤ C` of every functor `A ⥤ B`. -/
abbrev PreservesLeftKanExtensions := ∀ (F : A ⥤ B), G.PreservesLeftKanExtension F L

/-- `G.PreservesPointwiseLeftKanExtensions L` means that `G : B ⥤ D` preserves all pointwise left
Kan extensions along `L : A ⥤ C` of every functor `A ⥤ B`. -/
abbrev PreservesPointwiseLeftKanExtensions :=
  ∀ (F : A ⥤ B), G.PreservesPointwiseLeftKanExtension F L

/-- Commuting a functor that preserves left Kan extensions with the `lan` functor. -/
@[simps!]
noncomputable def lanFunctorCompOfPreserves [G.PreservesLeftKanExtensions L]
    [∀ F : A ⥤ B, HasLeftKanExtension L F]
    [∀ F : A ⥤ D, HasLeftKanExtension L F] :
    L.lan ⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.lan :=
  NatIso.ofComponents (fun F ↦ leftKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η ↦ by
      apply hom_ext_of_isLeftKanExtension (L.leftKanExtension F ⋙ G)
        (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      dsimp [lan]
      ext
      simp [← G.map_comp_assoc])

end LeftKanExtension

section RightKanExtension

/-- `G.PreservesRightKanExtension F L` asserts that `G` preserves all right kan extensions
of `F` along `L` -/
class PreservesRightKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α],
    IsRightKanExtension (F' ⋙ G) <| (Functor.associator _ _ _).inv ≫ whiskerRight α G

attribute [instance] PreservesRightKanExtension.preserves

/-- `G.PreservesRightKanExtensionAt F L c` asserts that `G` preserves all right pointwise right kan
extensions of `F` along `L` at `c`. -/
class PreservesPointwiseRightKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : ∀ (E : RightExtension L F), E.IsPointwiseRightKanExtensionAt c →
    (RightExtension.whiskerRight L F G|>.obj E).IsPointwiseRightKanExtensionAt c

/-- `G.PreservesRightKanExtensions L` asserts that `G` preserves all pointwise right kan
extensions of `F` along `L` for every `F`. -/
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
def RightExtension.coneAtWhiskerRightIso (E : RightExtension L F) (c : C) :
    (RightExtension.whiskerRight L F G|>.obj E).coneAt c ≅ G.mapCone (E.coneAt c) :=
  Limits.Cones.ext (Iso.refl _)

instance hasRightKanExtension_of_preserves [L.HasRightKanExtension F]
    [PreservesRightKanExtension G F L] : L.HasRightKanExtension (F ⋙ G) :=
  @HasRightKanExtension.mk _ _ _ _ _ _ _ _ _ _ <|
    letI : (L.rightKanExtension F).IsRightKanExtension <| L.rightKanExtensionCounit F := by
      infer_instance
    PreservesRightKanExtension.preserves (L.rightKanExtension F) (L.rightKanExtensionCounit F)

instance hasPointwiseRightKanExtension_of_preserves [L.HasPointwiseRightKanExtension F]
    [PreservesPointwiseRightKanExtension G F L] : L.HasPointwiseRightKanExtension (F ⋙ G) :=
  (PreservesPointwiseRightKanExtension.preserves G F L _
    <| pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).hasPointwiseRightKanExtension

/-- Extract an isomorphism `(rightKanExtension L F) ⋙ G ≅ rightKanExtension L (F ⋙ G)` when `G`
preserves left Kan extensions. -/
noncomputable def rightKanExtensionCompIsoOfPreserves [PreservesRightKanExtension G F L]
    [L.HasRightKanExtension F] :
    L.rightKanExtension F ⋙ G ≅ L.rightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.rightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G)
    (L.rightKanExtension <| F ⋙ G)
    (L.rightKanExtensionCounit <| F ⋙ G)

section

variable [PreservesRightKanExtension G F L] [L.HasRightKanExtension F]

@[reassoc (attr := simp)]
lemma rightKanExtensionCompIsoOfPreserves_fac :
    whiskerLeft L (rightKanExtensionCompIsoOfPreserves G F L).hom ≫
      (L.rightKanExtensionCounit <| F ⋙ G) =
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G):= by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]
lemma rightKanExtensionCompIsoOfPreserves_fac_app (a : A) :
    (G.rightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫
      (L.rightKanExtensionCounit (F ⋙ G)).app a =
    G.map ((L.rightKanExtensionCounit F).app a) := by
  simp [rightKanExtensionCompIsoOfPreserves]

end

/-- A functor that preserves the colimit of `(StructuredArrow.proj L c ⋙ F)` preserves
the pointwise right kan extension of `F` along `L` at c. -/
noncomputable instance preservesPointwiseRightKanExtensionAtOfPreservesColimit (c : C)
    [Limits.PreservesLimit (StructuredArrow.proj c L ⋙ F) G] :
    G.PreservesPointwiseRightKanExtensionAt F L c where
  preserves E p :=
    Limits.IsLimit.ofIsoLimit
      (Limits.PreservesLimit.preserves p).some
      (E.coneAtWhiskerRightIso G _ _ c).symm

/-- If there is a pointwise right Kan extension of `F` along `L`, and if `G` preserves them,
then `G` preserves right Kan extensions of `F` along `L`. -/
noncomputable instance preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseRightKanExtension L F] [G.PreservesPointwiseRightKanExtension F L] :
    G.PreservesRightKanExtension F L where
  preserves F' α _ :=
    (RightExtension.isPointwiseRightKanExtensionEquivOfIso (RightExtension.whiskerRightIsoMk G α) <|
      PreservesPointwiseRightKanExtension.preserves G F L _ <|
        isPointwiseRightKanExtensionOfIsRightKanExtension F' α).isRightKanExtension

/-- Extract an isomorphism
`(pointwiseRightKanExtension L F) ⋙ G ≅ pointwiseRightKanExtension L (F ⋙ G)` when `G` preserves
right Kan extensions. -/
noncomputable def pointwiseRightKanExtensionCompIsoOfPreserves
    [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F] :
    L.pointwiseRightKanExtension F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.pointwiseRightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G)
    (L.pointwiseRightKanExtension <| F ⋙ G)
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G)

section

variable [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F]

@[reassoc (attr := simp)]
lemma pointwiseRightKanExtensionCompIsoOfPreserves_fac :
    whiskerLeft L (pointwiseRightKanExtensionCompIsoOfPreserves G F L).hom ≫
      (L.pointwiseRightKanExtensionCounit <| F ⋙ G) =
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G):= by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]
lemma pointwiseRightKanExtensionCompIsoOfPreserves_fac_app (a : A) :
    (G.pointwiseRightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫
      (L.pointwiseRightKanExtensionCounit (F ⋙ G)).app a =
    G.map ((L.pointwiseRightKanExtensionCounit F).app a) := by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_fac] using
    congrArg (fun t ↦ t.app a) <| pointwiseRightKanExtensionCompIsoOfPreserves_fac G F L

end

/-- `G.PreservesRightKanExtensions L` means that `G : B ⥤ D` preserves all right Kan extensions
along `L : A ⥤ C` of every functor `A ⥤ B`. -/
abbrev PreservesRightKanExtensions := ∀ (F : A ⥤ B), G.PreservesRightKanExtension F L

/-- `G.PreservesPointwiseRightKanExtensions L` means that `G : B ⥤ D` preserves all pointwise right
Kan extensions along `L : A ⥤ C` of every functor `A ⥤ B`. -/
abbrev PreservesPointwiseRightKanExtensions :=
  ∀ (F : A ⥤ B), G.PreservesPointwiseRightKanExtension F L

/-- Commuting a functor that preserves right Kan extensions with the `ran` functor. -/
@[simps!]
noncomputable def ranFunctorCompOfPreserves [G.PreservesRightKanExtensions L]
    [∀ F : A ⥤ B, HasRightKanExtension L F] [∀ F : A ⥤ D, HasRightKanExtension L F] :
    L.ran ⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.ran :=
  NatIso.ofComponents (fun F ↦ rightKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η ↦ by
      apply hom_ext_of_isRightKanExtension
        (L.rightKanExtension <| F' ⋙ G)
        (L.rightKanExtensionCounit <| F' ⋙ G)
      dsimp [ran]
      ext
      simp only [comp_obj, Category.assoc, rightKanExtensionCompIsoOfPreserves_fac,
        NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app, Category.id_comp,
        liftOfIsRightKanExtension_fac, rightKanExtensionCompIsoOfPreserves_fac_assoc, ← G.map_comp ]
      simp)

end RightKanExtension

end CategoryTheory.Functor
