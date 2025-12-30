/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
<<<<<<< HEAD
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Localization.StructuredArrow
=======
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Localization.StructuredArrow
>>>>>>> origin/master

/-!
# Pointwise right derived functors

<<<<<<< HEAD
We define the pointwise right derived functors using the notion
=======
We define pointwise right derived functors using the notion
>>>>>>> origin/master
of pointwise left Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise right derived functor.

<<<<<<< HEAD
-/

=======
Note: the file `Mathlib/CategoryTheory/Functor/Derived/PointwiseLeftDerived.lean` was obtained
by dualizing this file. These two files should be kept in sync.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

>>>>>>> origin/master
namespace CategoryTheory

open Category Limits

namespace Functor

<<<<<<< HEAD
variable {C D H : Type _} [Category C] [Category D] [Category H]
=======
variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
>>>>>>> origin/master
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

/-- Given `F : C ⥤ H`, `W : MorphismProperty C` and `X : C`, we say that `F` has a
pointwise right derived functor at `X` if `F` has a left Kan extension
at `L.obj X` for any localization functor `L : C ⥤ D` for `W`. In the
definition, this is stated for `L := W.Q`, see `hasPointwiseRightDerivedFunctorAt_iff`
for the more general equivalence. -/
class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
<<<<<<< HEAD
=======
  /-- Use the more general `hasColimit` lemma instead, see also
  `hasPointwiseRightDerivedFunctorAt_iff` -/
>>>>>>> origin/master
  hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

/-- A functor `F : C ⥤ H` has a pointwise right derived functor with respect to
`W : MorphismProperty C` if it has a pointwise right derived functor at `X`
for any `X : C`. -/
abbrev HasPointwiseRightDerivedFunctor := ∀ (X : C), F.HasPointwiseRightDerivedFunctorAt W X

lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
<<<<<<< HEAD
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩
=======
  exact ⟨fun h ↦ h.hasColimit', fun h ↦ ⟨h⟩⟩

lemma HasPointwiseRightDerivedFunctorAt.hasColimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseRightDerivedFunctorAt W X] :
    HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseRightDerivedFunctorAt_iff F L W]
>>>>>>> origin/master

lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseRightDerivedFunctor W]

lemma hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor [L.IsLocalization W] :
<<<<<<< HEAD
      HasPointwiseLeftKanExtension L F := fun Y => by
    have := Localization.essSurj L W
    rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
      ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
    infer_instance
=======
    HasPointwiseLeftKanExtension L F := fun Y ↦ by
  have := Localization.essSurj L W
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
    ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
  infer_instance
>>>>>>> origin/master

lemma hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have := F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

variable {F L}

/-- A right derived functor is a pointwise right derived functor when
there exists a pointwise right derived functor. -/
noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
<<<<<<< HEAD
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension := by
  have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α
=======
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α
>>>>>>> origin/master

end

section

variable {F L}

/-- If `L : C ⥤ D` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.hom` makes `G` a pointwise left Kan extension of `F` along `L` at `L.obj Y`
for any `Y : C`. -/
<<<<<<< HEAD
def isPointwiseLeftKanExtensionAtOfIso
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s := by
    intro j
=======
def isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s j := by
>>>>>>> origin/master
    refine Localization.induction_costructuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ ↦ ?_) (fun X₁ X₂ w hw φ hφ ↦ ?_) j
    · have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [assoc, map_comp_assoc, ← eq, ← hφ, NatTrans.naturality_assoc, comp_map]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [map_comp, assoc, assoc, ← cancel_epi (F.map w), eq, ← hφ,
        NatTrans.naturality_assoc, comp_map, ← G.map_comp_assoc]
      simp
  uniq s m hm := by
    have := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp only [← this, map_id, comp_id, Iso.inv_hom_id_app_assoc]

/-- If `L` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
<<<<<<< HEAD
then `e.hom` makes `G` a poinwise left Kan extension of `F` along `L`. -/
noncomputable def isPointwiseLeftKanExtensionOfIso
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y => by
  have := Localization.essSurj L W
  exact (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIso W e _)
=======
then `e.hom` makes `G` a pointwise left Kan extension of `F` along `L`. -/
noncomputable def isPointwiseLeftKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y ↦
  have := Localization.essSurj L W
  (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization W e _)
>>>>>>> origin/master

/-- Let `L : C ⥤ D` be a localization functor for `W`, if an extension `E`
of `F : C ⥤ H` along `L` is such that the natural transformation
`E.hom : F ⟶ L ⋙ E.right` is an isomorphism, then `E` is a pointwise
<<<<<<< HEAD
left Ken extension. -/
noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIso
    (E : LeftExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIso W (asIso E.hom)

variable {W} in
=======
left Kan extension. -/
noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization
    (E : LeftExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization W (asIso E.hom)

>>>>>>> origin/master
lemma hasPointwiseRightDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
<<<<<<< HEAD
  exact (isPointwiseLeftKanExtensionOfIso W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension  _
=======
  exact (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension _
>>>>>>> origin/master

lemma isRightDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsRightDerivedFunctor e.inv W where
  isLeftKanExtension :=
<<<<<<< HEAD
    (isPointwiseLeftKanExtensionOfIso W e.symm).isLeftKanExtension
=======
    (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W e.symm).isLeftKanExtension

instance [L.IsLocalization W] (hF : W.IsInvertedBy F) :
    (Localization.lift F hF L).IsRightDerivedFunctor (Localization.fac F hF L).inv W :=
  isRightDerivedFunctor_of_inverts W _ _
>>>>>>> origin/master

variable {W} in
lemma isIso_of_isRightDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) [RF.IsRightDerivedFunctor α W] :
    IsIso α := by
<<<<<<< HEAD
  let e := Localization.fac F hF L
  have := isRightDerivedFunctor_of_inverts W _ e
  have : α = e.inv ≫ whiskerLeft _ (rightDerivedUnique _ _ e.inv α W).hom := by simp
  rw [this]
  infer_instance

=======
  have : α = (Localization.fac F hF L).inv ≫
    whiskerLeft _ (rightDerivedUnique _ _ (Localization.fac F hF L).inv α W).hom := by simp
  rw [this]
  infer_instance

variable {W} in
lemma isRightDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) :
    RF.IsRightDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ ↦ isIso_of_isRightDerivedFunctor_of_inverts RF α hF, fun _ ↦
    isRightDerivedFunctor_of_inverts W RF (asIso α).symm⟩

>>>>>>> origin/master
end

end Functor

end CategoryTheory
