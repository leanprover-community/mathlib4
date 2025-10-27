/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# The shift induced on a localized category

Let `C` be a category equipped with a shift by a monoid `A`. A morphism property `W`
on `C` satisfies `W.IsCompatibleWithShift A` when for all `a : A`,
a morphism `f` is in `W` iff `f⟦a⟧'` is. When this compatibility is satisfied,
then the corresponding localized category can be equipped with
a shift by `A`, and the localization functor is compatible with the shift.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (A : Type w) [AddMonoid A] [HasShift C A]

namespace MorphismProperty

/-- A morphism property `W` on a category `C` is compatible with the shift by a
monoid `A` when for all `a : A`, a morphism `f` belongs to `W`
if and only if `f⟦a⟧'` does. -/
class IsCompatibleWithShift : Prop where
  /-- the condition that for all `a : A`, the morphism property `W` is not changed when
  we take its inverse image by the shift functor by `a` -/
  condition : ∀ (a : A), W.inverseImage (shiftFunctor C a) = W

variable [W.IsCompatibleWithShift A]

namespace IsCompatibleWithShift

variable {A}

lemma iff {X Y : C} (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f := by
  conv_rhs => rw [← @IsCompatibleWithShift.condition _ _ W A _ _ _ a]
  rfl

lemma shiftFunctor_comp_inverts (a : A) :
    W.IsInvertedBy (shiftFunctor C a ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)

end IsCompatibleWithShift

variable {A} in
lemma shift {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A) : W (f⟦a⟧') := by
  simpa only [IsCompatibleWithShift.iff W f a] using hf

variable {A} in
/-- The morphism of localizer from `W` to `W` given by the functor `shiftFunctor C a`
when `a : A` and `W` is compatible with the shift by `A`. -/
abbrev shiftLocalizerMorphism (a : A) : LocalizerMorphism W W where
  functor := shiftFunctor C a
  map := by rw [MorphismProperty.IsCompatibleWithShift.condition]

end MorphismProperty

section
variable [W.IsCompatibleWithShift A]

/-- When `L : C ⥤ D` is a localization functor with respect to a morphism property `W`
that is compatible with the shift by a monoid `A` on `C`, this is the induced
shift on the category `D`. -/
noncomputable def HasShift.localized : HasShift D A :=
  have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  HasShift.induced L A
    (fun a => Localization.lift (shiftFunctor C a ⋙ L)
      (MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts L W a) L)
    (fun _ => Localization.fac _ _ _)

/-- The localization functor `L : C ⥤ D` is compatible with the shift. -/
@[nolint unusedHavesSuffices]
noncomputable def Functor.CommShift.localized :
    @Functor.CommShift _ _ _ _ L A _ _ (HasShift.localized L W A) :=
  have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  Functor.CommShift.ofInduced _ _ _ _

attribute [irreducible] HasShift.localized Functor.CommShift.localized

/-- The localized category `W.Localization` is endowed with the induced shift. -/
noncomputable instance HasShift.localization :
    HasShift W.Localization A :=
  HasShift.localized W.Q W A

/-- The localization functor `W.Q : C ⥤ W.Localization` is compatible with the shift. -/
noncomputable instance MorphismProperty.commShift_Q :
    W.Q.CommShift A :=
  Functor.CommShift.localized W.Q W A

attribute [irreducible] HasShift.localization MorphismProperty.commShift_Q

variable [W.HasLocalization]

/-- The localized category `W.Localization'` is endowed with the induced shift. -/
noncomputable instance HasShift.localization' :
    HasShift W.Localization' A :=
  HasShift.localized W.Q' W A

/-- The localization functor `W.Q' : C ⥤ W.Localization'` is compatible with the shift. -/
noncomputable instance MorphismProperty.commShift_Q' :
    W.Q'.CommShift A :=
  Functor.CommShift.localized W.Q' W A

attribute [irreducible] HasShift.localization' MorphismProperty.commShift_Q'

end

section

open Localization

variable (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
  [HasShift D A] [HasShift E A] [L.CommShift A] [F.CommShift A]

namespace Functor

namespace commShiftOfLocalization

variable {A}

/-- Auxiliary definition for `Functor.commShiftOfLocalization`. -/
noncomputable def iso (a : A) :
    shiftFunctor D a ⋙ F' ≅ F' ⋙ shiftFunctor E a :=
  Localization.liftNatIso L W (L ⋙ shiftFunctor D a ⋙ F')
    (L ⋙ F' ⋙ shiftFunctor E a) _ _
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (L.commShiftIso a).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (Lifting.iso L W F F') ≪≫
        F.commShiftIso a ≪≫
        isoWhiskerRight (Lifting.iso L W F F').symm _ ≪≫ Functor.associator _ _ _)

@[simp, reassoc]
lemma iso_hom_app (a : A) (X : C) :
    (commShiftOfLocalization.iso L W F F' a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫
      (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  simp [commShiftOfLocalization.iso]

@[simp, reassoc]
lemma iso_inv_app (a : A) (X : C) :
    (commShiftOfLocalization.iso L W F F' a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫
      (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  simp [commShiftOfLocalization.iso]

end commShiftOfLocalization

/-- In the context of localization of categories, if a functor
is induced by a functor which commutes with the shift, then
this functor commutes with the shift. -/
noncomputable def commShiftOfLocalization : F'.CommShift A where
  iso := commShiftOfLocalization.iso L W F F'
  zero := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_zero,
      CommShift.isoZero_inv_app, map_comp, CommShift.isoZero_hom_app, Category.assoc,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality]
    dsimp
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, id_obj, map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  add a b := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_add,
      CommShift.isoAdd_inv_app, map_comp, CommShift.isoAdd_hom_app, Category.assoc]
    congr 1
    rw [← cancel_epi (F'.map ((shiftFunctor D b).map ((L.commShiftIso a).hom.app X))),
      ← F'.map_comp_assoc, ← map_comp, Iso.hom_inv_id_app, map_id, map_id, Category.id_comp]
    conv_lhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc, ← map_comp_assoc, Category.assoc,
        ← map_comp, Iso.inv_hom_id_app]
      dsimp
      rw [map_id, Category.comp_id, ← NatTrans.naturality]
      dsimp
    conv_rhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc, ← map_comp, Iso.hom_inv_id_app]
      dsimp
      rw [map_id, map_id, Category.id_comp, commShiftOfLocalization.iso_hom_app,
        Category.assoc, Category.assoc, Category.assoc, ← map_comp_assoc,
        Iso.inv_hom_id_app, map_id, Category.id_comp]

variable {A}

lemma commShiftOfLocalization_iso_hom_app (a : A) (X : C) :
    letI := Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  apply commShiftOfLocalization.iso_hom_app

lemma commShiftOfLocalization_iso_inv_app (a : A) (X : C) :
    letI := Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫ (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  apply commShiftOfLocalization.iso_inv_app

end Functor

instance NatTrans.commShift_iso_hom_of_localization :
    letI := Functor.commShiftOfLocalization L W A F F'
    NatTrans.CommShift (Lifting.iso L W F F').hom A := by
  letI := Functor.commShiftOfLocalization L W A F F'
  constructor
  intro a
  ext X
  simp only [comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app,
    Functor.commShiftOfLocalization_iso_hom_app,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Iso.inv_hom_id_app,
    Category.comp_id, Category.id_comp, Functor.comp_obj]

end

namespace LocalizerMorphism

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂)
  {M : Type*} [AddMonoid M] [HasShift C₁ M] [HasShift C₂ M]
  [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M] [Φ.functor.CommShift M]

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
  [HasShift D₁ M] [HasShift D₂ M] [L₁.CommShift M] [L₂.CommShift M]

noncomputable instance : (Φ.localizedFunctor L₁ L₂).CommShift M :=
  Functor.commShiftOfLocalization L₁ W₁ M (Φ.functor ⋙ L₂) _

end LocalizerMorphism

end CategoryTheory
