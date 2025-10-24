/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.Continuous
import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# The representation theorem

In this file, we show that if `C` is a locally `κ`-presentable category,
then `C` identifies to the category of `κ`-continuous presheaves on
the fullsubcategory of `κ`-presentable objects of `C`.

-/

universe w v v' u u'

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]

@[simps!]
def whiskeringLeftObjCompWhiskeringRightObj (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) :
    (whiskeringLeft C₁ C₂ C₃).obj F ⋙ (whiskeringRight C₁ C₃ C₄).obj G ≅
      (whiskeringRight C₂ C₃ C₄).obj G ⋙ (whiskeringLeft C₁ C₂ C₄).obj F :=
  NatIso.ofComponents (fun _ ↦ Functor.associator _ _ _)

end Functor

-- to be moved
namespace Presheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [LocallySmall.{w} D] (F : C ⥤ D)

noncomputable def shrinkYonedaCompWhiskeringRightUliftFunctorIso :
    shrinkYoneda.{w} (C := D) ⋙
      (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}) ≅
    uliftYoneda.{w} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans (Equiv.trans (equivShrink _).symm Equiv.ulift.symm)).toIso) (by
    intro Y₁ Y₂ f
    ext g
    simp [uliftYoneda, shrinkYoneda])) (by
    intro X₁ X₂ f
    ext Y g
    simp [uliftYoneda, shrinkYoneda])

noncomputable def restrictedShrinkYoneda : D ⥤ Cᵒᵖ ⥤ Type w :=
  shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

open Functor in
noncomputable def restrictedShrinkYonedaCompULiftIso :
    restrictedShrinkYoneda.{w} F ⋙
      (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}) ≅
        restrictedULiftYoneda.{w} F :=
  associator _ _ _ ≪≫
    isoWhiskerLeft _ (whiskeringLeftObjCompWhiskeringRightObj _ _) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight shrinkYonedaCompWhiskeringRightUliftFunctorIso.{w} _

variable [F.IsDense]

instance : (restrictedShrinkYoneda.{w} F).Faithful := by
  have := Functor.Faithful.of_iso (restrictedShrinkYonedaCompULiftIso.{w} F).symm
  exact Functor.Faithful.of_comp _ ((Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}))

instance : (restrictedShrinkYoneda.{w} F).Full := by
  have := Functor.Full.of_iso (restrictedShrinkYonedaCompULiftIso.{w} F).symm
  exact Functor.Full.of_comp_faithful _
    ((Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}))

end Presheaf

namespace IsCardinalLocallyPresentable

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable C κ]

#synth (isCardinalPresentable C κ).ι.IsDense
#check Presheaf.restrictedShrinkYoneda.{w} (C := C)

end IsCardinalLocallyPresentable

end CategoryTheory
