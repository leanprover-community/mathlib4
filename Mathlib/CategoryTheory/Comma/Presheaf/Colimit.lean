/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Limits.Over

/-!
# Relative Yoneda preserves certain colimits

In this file we turn the statement `yonedaYonedaColimit` from
`CategoryTheory.Limits.Preserves.Yoneda` from a functor `F : J ⥤ Cᵒᵖ ⥤ Type v` into a statement
about families of presheaves over `A`, i.e., functors `F : J ⥤ Over A`.
-/

namespace CategoryTheory

open Category Opposite Limits

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}
variable {J : Type v} [SmallCategory J] {A : Cᵒᵖ ⥤ Type v} (F : J ⥤ Over A)

-- We introduce some local notation to reduce visual noise in the following proof
local notation "E" => Equivalence.functor (overEquivPresheafCostructuredArrow A)
local notation "E.obj" =>
  Prefunctor.obj (Functor.toPrefunctor (Equivalence.functor (overEquivPresheafCostructuredArrow A)))

/-- Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`, where `Y` is the
    "Yoneda embedding" `CostructuredArrow.toOver yoneda A`. This is a relative version of
    `yonedaYonedaColimit`. -/
noncomputable def CostructuredArrow.toOverCompYonedaColimit :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F) ≅
    (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) := calc
  (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F)
    ≅ yoneda.op ⋙ yoneda.obj (E.obj (colimit F)) :=
        CostructuredArrow.toOverCompYoneda A _
  _ ≅ yoneda.op ⋙ yoneda.obj (colimit (F ⋙ E)) :=
        isoWhiskerLeft yoneda.op (yoneda.mapIso (preservesColimitIso _ F))
  _ ≅ yoneda.op ⋙ colimit ((F ⋙ E) ⋙ yoneda) :=
        yonedaYonedaColimit _
  _ ≅ yoneda.op ⋙ ((F ⋙ E) ⋙ yoneda).flip ⋙ colim :=
        isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj E) ⋙
          (whiskeringLeft _ _ _).obj F ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F ⋙ colim :=
        isoWhiskerRight (CostructuredArrow.toOverCompCoyoneda _).symm _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ (F ⋙ yoneda).flip ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) :=
      isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm

end CategoryTheory
