/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# Natural transformations of colimits of representable functors
-/

open CategoryTheory Limits Opposite

universe v v₁ v₂ u u₁ u₂

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I (Type v)]
  [HasLimitsOfShape Iᵒᵖ (Type v)]
variable {J : Type u₂} [Category.{v₂} J] [HasColimitsOfShape J (Type v)]
  [HasLimitsOfShape Iᵒᵖ (Type (max u v))]
  [HasColimitsOfShape J (Type (max u v))]
variable (F : I ⥤ C) (G : J ⥤ C)

noncomputable def final : (colimit (F ⋙ yoneda) ⟶ colimit (G ⋙ yoneda)) ≅
    uliftFunctor.{u}.obj (limit (colimit (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op)))) := calc
  (colimit (F ⋙ yoneda) ⟶ colimit (G ⋙ yoneda)) ≅
    limit (F.op ⋙ colimit (G ⋙ yoneda) ⋙ uliftFunctor.{u}) := colimitYonedaHomIsoLimit F.op _
  _ ≅ limit ((F.op ⋙ colimit (G ⋙ yoneda)) ⋙ uliftFunctor.{u}) :=
      HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u}.obj (limit (F.op ⋙ colimit (G ⋙ yoneda))) :=
      (preservesLimitIso _ _).symm
  _ ≅ uliftFunctor.{u}.obj
        (limit (colimit ((G ⋙ yoneda) ⋙ (whiskeringLeft _ _ _).obj F.op))) :=
      uliftFunctor.{u}.mapIso (HasLimit.isoOfNatIso
      (colimitCompWhiskeringLeftIsoCompColimit _ _).symm)
  _ ≅ uliftFunctor.{u}.obj
        (limit (colimit (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op)))) :=
      uliftFunctor.{u}.mapIso (HasLimit.isoOfNatIso (HasColimit.isoOfNatIso
        (Functor.associator _ _ _)))

noncomputable def final' : (colimit (F ⋙ yoneda) ⟶ colimit (G ⋙ yoneda)) ≃
    limit (colimit (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op))) :=
  (final F G).toEquiv.trans Equiv.ulift

instance : Small.{v} (colimit (F ⋙ yoneda) ⟶ colimit (G ⋙ yoneda)) where
  equiv_small := ⟨_, ⟨final' F G⟩⟩

end

instance : LocallySmall.{v} (FullSubcategory (IsIndObject (C := C))) where
  hom_small X Y := by
    obtain ⟨⟨P⟩⟩ := X.2
    obtain ⟨⟨Q⟩⟩ := Y.2
    let e₁ := IsColimit.coconePointUniqueUpToIso (P.isColimit) (colimit.isColimit _)
    let e₂ := IsColimit.coconePointUniqueUpToIso (Q.isColimit) (colimit.isColimit _)
    let e₃ := Iso.homCongr e₁ e₂
    dsimp at e₃
    exact small_map e₃

variable (C) in
def Ind : Type (max u (v + 1)) := ShrinkHoms (FullSubcategory (IsIndObject (C := C)))

noncomputable instance : Category.{v} (Ind C) :=
  inferInstanceAs (Category.{v} (ShrinkHoms (FullSubcategory (IsIndObject (C := C)))))

noncomputable def Ind.equivalence : Ind C ≌ FullSubcategory (IsIndObject (C := C)) :=
  (ShrinkHoms.equivalence _).symm

end CategoryTheory
