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

variable {D : Type u₁} [Category.{max v v₁} D] (F : C ⥤ D) (hF : F.FullyFaithful)

def homNatIsoMaxRight' (hF : F.FullyFaithful) : F ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ≅
    yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₁} :=
  NatIso.ofComponents (fun X => hF.homNatIsoMaxRight _) (by
    intro X Y f
    ext Z g
    dsimp at g
    simp [Functor.FullyFaithful.homNatIsoMaxRight, Equiv.ulift]
    apply hF.map_injective
    simp)

end

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
      (yoneda.obj (colimit (G ⋙ yoneda))).obj (op (colimit (F ⋙ yoneda))) := Iso.refl _
  _ ≅ (yoneda.obj (colimit (G ⋙ yoneda))).obj (limit (F ⋙ yoneda).op) :=
        Functor.mapIso _ (by exact (limitOpIsoOpColimit (F ⋙ yoneda)).symm)
  _ ≅ limit ((F ⋙ yoneda).op ⋙ yoneda.obj (colimit (G ⋙ yoneda))) :=
        preservesLimitIso _ _
  _ ≅ limit ((F.op ⋙ yoneda.op) ⋙ yoneda.obj (colimit (G ⋙ yoneda))) :=
        HasLimit.isoOfNatIso (isoWhiskerRight (Iso.refl _) _)
  _ ≅ limit (F.op ⋙ yoneda.op ⋙ yoneda.obj (colimit (G ⋙ yoneda))) :=
        HasLimit.isoOfNatIso (Iso.refl _)
  _ ≅ limit (F.op ⋙ yoneda.op ⋙ colimit ((G ⋙ yoneda) ⋙ yoneda)) :=
        HasLimit.isoOfNatIso (isoWhiskerLeft _ (yonedaYonedaColimit _))
  _ ≅ limit ((F ⋙ yoneda).op ⋙ colimit ((G ⋙ yoneda) ⋙ yoneda)) :=
        Iso.refl _
  _ ≅ limit (colimit ((G ⋙ yoneda) ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj (F ⋙ yoneda).op)) :=
        HasLimit.isoOfNatIso (colimitCompWhiskeringLeftIsoCompColimit _ _).symm
  _ ≅ limit (colimit ((G ⋙ yoneda) ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj yoneda.op ⋙
        (whiskeringLeft _ _ _).obj F.op)) := Iso.refl _
  _ ≅ limit (colimit (G ⋙ (yoneda ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj yoneda.op) ⋙
        (whiskeringLeft _ _ _).obj F.op)) := Iso.refl _
  _ ≅ limit (colimit (G ⋙ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}) ⋙
          (whiskeringLeft _ _ _).obj F.op)) :=
        HasLimit.isoOfNatIso (HasColimit.isoOfNatIso
          (isoWhiskerLeft _ (isoWhiskerRight (homNatIsoMaxRight' yoneda Yoneda.fullyFaithful) _)))
  _ ≅ limit (colimit (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op) ⋙
        (whiskeringRight _ _ _).obj uliftFunctor.{u})) := Iso.refl _
  _ ≅ limit (colimit (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op)) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (colimitCompWhiskeringRightIsoColimitComp
          (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op)) uliftFunctor.{u})
  _ ≅ uliftFunctor.{u}.obj (limit (colimit (G ⋙ (yoneda ⋙ (whiskeringLeft _ _ _).obj F.op)))) :=
        (preservesLimitIso _ _).symm

instance : Small.{v} (colimit (F ⋙ yoneda) ⟶ colimit (G ⋙ yoneda)) where
  equiv_small := ⟨_, ⟨(final F G).toEquiv.trans Equiv.ulift⟩⟩

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
