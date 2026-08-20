/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryAut

/-!
# ...

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

abbrev SingleObj.HasQuotient {X : C} (H : Subgroup (Aut X)) :=
    HasColimit (SingleObj.functor ((Aut.toEnd X).comp H.subtype))

noncomputable def SingleObj.quotient {X : C} (H : Subgroup (Aut X)) [HasQuotient H] : C :=
  colimit (SingleObj.functor ((Aut.toEnd X).comp H.subtype))

noncomputable def SingleObj.quotient.π {X : C} (H : Subgroup (Aut X)) [HasQuotient H] :
    X ⟶ quotient H :=
  colimit.ι (SingleObj.functor ((Aut.toEnd X).comp H.subtype))
    (Quiver.SingleObj.star _)

namespace GaloisCategory

variable [GaloisCategory C]

instance {X : C} (H : Subgroup (Aut X)) : SingleObj.HasQuotient H := by
  sorry

section

variable {Y X : C} {f : Y ⟶ X}
  [PreGaloisCategory.IsConnected X]
  (H : Subgroup (Aut (Over.mk f)))

noncomputable abbrev overQuotient : Over X := SingleObj.quotient H

instance [IsGaloisCover f] : PreGaloisCategory.IsConnected (overQuotient H).left := by
  sorry

instance [PreGaloisCategory.IsConnected Y] :
    PreGaloisCategory.IsConnected (overQuotient H).left := by
  sorry

noncomputable abbrev overQuotientπ : Y ⟶ (overQuotient H).left :=
  (SingleObj.quotient.π H).left

instance [IsGaloisCover f] : IsGaloisCover (overQuotientπ H) := sorry

@[simp]
lemma range_overMap_overQuotientπ :
    (Aut.overMap (overQuotientπ H) (overQuotient H).hom f).range = H := by
  sorry

end

lemma exists_of_subgroup
    {Y X : C} {f : Y ⟶ X} [PreGaloisCategory.IsConnected X] [IsGaloisCover f]
    (H : Subgroup (Aut (Over.mk f))) :
    ∃ (Z : C) (_ : PreGaloisCategory.IsConnected Z) (a : Y ⟶ Z) (b : Z ⟶ X) (fac : a ≫ b = f)
      (_ : IsGaloisCover a), (Aut.overMap a b f).range = H :=
  ⟨(overQuotient H).left, inferInstance, overQuotientπ H, (overQuotient H).hom,
    by simp, inferInstance, by simp⟩

lemma isGaloisCover_iff_normal
    {Z Y X : C} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X) [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    IsGaloisCover g ↔ (Aut.overMap f g fg).range.Normal := sorry

lemma exists_of_normal_subgroup
    {Y X : C} {f : Y ⟶ X} [PreGaloisCategory.IsConnected X] [IsGaloisCover f]
    (H : Subgroup (Aut (Over.mk f))) [H.Normal] :
    ∃ (Z : C) (_ :PreGaloisCategory.IsConnected Z) (a : Y ⟶ Z) (b : Z ⟶ X) (fac : a ≫ b = f)
      (_ : IsGaloisCover a) (_ : IsGaloisCover b), (Aut.overMap a b f).range = H := by
  obtain ⟨Z, _, a, b, fac, _, h⟩ := exists_of_subgroup H
  refine ⟨Z, inferInstance, a, b, fac, inferInstance, ?_, h⟩
  rw [isGaloisCover_iff_normal a b f, h]
  infer_instance

end GaloisCategory

end CategoryTheory
