/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.LocallySmall
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# The category of Ind-objects

We define the `v`-category of Ind-objects of a category `C`, called `Ind C`, as well as the functors
`Ind.yoneda : C ⥤ Ind C` and `Ind.inclusion C : Ind C ⥤ Cᵒᵖ ⥤ Type v`.

This file will mainly collect results about ind-objects (stated in terms of `IsIndObject`) and
reinterpret them in terms of `Ind C`. For now, we show that `Ind C` has filtered colimits and that
`Ind.inclusion C` creates them. Many other limit-colimit properties will follow.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The category of Ind-objects of `C`. -/
def Ind : Type (max u (v + 1)) :=
  ShrinkHoms (FullSubcategory (IsIndObject (C := C)))

noncomputable instance : Category.{v} (Ind C) :=
  inferInstanceAs <| Category.{v} (ShrinkHoms (FullSubcategory (IsIndObject (C := C))))

variable (C) in
/-- The defining properties of `Ind C` are that its morphisms live in `v` and that it is equivalent
to the full subcategory of `Cᵒᵖ ⥤ Type v` containing the ind-objects. -/
noncomputable def Ind.equivalence : Ind C ≌ FullSubcategory (IsIndObject (C := C)) :=
  (ShrinkHoms.equivalence _).symm

variable (C) in
/-- The canonical inclusion of ind-objects into presheaves. -/
protected noncomputable def Ind.inclusion : Ind C ⥤ Cᵒᵖ ⥤ Type v :=
  (Ind.equivalence C).functor ⋙ fullSubcategoryInclusion _

instance : (Ind.inclusion C).Full :=
  inferInstanceAs <| ((Ind.equivalence C).functor ⋙ fullSubcategoryInclusion _).Full

instance : (Ind.inclusion C).Faithful :=
  inferInstanceAs <| ((Ind.equivalence C).functor ⋙ fullSubcategoryInclusion _).Faithful

/-- The inclusion of `C` into `Ind C` induced by the Yoneda embedding. -/
protected noncomputable def Ind.yoneda : C ⥤ Ind C :=
  FullSubcategory.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

instance : (Ind.yoneda (C := C)).Full :=
  inferInstanceAs <| Functor.Full <|
    FullSubcategory.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

instance : (Ind.yoneda (C := C)).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    FullSubcategory.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

/-- The composition `C ⥤ Ind C ⥤ (Cᵒᵖ ⥤ Type v)` is just the Yoneda embedding. -/
noncomputable def Ind.yonedaCompInclusion : Ind.yoneda ⋙ Ind.inclusion C ≅ CategoryTheory.yoneda :=
  isoWhiskerLeft (FullSubcategory.lift _ _ _)
    (isoWhiskerRight (Ind.equivalence C).counitIso (fullSubcategoryInclusion _))

noncomputable instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    CreatesColimitsOfShape J (Ind.inclusion C) :=
  letI _ : CreatesColimitsOfShape J (fullSubcategoryInclusion (IsIndObject (C := C))) :=
    createsColimitsOfShapeFullSubcategoryInclusion (closedUnderColimitsOfShape_of_colimit
      (fun e => IsIndObject.map e.hom) (isIndObject_colimit _ _))
  inferInstanceAs <|
    CreatesColimitsOfShape J ((Ind.equivalence C).functor ⋙ fullSubcategoryInclusion _)

instance : HasFilteredColimits (Ind C) where
  HasColimitsOfShape _ _ _ :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Ind.inclusion C)

end CategoryTheory
