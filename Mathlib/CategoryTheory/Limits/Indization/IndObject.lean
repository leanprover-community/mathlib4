/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Ind-objects

For a presheaf `A : Cᵒᵖ ⥤ Type v` we define the type `IndObjectPresentation A` of presentations
of `A` as a small filtered colimit of representable presheaves and define the predicate
`IsIndObject A` asserting that there is at least one such presentation.

## Future work

A presheaf is an ind-object if and only if the category `CostructuredArrow yoneda A` is filtered
and finally small. In this way, `CostructuredArrow yoneda A` can be thought of the universal
indexing category for the representation of `A` as a small filtered colimit of representable
presheaves.

There are various useful ways to understand natural transformations between ind-objects in terms
of their presentations.

The ind-objects form a locally `v`-small category `IndCategory C` which has numerous interesting
properties.

## Implementation notes

One might be tempted to introduce another universe parameter and consider being a `w`-ind-object
as a property of presheaves `C ⥤ TypeMax.{v, w}`. This comes with significant technical hurdles.
The recommended alternative is to consider ind-objects over `ULiftHom.{w} C` instead.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The data that witnesses that a presheaf `A` is an ind-object. It consists of a small
    filtered indexing category `I`, a diagram `F : I ⥤ C` and the data for a colimit cocone on
    `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v` with cocone point `A`. -/
structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  /-- The indexing category of the filtered colimit presentation -/
  I : Type v
  /-- The indexing category of the filtered colimit presentation -/
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  /-- The diagram of the filtered colimit presentation -/
  F : I ⥤ C
  /-- Use `IndObjectPresentation.cocone` instead. -/
  ι : F ⋙ yoneda ⟶ (Functor.const I).obj A
  /-- Use `IndObjectPresenation.coconeIsColimit` instead. -/
  isColimit : IsColimit (Cocone.mk A ι)

namespace IndObjectPresentation

variable {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)

instance : SmallCategory P.I := P.ℐ
instance : IsFiltered P.I := P.hI

/-- The (colimit) cocone with cocone point `A`. -/
@[simps pt]
def cocone : Cocone (P.F ⋙ yoneda) where
  pt := A
  ι := P.ι

/-- `P.cocone` is a colimit cocone. -/
def coconeIsColimit : IsColimit P.cocone :=
  P.isColimit

/-- The canonical comparison functor between the indexing category of the presentation and the
    comma category `CostructuredArrow yoneda A`. This functor is always final. -/
@[simps! obj_left obj_right_as obj_hom map_left]
def toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A :=
  P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _

instance : P.toCostructuredArrow.Final :=
  final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

/-- Representable presheaves are (trivially) ind-objects. -/
@[simps]
def yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where
  I := Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun s => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun s m h => h ⟨PUnit.unit⟩ }

end IndObjectPresentation

/-- A presheaf is called an ind-object if it can be written as a filtered colimit of representable
    presheaves. -/
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)

theorem IsIndObject.mk {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsIndObject A :=
  ⟨⟨P⟩⟩

/-- Representable presheaves are (trivially) ind-objects. -/
theorem isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X) :=
  .mk <| IndObjectPresentation.yoneda X

end CategoryTheory.Limits
