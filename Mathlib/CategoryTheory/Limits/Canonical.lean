/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Canonical colimits

Given a functor `F : C ⥤ D` and `Y : D`, we say that `Y` is a
canonical colimit relatively to `F` if `Y` identifies to the
colimit of all `F.obj X` for `X : C` and `f : F.obj X ⟶ Y`,
i.e. `Y` identifies to the colimit of the obvious functor
`CostructuredArrow F Y ⥤ D` (see definitions `canonicalCocone`
and `CanonicalColimit`). We introduce the corresponding property
`isCanonicalColimit F` of objects of `D`.

## TODO

* formalize dense subcategories
* show the presheaves of types are canonical colimits relatively
to the Yoneda embedding

## References
* https://ncatlab.org/nlab/show/dense+functor

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D)

namespace Limits

/-- Given a functor `F : C ⥤ D` and `Y : D`, this is the canonical cocone
with point `Y` for the functor
`CostructuredArrow.proj F Y ⋙ F : CostructuredArrow F Y ⥤ D`. -/
@[simps]
def canonicalCocone (Y : D) :
    Cocone (CostructuredArrow.proj F Y ⋙ F) where
  pt := Y
  ι := { app f := f.hom }

/-- An object `Y : D` is a canonical colimit relatively to `F : C ⥤ D`
when `canonicalCocone F Y` is colimit, i.e. `Y` identifies to the
colimit of all `F.obj X` for `X : C` and `f : F.obj X ⟶ Y`. -/
abbrev CanonicalColimit (Y : D) : Type _ := IsColimit (canonicalCocone F Y)

end Limits

/-- Given a functor `F : C ⥤ D`, this is the property that an object `Y : D`
is a canonical colimit relatively to `F`, i.e. `Y` identifies to the
colimit of all `F.obj X` for `X : C` and `f : F.obj X ⟶ Y`. -/
def Functor.isCanonicalColimit : ObjectProperty D :=
  fun Y ↦ Nonempty (CanonicalColimit F Y)

variable {F} in
lemma Functor.isCanonicalColimit.hom_ext
    {Y : D} (hY : F.isCanonicalColimit Y)
    {T : D} {f g : Y ⟶ T}
    (h : ∀ (X : C) (p : F.obj X ⟶ Y), p ≫ f = p ≫ g) : f = g :=
  hY.some.hom_ext (fun _ ↦ h _ _)

end CategoryTheory
