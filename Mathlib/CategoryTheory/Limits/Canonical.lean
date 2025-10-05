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
canonical colimit relatively to `F` is `Y` identifies to the
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

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C']
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

variable {F} in
lemma CanonicalColimit.hom_ext'
    {Y : D} (hY : CanonicalColimit F Y) {T : D} {f g : Y ⟶ T}
    (h : ∀ (X : C) (p : F.obj X ⟶ Y), p ≫ f = p ≫ g) : f = g :=
  hY.hom_ext (fun _ ↦ h _ _)

variable {F} in
/-- If `Y` is a canonical colimit relatively to `F : C ⥤ D`, and `G : C ⥤ D`
is isomorphic to `F`, then `Y` is also a canonical colimit relatively to `G`. -/
def CanonicalColimit.ofNatIso {Y : D} (h : CanonicalColimit F Y) {G : C ⥤ D} (e : F ≅ G) :
    CanonicalColimit G Y := by
  refine (IsColimit.equivOfNatIsoOfIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _ ?_).1
    (h.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))
  exact Cocones.ext (Iso.refl _)

variable {F} in
noncomputable def CanonicalColimit.ofEquivalence
    {X : D} (h : CanonicalColimit F X) (e : C' ≌ C) :
    CanonicalColimit (e.functor ⋙ F) X :=
  h.whiskerEquivalence (CostructuredArrow.pre e.functor F X).asEquivalence

end Limits

/-- Given a functor `F : C ⥤ D`, this is the property that an object `Y : D`
is a canonical colimit relatively to `F`, i.e. `Y` identifies to the
colimit of all `F.obj X` for `X : C` and `f : F.obj X ⟶ Y`. -/
def Functor.isCanonicalColimit : ObjectProperty D :=
  fun Y ↦ Nonempty (CanonicalColimit F Y)

variable {F} in
/-- When `Y : D` is a canonical colimit relatively to `F`,
this is a choice of structure `CanonicalColimit F Y`. -/
noncomputable def Functor.isCanonicalColimit.canonicalColimit
    {Y : D} (hY : F.isCanonicalColimit Y) :
    CanonicalColimit F Y := hY.some

variable {F} in
lemma Functor.congr_isCanonicalColimit {G : C ⥤ D} (e : F ≅ G) :
    F.isCanonicalColimit = G.isCanonicalColimit := by
  ext Y
  exact ⟨fun ⟨h⟩ ↦ ⟨h.ofNatIso e⟩, fun ⟨h⟩ ↦ ⟨h.ofNatIso e.symm⟩⟩

end CategoryTheory
