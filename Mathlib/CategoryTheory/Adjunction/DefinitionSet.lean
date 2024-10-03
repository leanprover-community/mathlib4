/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Set.Lattice

/-!
# Set of definition of a candidate adjoint

Given a functor `F : D ⥤ C`, we define a functor
`partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D` which is
defined on the full subcategory of `C` consisting of those objects `X : C`
such that `F ⋙ coyoneda.obj (op X) : D ⥤ Type _` is corepresentable.
We have a natural bijection
`(F.partialLeftAdjoint.obj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
that is similar to what we would expect for the left adjoint of `F`.

Indeed, if the predicate `F.LeftAdjointObjIsDefined` which defines `F.PartialLeftAdjointSource`
holds for all objects `X : C`, then `F` has a left adjoint.

When colimits indexed by a category `J` exist in `D`, we show that
the predicate `F.LeftAdjointObjIsDefined` is stable under colimits indexed by `J`.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)

def LeftAdjointObjIsDefined (X : C) : Prop := IsCorepresentable (F ⋙ coyoneda.obj (op X))

lemma LeftAdjointObjIsDefined_iff (X : C) :
    F.LeftAdjointObjIsDefined X ↔ IsCorepresentable (F ⋙ coyoneda.obj (op X)) := by rfl

abbrev PartialLeftAdjointSource := FullSubcategory F.LeftAdjointObjIsDefined

instance (X : F.PartialLeftAdjointSource) :
    IsCorepresentable (F ⋙ coyoneda.obj (op X.obj)) := X.property

noncomputable def partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D :=
  (F ⋙ coyoneda.obj (op X.obj)).coreprX

noncomputable def partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} :
    (F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y) :=
  (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv

lemma partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv (f ≫ g) =
      F.partialLeftAdjointHomEquiv f ≫ F.map g := by
  apply CorepresentableBy.homEquiv_comp

noncomputable def partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) : F.partialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y :=
    F.partialLeftAdjointHomEquiv.symm (f ≫ F.partialLeftAdjointHomEquiv (𝟙 _))

@[simp]
lemma partialLeftAdjointHomEquiv_partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f) =
      by exact f ≫ F.partialLeftAdjointHomEquiv (𝟙 _) := by
  simp [partialLeftAdjointMap]

@[simps]
noncomputable def partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D where
  obj := F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    dsimp
    rw [partialLeftAdjointHomEquiv_partialLeftAdjointMap]
    erw [id_comp]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    dsimp
    rw [partialLeftAdjointHomEquiv_partialLeftAdjointMap, partialLeftAdjointHomEquiv_comp,
      partialLeftAdjointHomEquiv_partialLeftAdjointMap, assoc]
    erw [assoc]
    rw [← F.partialLeftAdjointHomEquiv_comp, id_comp,
      partialLeftAdjointHomEquiv_partialLeftAdjointMap]

variable {F}

lemma isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (h : F.LeftAdjointObjIsDefined = ⊤) : F.IsRightAdjoint := by
  replace h : ∀ X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X ↦ by
    simp only [← LeftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y ↦ (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f ↦ by apply CorepresentableBy.homEquiv_comp)).isRightAdjoint

def corepresentableByCompCoyonedaObjOfIsColimit {J : Type*} [Category J]
    {R : J ⥤ F.PartialLeftAdjointSource}
    {c : Cocone (R ⋙ fullSubcategoryInclusion _)} (hc : IsColimit c)
    {c' : Cocone (R ⋙ F.partialLeftAdjoint)} (hc' : IsColimit c') :
    (F ⋙ coyoneda.obj (op c.pt)).CorepresentableBy c'.pt :=
  sorry

lemma leftAdjointObjIsDefined_of_isColimit {J : Type*} [Category J] {R : J ⥤ C} {c : Cocone R}
    (hc : IsColimit c) [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.LeftAdjointObjIsDefined (R.obj j)) :
    F.LeftAdjointObjIsDefined c.pt :=
  (corepresentableByCompCoyonedaObjOfIsColimit
    (R := FullSubcategory.lift _ R h) hc (colimit.isColimit _)).isCorepresentable

lemma leftAdjointObjIsDefined_colimit {J : Type*} [Category J] (R : J ⥤ C)
    [HasColimit R] [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.LeftAdjointObjIsDefined (R.obj j)) :
    F.LeftAdjointObjIsDefined (colimit R) :=
  leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h

end Functor

end CategoryTheory
