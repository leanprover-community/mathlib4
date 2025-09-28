/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Objects that are colimits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictColimitsOfShape J`
and `P.colimitsOfShape J`. The former contains exactly the objects
of the form `colimit F` for any functor `F : J ⥤ C` that has
a colimit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `colimit F`.

Under certain circumstances, the type of objects satisfying
`P.strictColimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.colimitsOfShape J`
is essentially small.

## TODO

* refactor `ClosedUnderColimitsOfShape J P` to make it a typeclass which
would say that `P.colimitsOfShape J ≤ J`.
* refactor `ObjectProperty.ind` by saying that it is the supremum
of `P.colimitsOfShape J` for a filtered category `J`
(generalize also to `κ`-filtered categories?)
* dualize the results and formalize the closure of `P`
under finite limits (which require iterating over `ℕ`),
and more generally the closure under limits indexed by a category
whose type of arrows has a cardinality that is bounded by a
certain regular cardinal (@joelriou)

-/

universe w v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category C] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]

/-- The property of objects that are *equal* to `colimit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`. -/
inductive strictColimitsOfShape : ObjectProperty C
  | colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    strictColimitsOfShape (colimit F)

variable {P} in
lemma strictColimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictColimitsOfShape J ≤ Q.strictColimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩

/-- A structure expressing that `X : C` is the colimit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`. -/
structure ColimitOfShape (X : C) extends ColimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace ColimitOfShape

variable {P J}

/-- If `F : J ⥤ C` is a functor that has a colimit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `colimit F`
is indeed a colimit of objects satisfying `P`. -/
@[simps toColimitPresentation]
noncomputable def colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    P.ColimitOfShape J (colimit F) where
  toColimitPresentation := .colimit F
  prop_diag_obj := hF

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toColimitPresentation]
def ofIso {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.ColimitOfShape J Y where
  toColimitPresentation := .ofIso h.toColimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`,
it is also a colimit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toColimitPresentation]
def ofLE {X : C} (h : P.ColimitOfShape J X) {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    Q.ColimitOfShape J X where
  toColimitPresentation := h.toColimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

end ColimitOfShape

/-- The property of objects that are the point of a colimit cocone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`. -/
def colimitsOfShape : ObjectProperty C :=
  fun X ↦ Nonempty (P.ColimitOfShape J X)

variable {P J} in
lemma ColimitOfShape.colimitsOfShape {X : C} (h : P.ColimitOfShape J X) :
    P.colimitsOfShape J X :=
  ⟨h⟩

lemma strictColimitsOfShape_le_colimitsOfShape :
    P.strictColimitsOfShape J ≤ P.colimitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.colimit F hF⟩

instance : (P.colimitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
lemma isoClosure_strictColimitsOfShape :
    (P.strictColimitsOfShape J).isoClosure = P.colimitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictColimitsOfShape_le_colimitsOfShape
  · intro X ⟨h⟩
    have := h.hasColimit
    exact ⟨colimit h.diag, strictColimitsOfShape.colimit h.diag h.prop_diag_obj,
      ⟨h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

variable {P} in
lemma colimitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    P.colimitsOfShape J ≤ Q.colimitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
lemma colimitsOfShape_isoClosure :
    P.isoClosure.colimitsOfShape J = P.colimitsOfShape J := by
  refine le_antisymm ?_ (colimitsOfShape_monotone _ (P.le_isoClosure))
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toColimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j ↦ (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictColimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasColimit (F ⋙ P.ι) }) ↦
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j ↦ (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

end CategoryTheory.ObjectProperty
