/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Objects that are limits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictLimitsOfShape J`
and `P.limitsOfShape J`. The former contains exactly the objects
of the form `limit F` for any functor `F : J ⥤ C` that has
a limit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `limit F`.

Under certain circumstances, the type of objects satisfying
`P.strictLimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.limitsOfShape J`
is essentially small.

-/

universe w v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category C] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]

/-- The property of objects that are *equal* to `limit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`. -/
inductive strictLimitsOfShape : ObjectProperty C
  | limit (F : J ⥤ C) [HasLimit F] (hF : ∀ j, P (F.obj j)) :
    strictLimitsOfShape (limit F)

variable {P} in
lemma strictLimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictLimitsOfShape J ≤ Q.strictLimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩

/-- A structure expressing that `X : C` is the limit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`. -/
structure LimitOfShape (X : C) extends LimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace LimitOfShape

variable {P J}

/-- If `F : J ⥤ C` is a functor that has a limit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `limit F`
is indeed a limit of objects satisfying `P`. -/
noncomputable def limit (F : J ⥤ C) [HasLimit F] (hF : ∀ j, P (F.obj j)) :
    P.LimitOfShape J (limit F) where
  toLimitPresentation := .limit F
  prop_diag_obj := hF

/-- If `X` is a limit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toLimitPresentation]
def ofIso {X : C} (h : P.LimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.LimitOfShape J Y where
  toLimitPresentation := .ofIso h.toLimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a limit indexed by `J` of objects satisfying a property `P`,
it is also a limit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toLimitPresentation]
def ofLE {X : C} (h : P.LimitOfShape J X) {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    Q.LimitOfShape J X where
  toLimitPresentation := h.toLimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

end LimitOfShape

/-- The property of objects that are the point of a limit cone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`. -/
def limitsOfShape : ObjectProperty C :=
  fun X ↦ Nonempty (P.LimitOfShape J X)

variable {P J} in
lemma LimitOfShape.limitsOfShape {X : C} (h : P.LimitOfShape J X) :
    P.limitsOfShape J X :=
  ⟨h⟩

lemma strictLimitsOfShape_le_limitsOfShape :
    P.strictLimitsOfShape J ≤ P.limitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.limit F hF⟩

instance : (P.limitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
lemma isoClosure_strictLimitsOfShape :
    (P.strictLimitsOfShape J).isoClosure = P.limitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictLimitsOfShape_le_limitsOfShape
  · intro X ⟨h⟩
    have := h.hasLimit
    exact ⟨limit h.diag, strictLimitsOfShape.limit h.diag h.prop_diag_obj,
      ⟨h.isLimit.conePointUniqueUpToIso (limit.isLimit _)⟩⟩

variable {P} in
lemma limitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    P.limitsOfShape J ≤ Q.limitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
lemma limitsOfShape_isoClosure :
    P.isoClosure.limitsOfShape J = P.limitsOfShape J := by
  refine le_antisymm ?_ (limitsOfShape_monotone _ P.le_isoClosure)
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toLimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j ↦ (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictLimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasLimit (F ⋙ P.ι) }) ↦
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j ↦ (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

end CategoryTheory.ObjectProperty
