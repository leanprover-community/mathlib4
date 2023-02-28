/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.category.pairwise
! leanprover-community/mathlib commit d82b87871d9a274884dff5263fa4f5d93bcce1d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Limits.IsLimit

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(opens X)ᵒᵖ`),
we produce a functor `pairwise ι ⥤ α` in the obvious way,
and show that `supr U` provides a colimit cocone over this functor.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

/-- An inductive type representing either a single term of a type `ι`, or a pair of terms.
We use this as the objects of a category to describe the sheaf condition.
-/
inductive Pairwise (ι : Type v)
  | single : ι → Pairwise
  | pair : ι → ι → Pairwise
#align category_theory.pairwise CategoryTheory.Pairwise

variable {ι : Type v}

namespace Pairwise

instance pairwiseInhabited [Inhabited ι] : Inhabited (Pairwise ι) :=
  ⟨single default⟩
#align category_theory.pairwise.pairwise_inhabited CategoryTheory.Pairwise.pairwiseInhabited

/-- Morphisms in the category `pairwise ι`. The only non-identity morphisms are
`left i j : single i ⟶ pair i j` and `right i j : single j ⟶ pair i j`.
-/
inductive Hom : Pairwise ι → Pairwise ι → Type v
  | id_single : ∀ i, hom (single i) (single i)
  | id_pair : ∀ i j, hom (pair i j) (pair i j)
  | left : ∀ i j, hom (pair i j) (single i)
  | right : ∀ i j, hom (pair i j) (single j)
#align category_theory.pairwise.hom CategoryTheory.Pairwise.Hom

open Hom

instance homInhabited [Inhabited ι] : Inhabited (Hom (single (default : ι)) (single default)) :=
  ⟨id_single default⟩
#align category_theory.pairwise.hom_inhabited CategoryTheory.Pairwise.homInhabited

/-- The identity morphism in `pairwise ι`.
-/
def id : ∀ o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j
#align category_theory.pairwise.id CategoryTheory.Pairwise.id

/-- Composition of morphisms in `pairwise ι`. -/
def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (f : Hom o₁ o₂) (g : Hom o₂ o₃), Hom o₁ o₃
  | _, _, _, id_single i, g => g
  | _, _, _, id_pair i j, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j
#align category_theory.pairwise.comp CategoryTheory.Pairwise.comp

section

attribute [local tidy] tactic.case_bash

instance : Category (Pairwise ι) where
  Hom := Hom
  id := id
  comp X Y Z f g := comp f g

end

variable {α : Type v} (U : ι → α)

section

variable [SemilatticeInf α]

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagramObj : Pairwise ι → α
  | single i => U i
  | pair i j => U i ⊓ U j
#align category_theory.pairwise.diagram_obj CategoryTheory.Pairwise.diagramObj

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagramMap : ∀ {o₁ o₂ : Pairwise ι} (f : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂
  | _, _, id_single i => 𝟙 _
  | _, _, id_pair i j => 𝟙 _
  | _, _, left i j => homOfLE inf_le_left
  | _, _, right i j => homOfLE inf_le_right
#align category_theory.pairwise.diagram_map CategoryTheory.Pairwise.diagramMap

/-- Given a function `U : ι → α` for `[semilattice_inf α]`, we obtain a functor `pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
@[simps]
def diagram : Pairwise ι ⥤ α where
  obj := diagramObj U
  map X Y f := diagramMap U f
#align category_theory.pairwise.diagram CategoryTheory.Pairwise.diagram

end

section

-- `complete_lattice` is not really needed, as we only ever use `inf`,
-- but the appropriate structure has not been defined.
variable [CompleteLattice α]

/-- Auxiliary definition for `cocone`. -/
def coconeιApp : ∀ o : Pairwise ι, diagramObj U o ⟶ supᵢ U
  | single i => homOfLE (le_supᵢ U i)
  | pair i j => homOfLE inf_le_left ≫ homOfLE (le_supᵢ U i)
#align category_theory.pairwise.cocone_ι_app CategoryTheory.Pairwise.coconeιApp

/-- Given a function `U : ι → α` for `[complete_lattice α]`,
`supr U` provides a cocone over `diagram U`.
-/
@[simps]
def cocone : Cocone (diagram U) where
  x := supᵢ U
  ι := { app := coconeιApp U }
#align category_theory.pairwise.cocone CategoryTheory.Pairwise.cocone

/-- Given a function `U : ι → α` for `[complete_lattice α]`,
`infi U` provides a limit cone over `diagram U`.
-/
def coconeIsColimit : IsColimit (cocone U)
    where desc s :=
    homOfLE
      (by
        apply CompleteLattice.sup_le
        rintro _ ⟨j, rfl⟩
        exact (s.ι.app (single j)).le)
#align category_theory.pairwise.cocone_is_colimit CategoryTheory.Pairwise.coconeIsColimit

end

end Pairwise

end CategoryTheory

