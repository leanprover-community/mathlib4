/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Order.CompleteLattice
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

#align_import category_theory.category.pairwise from "leanprover-community/mathlib"@"d82b87871d9a274884dff5263fa4f5d93bcce1d6"

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `Pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(opens X)ᵒᵖ`),
we produce a functor `Pairwise ι ⥤ α` in the obvious way,
and show that `iSup U` provides a colimit cocone over this functor.
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
  | single : ι → Pairwise ι
  | pair : ι → ι → Pairwise ι
#align category_theory.pairwise CategoryTheory.Pairwise

variable {ι : Type v}

namespace Pairwise

instance pairwiseInhabited [Inhabited ι] : Inhabited (Pairwise ι) :=
  ⟨single default⟩
#align category_theory.pairwise.pairwise_inhabited CategoryTheory.Pairwise.pairwiseInhabited

/-- Morphisms in the category `Pairwise ι`. The only non-identity morphisms are
`left i j : single i ⟶ pair i j` and `right i j : single j ⟶ pair i j`.
-/
inductive Hom : Pairwise ι → Pairwise ι → Type v
  | id_single : ∀ i, Hom (single i) (single i)
  | id_pair : ∀ i j, Hom (pair i j) (pair i j)
  | left : ∀ i j, Hom (pair i j) (single i)
  | right : ∀ i j, Hom (pair i j) (single j)
#align category_theory.pairwise.hom CategoryTheory.Pairwise.Hom

open Hom

instance homInhabited [Inhabited ι] : Inhabited (Hom (single (default : ι)) (single default)) :=
  ⟨id_single default⟩
#align category_theory.pairwise.hom_inhabited CategoryTheory.Pairwise.homInhabited

/-- The identity morphism in `Pairwise ι`.
-/
def id : ∀ o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j
#align category_theory.pairwise.id CategoryTheory.Pairwise.id

/-- Composition of morphisms in `Pairwise ι`. -/
def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
  | _, _, _, id_single _, g => g
  | _, _, _, id_pair _ _, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j
#align category_theory.pairwise.comp CategoryTheory.Pairwise.comp

section

open Lean Elab Tactic in
/-- A helper tactic for `aesop_cat` and `Pairwise`. -/
def pairwiseCases : TacticM Unit := do
  evalTactic (← `(tactic| casesm* (_ : Pairwise _) ⟶ (_ : Pairwise _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] pairwiseCases in
instance : Category (Pairwise ι) where
  Hom := Hom
  id := id
  comp f g := comp f g

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
def diagramMap : ∀ {o₁ o₂ : Pairwise ι} (_ : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => homOfLE inf_le_left
  | _, _, right _ _ => homOfLE inf_le_right
#align category_theory.pairwise.diagram_map CategoryTheory.Pairwise.diagramMap

-- Porting note: the fields map_id and map_comp were filled by hand, as generating them by `aesop`
-- causes a PANIC.
/-- Given a function `U : ι → α` for `[SemilatticeInf α]`, we obtain a functor `Pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
-- Porting note: We want `@[simps]` here, but this causes a PANIC in the linter.
-- (Which, worryingly, does not cause a linter failure!)
-- @[simps]
def diagram : Pairwise ι ⥤ α where
  obj := diagramObj U
  map := diagramMap U
#align category_theory.pairwise.diagram CategoryTheory.Pairwise.diagram

end

section

-- `CompleteLattice` is not really needed, as we only ever use `inf`,
-- but the appropriate structure has not been defined.
variable [CompleteLattice α]

/-- Auxiliary definition for `cocone`. -/
def coconeιApp : ∀ o : Pairwise ι, diagramObj U o ⟶ iSup U
  | single i => homOfLE (le_iSup U i)
  | pair i _ => homOfLE inf_le_left ≫ homOfLE (le_iSup U i)
#align category_theory.pairwise.cocone_ι_app CategoryTheory.Pairwise.coconeιApp

/-- Given a function `U : ι → α` for `[CompleteLattice α]`,
`iSup U` provides a cocone over `diagram U`.
-/
@[simps]
def cocone : Cocone (diagram U) where
  pt := iSup U
  ι := { app := coconeιApp U }
#align category_theory.pairwise.cocone CategoryTheory.Pairwise.cocone

/-- Given a function `U : ι → α` for `[CompleteLattice α]`,
`iInf U` provides a limit cone over `diagram U`.
-/
def coconeIsColimit : IsColimit (cocone U) where
  desc s := homOfLE
    (by
      apply CompleteSemilatticeSup.sSup_le
      rintro _ ⟨j, rfl⟩
      exact (s.ι.app (single j)).le)
#align category_theory.pairwise.cocone_is_colimit CategoryTheory.Pairwise.coconeIsColimit

end

end Pairwise

end CategoryTheory
