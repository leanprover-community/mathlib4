/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `Pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(Opens X)ᵒᵖ`),
we produce a functor `Pairwise ι ⥤ α` in the obvious way,
and show that `iSup U` provides a colimit cocone over this functor.
-/

@[expose] public section


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
  deriving Fintype, DecidableEq

variable {ι : Type v}

namespace Pairwise

instance pairwiseInhabited [Inhabited ι] : Inhabited (Pairwise ι) :=
  ⟨single default⟩

/-- Morphisms in the category `Pairwise ι`. The only non-identity morphisms are
`left i j : pair i j ⟶ single i` and `right i j : pair i j ⟶ single j`.
-/
inductive Hom : Pairwise ι → Pairwise ι → Type v
  | id_single : ∀ i, Hom (single i) (single i)
  | id_pair : ∀ i j, Hom (pair i j) (pair i j)
  | left : ∀ i j, Hom (pair i j) (single i)
  | right : ∀ i j, Hom (pair i j) (single j)
  deriving DecidableEq

-- False positive?
attribute [nolint unusedArguments] instDecidableEqHom.decEq

open Hom

instance homInhabited [Inhabited ι] : Inhabited (Hom (single (default : ι)) (single default)) :=
  ⟨id_single default⟩

/-- The identity morphism in `Pairwise ι`.
-/
def id : ∀ o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j

/-- Composition of morphisms in `Pairwise ι`. -/
def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
  | _, _, _, id_single _, g => g
  | _, _, _, id_pair _ _, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j

instance : CategoryStruct (Pairwise ι) where
  Hom := Hom
  id := id
  comp := @comp _

section

open Lean Elab Tactic in
/-- A helper tactic for `cat_disch` and `Pairwise`. -/
meta def pairwiseCases : TacticM Unit := do
  evalTactic (← `(tactic| casesm* (_ : Pairwise _) ⟶ (_ : Pairwise _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] pairwiseCases in
instance : Category (Pairwise ι) where

end

instance {i j : Pairwise ι} [DecidableEq ι] : DecidableEq (i ⟶ j) :=
  inferInstanceAs (DecidableEq (Pairwise.Hom i j))

instance [Fintype ι] [DecidableEq ι] : FinCategory (Pairwise ι) where
  fintypeHom
  | .single i, .single j => ⟨if h : i = j then {eqToHom (h ▸ rfl)} else ∅, by rintro ⟨⟩; cat_disch⟩
  | .single i, .pair j k => ⟨∅, by rintro ⟨⟩⟩
  | .pair i j, .single k =>
    ⟨(if h : i = k then {Hom.left i j ≫ eqToHom (h ▸ rfl)} else ∅) ∪
      (if h : j = k then {Hom.right i j ≫ eqToHom (h ▸ rfl)} else ∅),
        by rintro ⟨⟩ <;> cat_disch⟩
  | .pair i j, .pair k l =>
    ⟨if h : i = k ∧ j = l then {eqToHom (h.1 ▸ h.2 ▸ rfl)} else ∅, by rintro ⟨⟩; cat_disch⟩

variable {α : Type u} (U : ι → α)

section

variable [SemilatticeInf α]

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagramObj : Pairwise ι → α
  | single i => U i
  | pair i j => U i ⊓ U j

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagramMap : ∀ {o₁ o₂ : Pairwise ι} (_ : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => homOfLE inf_le_left
  | _, _, right _ _ => homOfLE inf_le_right

/-- Given a function `U : ι → α` for `[SemilatticeInf α]`, we obtain a functor `Pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
@[simps]
def diagram : Pairwise ι ⥤ α where
  obj := diagramObj U
  map := diagramMap U

end

section

-- `CompleteLattice` is not really needed, as we only ever use `inf`,
-- but the appropriate structure has not been defined.
variable [CompleteLattice α]

/-- Auxiliary definition for `cocone`. -/
def coconeιApp : ∀ o : Pairwise ι, diagramObj U o ⟶ iSup U
  | single i => homOfLE (le_iSup U i)
  | pair i _ => homOfLE inf_le_left ≫ homOfLE (le_iSup U i)

/-- Given a function `U : ι → α` for `[CompleteLattice α]`,
`iSup U` provides a cocone over `diagram U`.
-/
@[simps]
def cocone : Cocone (diagram U) where
  pt := iSup U
  ι := { app := coconeιApp U }

/-- Given a function `U : ι → α` for `[CompleteLattice α]`,
`iSup U` provides a colimit cocone over `diagram U`.
-/
def coconeIsColimit : IsColimit (cocone U) where
  desc s := homOfLE
    (by
      apply sSup_le
      rintro _ ⟨j, rfl⟩
      exact (s.ι.app (single j)).le)

end

end Pairwise

end CategoryTheory
