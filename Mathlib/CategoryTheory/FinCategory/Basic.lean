/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Category.ULift

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation
Prior to https://github.com/leanprover-community/mathlib4/pull/14046, `FinCategory` required a `DecidableEq` instance on the object and morphism types.
This does not seem to have had any practical payoff (i.e. making some definition constructive)
so we have removed these requirements to avoid
having to supply instances or delay with non-defeq conflicts between instances.
-/


universe w v u

noncomputable section

namespace CategoryTheory

instance discreteFintype {α : Type*} [Fintype α] : Fintype (Discrete α) :=
  Fintype.ofEquiv α discreteEquiv.symm

instance discreteHomFintype {α : Type*} (X Y : Discrete α) : Fintype (X ⟶ Y) := by
  classical
  apply ULift.fintype

/-- A category with a `Fintype` of objects, and a `Fintype` for each morphism space. -/
class FinCategory (J : Type v) [SmallCategory J] where
  fintypeObj : Fintype J := by infer_instance
  fintypeHom : ∀ j j' : J, Fintype (j ⟶ j') := by infer_instance

attribute [instance] FinCategory.fintypeObj FinCategory.fintypeHom

instance finCategoryDiscreteOfFintype (J : Type v) [Fintype J] : FinCategory (Discrete J) where

open Opposite

/-- The opposite of a finite category is finite.
-/
instance finCategoryOpposite {J : Type v} [SmallCategory J] [FinCategory J] : FinCategory Jᵒᵖ where
  fintypeObj := Fintype.ofEquiv _ equivToOpposite
  fintypeHom j j' := Fintype.ofEquiv _ (opEquiv j j').symm

/-- Applying `ULift` to morphisms and objects of a category preserves finiteness. -/
instance finCategoryUlift {J : Type v} [SmallCategory J] [FinCategory J] :
    FinCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  fintypeObj := ULift.fintype J
  fintypeHom := fun _ _ => ULift.fintype _

end CategoryTheory
