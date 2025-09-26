/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Countable.Small
/-!
# Countable categories

A category is countable in this sense if it has countably many objects and countably many morphisms.

-/

universe w v u

noncomputable section

namespace CategoryTheory

instance discreteCountable {α : Type*} [Countable α] : Countable (Discrete α) :=
  Countable.of_equiv α discreteEquiv.symm

/-- A category with countably many objects and morphisms. -/
class CountableCategory (J : Type*) [Category J] : Prop where
  countableObj : Countable J := by infer_instance
  countableHom : ∀ j j' : J, Countable (j ⟶ j') := by infer_instance

attribute [instance] CountableCategory.countableObj CountableCategory.countableHom

instance countableCategoryDiscreteOfCountable (J : Type*) [Countable J] :
    CountableCategory (Discrete J) where

instance : CountableCategory ℕ where

namespace CountableCategory

variable (α : Type u) [Category.{v} α] [CountableCategory α]

/-- A countable category `α` is equivalent to a category with objects in `Type`. -/
abbrev ObjAsType : Type :=
  InducedCategory α (equivShrink.{0} α).symm

instance : Countable (ObjAsType α) := Countable.of_equiv α (equivShrink.{0} α)

instance {i j : ObjAsType α} : Countable (i ⟶ j) :=
  CountableCategory.countableHom ((equivShrink.{0} α).symm i) _

instance : CountableCategory (ObjAsType α) where

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

/-- A countable category `α` is equivalent to a *small* category with objects in `Type`. -/
def HomAsType := ShrinkHoms (ObjAsType α)

instance : LocallySmall.{0} (ObjAsType α) where
  hom_small _ _ := inferInstance

instance : SmallCategory (HomAsType α) := inferInstanceAs <| SmallCategory (ShrinkHoms _)

instance : Countable (HomAsType α) := Countable.of_equiv α (equivShrink.{0} α)

instance {i j : HomAsType α} : Countable (i ⟶ j) :=
  Countable.of_equiv ((ShrinkHoms.equivalence _).inverse.obj i ⟶
    (ShrinkHoms.equivalence _).inverse.obj j)
    (Functor.FullyFaithful.ofFullyFaithful _).homEquiv.symm

instance : CountableCategory (HomAsType α) where

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def homAsTypeEquiv : HomAsType α ≌ α :=
  (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)

end CountableCategory

instance (α : Type*) [Category α] [FinCategory α] : CountableCategory α where

open Opposite

/-- The opposite of a countable category is countable. -/
instance countableCategoryOpposite {J : Type*} [Category J] [CountableCategory J] :
    CountableCategory Jᵒᵖ where
  countableObj := Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm

attribute [local instance] uliftCategory in
/-- Applying `ULift` to morphisms and objects of a category preserves countability. -/
instance countableCategoryUlift {J : Type v} [Category J] [CountableCategory J] :
    CountableCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  countableObj := instCountableULift
  countableHom := fun i j =>
    have : Countable ((ULiftHom.objDown i).down ⟶ (ULiftHom.objDown j).down) := inferInstance
    instCountableULift

end CategoryTheory
