/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers

#align_import category_theory.limits.constructions.over.basic from "leanprover-community/mathlib"@"15db1b4f26ba89c6eb0c78b0a44c7e779a788e29"

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `Over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `Over B` has limits.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

/-- Make sure we can derive pullbacks in `Over B`. -/
instance {B : C} [HasPullbacks C] : HasPullbacks (Over B) := by
  letI : HasLimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingCospan)) C :=
    hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : Category (ULiftHom.{v} (ULift.{v} WalkingCospan)) := inferInstance
  exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

/-- Make sure we can derive equalizers in `Over B`. -/
instance {B : C} [HasEqualizers C] : HasEqualizers (Over B) := by
  letI : HasLimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingParallelPair)) C :=
    hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : Category (ULiftHom.{v} (ULift.{v} WalkingParallelPair)) := inferInstance
  exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

instance hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) := by
  apply @hasFiniteLimits_of_hasEqualizers_and_finite_products _ _ ?_ ?_
  · exact ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  · apply @hasEqualizers_of_hasPullbacks_and_binary_products _ _ ?_ _
    haveI : HasPullbacks C := ⟨inferInstance⟩
    exact ConstructProducts.over_binaryProduct_of_pullback
#align category_theory.over.has_finite_limits CategoryTheory.Over.hasFiniteLimits

instance hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w, w} (Over B) := by
  apply @has_limits_of_hasEqualizers_and_products _ _ ?_ ?_
  · exact ConstructProducts.over_products_of_widePullbacks
  · apply @hasEqualizers_of_hasPullbacks_and_binary_products _ _ ?_ _
    haveI : HasPullbacks C := ⟨inferInstance⟩
    exact ConstructProducts.over_binaryProduct_of_pullback
#align category_theory.over.has_limits CategoryTheory.Over.hasLimits

end CategoryTheory.Over
