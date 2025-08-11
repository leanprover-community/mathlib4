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
instance {B : C} [HasPullbacks C] : HasPullbacks (Over B) := inferInstance

/-- Make sure we can derive equalizers in `Over B`. -/
instance {B : C} [HasEqualizers C] : HasEqualizers (Over B) := inferInstance

instance hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) := by
  have := ConstructProducts.over_finiteProducts_of_finiteWidePullbacks (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  apply hasFiniteLimits_of_hasEqualizers_and_finite_products

instance hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w, w} (Over B) := by
  have := ConstructProducts.over_binaryProduct_of_pullback (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  have := ConstructProducts.over_products_of_widePullbacks (B := B)
  apply has_limits_of_hasEqualizers_and_products

end CategoryTheory.Over
