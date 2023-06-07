/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.algebra
! leanprover-community/mathlib commit 1c775cc661988d96c477aa4ca6f7b5641a2a924b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.Module.Basic

/-!
# Additional typeclass for modules over an algebra

For an object in `M : Module A`, where `A` is a `k`-algebra,
we provide additional typeclasses on the underlying type `M`,
namely `module k M` and `is_scalar_tower k A M`.
These are not made into instances by default.

We provide the `linear k (Module A)` instance.

## Note

If you begin with a `[module k M] [module A M] [is_scalar_tower k A M]`,
and build a bundled module via `Module.of A M`,
these instances will not necessarily agree with the original ones.

It seems without making a parallel version `Module' k A`, for modules over a `k`-algebra `A`,
that carries these typeclasses, this seems hard to achieve.
(An alternative would be to always require these typeclasses, and remove the original `Module`,
requiring users to write `Module' ℤ A` when `A` is merely a ring.)
-/


universe v u w

open CategoryTheory

namespace ModuleCat

variable {k : Type u} [Field k]

variable {A : Type w} [Ring A] [Algebra k A]

/-- Type synonym for considering a module over a `k`-algebra as a `k`-module.
-/
def moduleOfAlgebraModule (M : ModuleCat.{v} A) : Module k M :=
  RestrictScalars.module k A M
#align Module.module_of_algebra_Module ModuleCat.moduleOfAlgebraModule

attribute [scoped instance] ModuleCat.moduleOfAlgebraModule

theorem isScalarTower_of_algebra_moduleCat (M : ModuleCat.{v} A) : IsScalarTower k A M :=
  RestrictScalars.isScalarTower k A M
#align Module.is_scalar_tower_of_algebra_Module ModuleCat.isScalarTower_of_algebra_moduleCat

attribute [scoped instance] ModuleCat.isScalarTower_of_algebra_moduleCat

-- We verify that the morphism spaces become `k`-modules.
example (M N : ModuleCat.{v} A) : Module k (M ⟶ N) := by infer_instance

instance linearOverField : Linear k (ModuleCat.{v} A) where homModule M N := by infer_instance
#align Module.linear_over_field ModuleCat.linearOverField

end ModuleCat

