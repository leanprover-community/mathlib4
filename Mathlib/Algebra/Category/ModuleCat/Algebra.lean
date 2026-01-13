/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Additional typeclass for modules over an algebra

For an object in `M : ModuleCat A`, where `A` is a `k`-algebra,
we provide additional typeclasses on the underlying type `M`,
namely `Module k M` and `IsScalarTower k A M`.
These are not made into instances by default.

We provide the `Linear k (ModuleCat A)` instance.

## Note

If you begin with a `[Module k M] [Module A M] [IsScalarTower k A M]`,
and build a bundled module via `ModuleCat.of A M`,
these instances will not necessarily agree with the original ones.

It seems without making a parallel version `ModuleCat' k A`, for modules over a `k`-algebra `A`,
that carries these typeclasses, this seems hard to achieve.
(An alternative would be to always require these typeclasses, and remove the original `ModuleCat`,
requiring users to write `ModuleCat' ℤ A` when `A` is merely a ring.)
-/

@[expose] public section


universe v u w

open CategoryTheory

namespace ModuleCat

variable {k : Type u} [Field k]
variable {A : Type w} [Ring A] [Algebra k A]

/-- Type synonym for considering a module over a `k`-algebra as a `k`-module. -/
def moduleOfAlgebraModule (M : ModuleCat.{v} A) : Module k M :=
  RestrictScalars.module k A M

attribute [scoped instance] ModuleCat.moduleOfAlgebraModule

theorem isScalarTower_of_algebra_moduleCat (M : ModuleCat.{v} A) : IsScalarTower k A M :=
  RestrictScalars.isScalarTower k A M

attribute [scoped instance] ModuleCat.isScalarTower_of_algebra_moduleCat

-- We verify that the morphism spaces become `k`-modules.
example (M N : ModuleCat.{v} A) : Module k (M ⟶ N) := inferInstance

instance linearOverField : Linear k (ModuleCat.{v} A) where
  homModule _ _ := inferInstance

end ModuleCat
