/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Algebra.Basic

#align_import algebra.module.algebra from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Additional facts about modules over algebras.
-/

section RestrictScalars

variable (k : Type*) [CommSemiring k] (A : Type*) [Semiring A] [Algebra k A]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (N : Type*) [AddCommMonoid N] [Module k N] [Module A N] [IsScalarTower k A N]

namespace LinearMap

/-- Restriction of scalars for linear maps between modules over a `k`-algebra is itself `k`-linear.
-/
@[simps]
def restrictScalarsLinearMap : (M →ₗ[A] N) →ₗ[k] M →ₗ[k] N where
  toFun := LinearMap.restrictScalars k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.restrict_scalars_linear_map LinearMap.restrictScalarsLinearMap

end LinearMap

namespace Submodule

lemma restrictScalars_map (f : M →ₗ[A] N) (M' : Submodule A M) :
    restrictScalars k (map f M') =
      map (f.restrictScalars k) (restrictScalars k M') :=
  toAddSubmonoid_injective <| by
    simp only [map_toAddSubmonoid, toAddSubmonoid_restrictScalars]
    rfl

end Submodule

end RestrictScalars
