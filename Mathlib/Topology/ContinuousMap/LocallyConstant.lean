/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/


namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive (attr := simps)
"The inclusion of locally-constant functions into continuous functions as an additive monoid hom."]
def toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X Y →* C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
def toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y) where
  toFun := (↑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
def toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [IsTopologicalSemiring Y] : LocallyConstant X Y →ₐ[R] C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  commutes' r := by
    ext x
    simp [Algebra.smul_def]

end LocallyConstant
