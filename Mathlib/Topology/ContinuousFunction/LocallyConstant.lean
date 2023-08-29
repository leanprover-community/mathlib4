/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.ContinuousFunction.Algebra

#align_import topology.continuous_function.locally_constant from "leanprover-community/mathlib"@"f0339374016bccf700da0b2e0129d107c4346521"

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/


namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : LocallyConstant X Y)

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive (attr := simps)
"The inclusion of locally-constant functions into continuous functions as an additive monoid hom."]
def toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X Y →* C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    -- ⊢ ↑↑1 a✝ = ↑1 a✝
    simp
    -- 🎉 no goals
  map_mul' x y := by
    ext
    -- ⊢ ↑(OneHom.toFun { toFun := toContinuousMap, map_one' := (_ : ↑1 = 1) } (x * y …
    simp
    -- 🎉 no goals
#align locally_constant.to_continuous_map_monoid_hom LocallyConstant.toContinuousMapMonoidHom
#align locally_constant.to_continuous_map_add_monoid_hom LocallyConstant.toContinuousMapAddMonoidHom

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
def toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y) where
  toFun := (↑)
  map_add' x y := by
    ext
    -- ⊢ ↑↑(x + y) a✝ = ↑(↑x + ↑y) a✝
    simp
    -- 🎉 no goals
  map_smul' x y := by
    ext
    -- ⊢ ↑(AddHom.toFun { toFun := toContinuousMap, map_add' := (_ : ∀ (x y : Locally …
    simp
    -- 🎉 no goals
#align locally_constant.to_continuous_map_linear_map LocallyConstant.toContinuousMapLinearMap

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
def toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [TopologicalSemiring Y] : LocallyConstant X Y →ₐ[R] C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    -- ⊢ ↑↑1 a✝ = ↑1 a✝
    simp
    -- 🎉 no goals
  map_mul' x y := by
    ext
    -- ⊢ ↑(OneHom.toFun { toFun := toContinuousMap, map_one' := (_ : ↑1 = 1) } (x * y …
    simp
    -- 🎉 no goals
  map_zero' := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑{ toOneHom := { toFun := toContinuousMap, map_one' := (_ :  …
    simp
    -- 🎉 no goals
  map_add' x y := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑{ toOneHom := { toFun := toContinuousMap, map_one' := (_ :  …
    simp
    -- 🎉 no goals
  commutes' r := by
    ext x
    -- ⊢ ↑(OneHom.toFun (↑↑{ toMonoidHom := { toOneHom := { toFun := toContinuousMap, …
    simp [Algebra.smul_def]
    -- 🎉 no goals
#align locally_constant.to_continuous_map_alg_hom LocallyConstant.toContinuousMapAlgHom

end LocallyConstant
