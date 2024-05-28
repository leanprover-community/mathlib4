/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic

#align_import algebra.hom.equiv.units.group_with_zero from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

/-!
# Multiplication by a nonzero element in a `GroupWithZero` is a permutation.
-/

assert_not_exists DenselyOrdered

variable {G : Type*}

namespace Equiv

section GroupWithZero

variable [GroupWithZero G]

/-- Left multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! (config := .asFn)]
protected def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulLeft
#align equiv.mul_left₀ Equiv.mulLeft₀
#align equiv.mul_left₀_symm_apply Equiv.mulLeft₀_symm_apply
#align equiv.mul_left₀_apply Equiv.mulLeft₀_apply

theorem _root_.mulLeft_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective (a * · : G → G) :=
  (Equiv.mulLeft₀ a ha).bijective
#align mul_left_bijective₀ mulLeft_bijective₀

/-- Right multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! (config := .asFn)]
protected def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulRight
#align equiv.mul_right₀ Equiv.mulRight₀
#align equiv.mul_right₀_symm_apply Equiv.mulRight₀_symm_apply
#align equiv.mul_right₀_apply Equiv.mulRight₀_apply

theorem _root_.mulRight_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * a) : G → G) :=
  (Equiv.mulRight₀ a ha).bijective
#align mul_right_bijective₀ mulRight_bijective₀

end GroupWithZero

end Equiv
