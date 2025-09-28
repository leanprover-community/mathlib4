/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplication by a nonzero element in a `GroupWithZero` is a permutation.
-/

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace Equiv
section GroupWithZero
variable [GroupWithZero G₀]

/-- In a `GroupWithZero` `G₀`, the unit group `G₀ˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps] def _root_.unitsEquivNeZero : G₀ˣ ≃ {a : G₀ // a ≠ 0} where
  toFun a := ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop

/-- Left multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
protected def mulLeft₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ :=
  (Units.mk0 a ha).mulLeft

theorem _root_.mulLeft_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective (a * · : G₀ → G₀) :=
  (Equiv.mulLeft₀ a ha).bijective

/-- Right multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
protected def mulRight₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ :=
  (Units.mk0 a ha).mulRight

theorem _root_.mulRight_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective ((· * a) : G₀ → G₀) :=
  (Equiv.mulRight₀ a ha).bijective

/-- Right division by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! +simpRhs]
def divRight₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ where
  toFun := (· / a)
  invFun := (· * a)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero G₀]

/-- Left division by a nonzero element in a `CommGroupWithZero` is a permutation of the underlying
type. -/
@[simps! +simpRhs]
def divLeft₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ where
  toFun := (a / ·)
  invFun := (a / ·)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

end CommGroupWithZero
end Equiv
