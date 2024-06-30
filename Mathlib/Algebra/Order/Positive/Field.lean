/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Positive.Ring

#align_import algebra.order.positive.field from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# Algebraic structures on the set of positive numbers

In this file we prove that the set of positive elements of a linear ordered field is a linear
ordered commutative group.
-/


variable {K : Type*} [Field K] [LinearOrderedField K]

namespace Positive

instance Subtype.inv : Inv { x : K // 0 < x } :=
  ⟨fun x => ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp]
theorem coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = (x⁻¹ : K) :=
  rfl
#align positive.coe_inv Positive.coe_inv

instance : Pow { x : K // 0 < x } ℤ :=
  ⟨fun x n => ⟨(x: K) ^ n, zpow_pos_of_pos x.2 _⟩⟩

@[simp]
theorem coe_zpow (x : { x : K // 0 < x }) (n : ℤ) : ↑(x ^ n) = (x : K) ^ n :=
  rfl
#align positive.coe_zpow Positive.coe_zpow

/-- sorry -/
local instance : CommGroup { x : K // 0 < x } where
  toInv := Positive.Subtype.inv
  __ := Subtype.coe_injective.commMonoid (Subtype.val) (by exact val_one) val_mul val_pow
  mul_left_inv := fun a => Subtype.ext <| inv_mul_cancel a.2.ne'

instance : LinearOrderedCommGroup { x : K // 0 < x } :=
  { Positive.linearOrderedCancelCommMonoid with }

end Positive
