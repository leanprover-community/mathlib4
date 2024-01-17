/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.WithOne.Defs

#align_import algebra.group.with_one.units from "leanprover-community/mathlib"@"4e87c8477c6c38b753f050bc9664b94ee859896c"

/-!
# Isomorphism between a group and the units of itself adjoined with `0`

## Notes
This is here to keep `Algebra.GroupWithZero.Units.Basic` out of the import requirements of
`Algebra.Order.Field.Defs`.
-/


namespace WithZero

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def unitsWithZeroEquiv {α : Type*} [Group α] : (WithZero α)ˣ ≃* α where
  toFun a := unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simp only [coe_unzero, Units.mk0_val]
  right_inv _ := rfl
  map_mul' _ _ := coe_inj.mp <| by simp only [Units.val_mul, coe_unzero, coe_mul]
#align with_zero.units_with_zero_equiv WithZero.unitsWithZeroEquiv

end WithZero
