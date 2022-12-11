/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathbin.Algebra.Group.WithOne.Basic
import Mathbin.Algebra.GroupWithZero.Units.Basic

/-!
# Isomorphism between a group and the units of itself adjoined with `0`

## Notes
This is here to keep `algebra.group_with_zero.units.basic` out of the import requirements of
`algebra.order.field.defs`.
-/


namespace WithZero

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def unitsWithZeroEquiv {α : Type _} [Group α] :
    (WithZero α)ˣ ≃* α where 
  toFun a := unzero a.NeZero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simpa only [coe_unzero]
  right_inv _ := rfl
  map_mul' _ _ := coe_inj.mp <| by simpa only [coe_unzero, coe_mul]
#align with_zero.units_with_zero_equiv WithZero.unitsWithZeroEquiv

end WithZero

