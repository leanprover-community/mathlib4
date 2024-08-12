/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Multiplicative actions with zero on and by `Mˣ`

This file provides the multiplicative actions with zero of a unit on a type `α`, `SMul Mˣ α`, in the
presence of `SMulWithZero M α`, with the obvious definition stated in `Units.smul_def`.

Additionally, a `MulDistribMulAction G M` for some group `G` satisfying some additional properties
admits a `MulDistribMulAction G Mˣ` structure, again with the obvious definition stated in
`Units.coe_smul`. This instance uses a primed name.

## See also

* `Algebra.GroupWithZero.Action.Opposite`
* `Algebra.GroupWithZero.Action.Pi`
* `Algebra.GroupWithZero.Action.Prod`
-/

variable {G M α : Type*}

namespace Units

/-! ### Action of the units of `M` on a type `α` -/

@[to_additive]
instance [Monoid M] [SMul M α] : SMul Mˣ α where smul m a := (m : M) • a

instance instSMulZeroClass [Monoid M] [Zero α] [SMulZeroClass M α] : SMulZeroClass Mˣ α where
  smul := (· • ·)
  smul_zero m := smul_zero (m : M)

instance instDistribSMulUnits [Monoid M] [AddZeroClass α] [DistribSMul M α] :
    DistribSMul Mˣ α where smul_add m := smul_add (m : M)

instance instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    DistribMulAction Mˣ α where
  __ := instDistribSMulUnits
  one_smul := fun b => one_smul M b
  mul_smul := fun x y b => mul_smul (x : M) y b

instance instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction Mˣ α where
  smul_mul m := smul_mul' (m : M)
  smul_one m := smul_one (m : M)

/-! ### Action of a group `G` on units of `M` -/

/-- A stronger form of `Units.mul_action'`. -/
instance mulDistribMulAction' [Group G] [Monoid M] [MulDistribMulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulDistribMulAction G Mˣ :=
  { Units.mulAction' with
    smul := (· • ·),
    smul_one := fun _ => Units.ext <| smul_one _,
    smul_mul := fun _ _ _ => Units.ext <| smul_mul' _ _ _ }

end Units
