/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
/-!
# OrderIso between Two-sided ideals of a non-unital non-assoc ring and its opposite

This file constructs an order isomorphism between the two-sided ideals of a non-unital non-assoc
ring and that of its opposite ring.

## Main results
* `TwoSidedIdeal.toMopOrderIso`: The order isomorphism between the two-sided ideals of a
  non-unital non-assoc ring and that of its opposite ring.

-/

namespace TwoSidedIdeal
variable {R : Type*} [NonUnitalNonAssocRing R]
/--
Any two-sided-ideal in `A` corresponds to a two-sided-ideal in `Aᵒᵖ`.
-/
-- @[simps]
def toMop (rel : TwoSidedIdeal R) : (TwoSidedIdeal Rᵐᵒᵖ) where
  ringCon.r a b := rel.ringCon b.unop a.unop
  ringCon.iseqv := {
    refl a := rel.ringCon.refl a.unop
    symm := rel.ringCon.symm
    trans h1 h2 := rel.ringCon.trans h2 h1
  }
  ringCon.mul' h1 h2 := rel.ringCon.mul h2 h1
  ringCon.add' := rel.ringCon.add

open MulOpposite

/--
Any two-sided-ideal in `Aᵒᵖ` corresponds to a two-sided-ideal in `A`.
-/
@[simps]
def fromMop (rel : TwoSidedIdeal Rᵐᵒᵖ) : (TwoSidedIdeal R) where
  ringCon.r a b := rel.ringCon (op b) (op a)
  ringCon.iseqv :=
  { refl a := rel.ringCon.refl (op a)
    symm := rel.ringCon.symm
    trans h1 h2 := rel.ringCon.trans h2 h1 }
  ringCon.mul' h1 h2 := rel.ringCon.mul h2 h1
  ringCon.add' := rel.ringCon.add

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
def toMopOrderIso : (TwoSidedIdeal R) ≃o (TwoSidedIdeal Rᵐᵒᵖ) where
  toFun := toMop
  invFun := fromMop
  left_inv := unop_op
  right_inv := unop_op
  map_rel_iff' {a b} :=
    ⟨fun h x H ↦ b.ringCon.symm <| @h (MulOpposite.op x) <|
        by simpa [toMop, mem_iff] using a.ringCon.symm H,
    fun h x H ↦ b.ringCon.symm <| @h (MulOpposite.unop x) <|
        by simpa [fromMop, mem_iff] using a.ringCon.symm H⟩

end TwoSidedIdeal
