/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
import Mathlib.GroupTheory.Submonoid.Basic
import Mathlib.Algebra.Group.Opposite

/-!
# Submonoid of opposite monoids

For every monoid `M`, we construct an equivalence between submonoids of `M` and that of `Mᵐᵒᵖ`.

-/

variable {M : Type*} [MulOneClass M]

namespace Submonoid

/-- pull a submonoid back to an opposite submonoid along `unop`-/
@[to_additive (attr := simps) "pull an additive submonoid back to an opposite submonoid along
`unop`"]
protected def op {M : Type*} [MulOneClass M] (x : Submonoid M) : Submonoid (MulOpposite M) where
  carrier := MulOpposite.unop ⁻¹' x.1
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

/-- pull an opposite submonoid back to a submonoid along `op`-/
@[to_additive (attr := simps) "pull an opposite additive submonoid back to a submonoid along `op`"]
protected def unop {M : Type*} [MulOneClass M] (x : Submonoid (MulOpposite M)) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x.1
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

/-- A submonoid `H` of `G` determines a submonoid `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) "A additive submonoid `H` of `G` determines an additive submonoid
`H.opposite` of the opposite group `Gᵐᵒᵖ`."]
def opEquiv : Submonoid M ≃ Submonoid Mᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl

/-- Bijection between a submonoid `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive submonoid `H` and its opposite."]
def equivOp (H : Submonoid M) : H ≃ op H :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Submonoid
