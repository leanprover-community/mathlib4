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

/-- Pull a submonoid back to an opposite submonoid along `MulOpposite.unop`-/
@[to_additive (attr := simps) "Pull an additive submonoid back to an opposite submonoid along
`AddOpposite.unop`"]
protected def op {M : Type*} [MulOneClass M] (x : Submonoid M) : Submonoid (MulOpposite M) where
  carrier := MulOpposite.unop ⁻¹' x.1
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

/-- Pull an opposite submonoid back to a submonoid along `MulOpposite.op`-/
@[to_additive (attr := simps) "Pull an opposite additive submonoid back to a submonoid along
`AddOpposite.op`"]
protected def unop {M : Type*} [MulOneClass M] (x : Submonoid (MulOpposite M)) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x.1
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

/-- A submonoid `H` of `G` determines a submonoid `H.op` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) "A additive submonoid `H` of `G` determines an additive submonoid
`H.op` of the opposite group `Gᵐᵒᵖ`."]
def opEquiv : Submonoid M ≃ Submonoid Mᵐᵒᵖ where
  toFun := Submonoid.op
  invFun := Submonoid.unop
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl

/-- Bijection between a submonoid `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive submonoid `H` and its opposite."]
def equivOp (H : Submonoid M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Submonoid
