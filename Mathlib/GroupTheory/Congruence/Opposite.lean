/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Algebra.Opposites

/-!
# Congruences on the opposite of a group

This file defines the order isomorphism between the congruences on a group `G` and the congruences
on the opposite group `Gᵒᵖ`.
-/


variable {M : Type*} [Mul M]

namespace Con

/-- If `c` is a multiplicative congruence on `M`, then `(a, b) ↦ c b.unop a.unop` is a
multiplicative congruence on `Mᵐᵒᵖ`-/
@[to_additive "If `c` is an additive congruence on `M`, then `(a, b) ↦ c b.unop a.unop` is an
additive congruence on `Mᵃᵒᵖ`"]
def op (c : Con M) : Con Mᵐᵒᵖ where
  r a b := c b.unop a.unop
  iseqv :=
  { refl := fun a ↦ c.refl a.unop
    symm := c.symm
    trans := fun h1 h2 ↦ c.trans h2 h1 }
  mul' h1 h2 := c.mul h2 h1

/-- If `c` is a multiplicative congruence on `Mᵐᵒᵖ`, then `(a, b) ↦ c bᵒᵖ aᵒᵖ` is a multiplicative
congruence on `M`-/
@[to_additive "If `c` is an additive congruence on `Mᵃᵒᵖ`, then `(a, b) ↦ c bᵒᵖ aᵒᵖ` is an additive
congruence on `M`"]
def unop (c : Con Mᵐᵒᵖ) : Con M where
  r a b := c (.op b) (.op a)
  iseqv :=
  { refl := fun a ↦ c.refl (.op a)
    symm := c.symm
    trans := fun h1 h2 ↦ c.trans h2 h1 }
  mul' h1 h2 := c.mul h2 h1

/--
The multiplicative congruences on `M` bijects to the multiplicative congruences on `Mᵐᵒᵖ`
-/
@[to_additive (attr := simps) "The additive congruences on `M` bijects to the additive congruences
on `Mᵃᵒᵖ`"]
def orderIsoOp : Con M ≃o Con Mᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'

end Con
