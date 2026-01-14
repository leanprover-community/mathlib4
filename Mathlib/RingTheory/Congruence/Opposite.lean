/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.RingTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Opposite

/-!
# Congruences on the opposite ring

This file defines the order isomorphism between the congruences on a ring `R` and the congruences on
the opposite ring `Rᵐᵒᵖ`.

-/

variable {R : Type*} [Add R] [Mul R]

namespace RingCon

/--
If `c` is a `RingCon R`, then `(a, b) ↦ c b.unop a.unop` is a `RingCon Rᵐᵒᵖ`.
-/
def op (c : RingCon R) : RingCon Rᵐᵒᵖ where
  __ := c.toCon.op
  mul' h1 h2 := c.toCon.op.mul h1 h2
  add' h1 h2 := c.add h1 h2

lemma op_iff {c : RingCon R} {x y : Rᵐᵒᵖ} : c.op x y ↔ c y.unop x.unop := Iff.rfl

/--
If `c` is a `RingCon Rᵐᵒᵖ`, then `(a, b) ↦ c b.op a.op` is a `RingCon R`.
-/
def unop (c : RingCon Rᵐᵒᵖ) : RingCon R where
  __ := c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2

lemma unop_iff {c : RingCon Rᵐᵒᵖ} {x y : R} : c.unop x y ↔ c (.op y) (.op x) := Iff.rfl

/--
The congruences of a ring `R` biject to the congruences of the opposite ring `Rᵐᵒᵖ`.
-/
@[simps]
def opOrderIso : RingCon R ≃o RingCon Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'

end RingCon
