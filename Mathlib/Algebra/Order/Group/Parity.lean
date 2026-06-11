/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Defs.LinearOrder

/-!
# Parity in ordered monoids

This file proves results about square and even elements in ordered monoids.
-/

public section

section
variable {M : Type*} [LinearOrder M] [Mul M] {a b : M}

@[to_additive]
protected lemma IsSquare.max (ha : IsSquare a) (hb : IsSquare b) : IsSquare (max a b) := by grind

@[to_additive]
protected lemma IsSquare.min (ha : IsSquare a) (hb : IsSquare b) : IsSquare (min a b) := by grind

end
