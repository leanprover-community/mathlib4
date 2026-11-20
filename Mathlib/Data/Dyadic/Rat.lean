/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Dyadic.Basic
public import Mathlib.Order.Hom.Basic

/-!
# The inclusion of dyadic rationals into the rationals

This file bundles `Dyadic.toRat` as a ring homomorphism and an order embedding.
-/

@[expose] public section

namespace Dyadic

/-- Coercion from dyadic rationals to rational numbers as a ring homomorphism. -/
@[simps]
def toRatRingHom : Dyadic →+* ℚ where
  toFun := toRat
  map_zero' := toRat_zero
  map_one' := toRat_one
  map_add' := toRat_add
  map_mul' := toRat_mul

/-- Coercion from dyadic rationals to rational numbers as an order embedding. -/
@[simps]
def toRatOrderEmbedding : Dyadic ↪o ℚ where
  toFun := toRat
  inj' := fun _ _ ↦ toRat_inj.mp
  map_rel_iff' := toRat_le_toRat_iff

end Dyadic
