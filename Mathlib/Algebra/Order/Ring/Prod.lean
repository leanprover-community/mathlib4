/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Products of ordered rings
-/

@[expose] public section

variable {α β : Type*}

instance [Semiring α] [PartialOrder α] [IsOrderedRing α]
    [Semiring β] [PartialOrder β] [IsOrderedRing β] : IsOrderedRing (α × β) where
  zero_le_one := ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_left hbc.1 ha.1, mul_le_mul_of_nonneg_left hbc.2 ha.2⟩
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_right hbc.1 ha.1, mul_le_mul_of_nonneg_right hbc.2 ha.2⟩
