/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Data.Fintype.EquivFin

/-! # A characteristic-zero semiring is infinite -/

@[expose] public section


open Set

variable (M : Type*) [AddMonoidWithOne M] [CharZero M]

-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective Nat.cast Nat.cast_injective
