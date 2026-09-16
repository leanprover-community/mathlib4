/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Nonneg.Basic

/-!
# Nonnegative elements are archimedean

This file defines instances and prove some properties about the nonnegative elements
`Nonneg α` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `Nonneg α` is a `FloorSemiring` if `α` is.
-/

public section

assert_not_exists Finset Field

namespace Nonneg

variable {α : Type*}

instance floorSemiring [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α] :
    FloorSemiring (Nonneg α) where
  floor a := ⌊(a : α)⌋₊
  ceil a := ⌈(a : α)⌉₊
  floor_of_neg ha := FloorSemiring.floor_of_neg ha
  gc_floor ha := FloorSemiring.gc_floor (Subtype.coe_le_coe.2 ha)
  gc_ceil a n := FloorSemiring.gc_ceil (a : α) n

@[norm_cast]
theorem nat_floor_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α]
    (a : Nonneg α) :
    ⌊(a : α)⌋₊ = ⌊a⌋₊ :=
  rfl

@[norm_cast]
theorem nat_ceil_coe [Semiring α] [PartialOrder α] [IsOrderedRing α] [FloorSemiring α]
    (a : Nonneg α) :
    ⌈(a : α)⌉₊ = ⌈a⌉₊ :=
  rfl

end Nonneg
