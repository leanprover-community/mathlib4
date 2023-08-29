/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.Order.Archimedean

#align_import algebra.order.nonneg.floor from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

/-!
# Nonnegative elements are archimedean

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `FloorSemiring` if `α` is.
-/

namespace Nonneg

variable {α : Type*}

instance archimedean [OrderedAddCommMonoid α] [Archimedean α] : Archimedean { x : α // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : α) (hy : (0 : α) < y)
    ⟨n, show (x : α) ≤ (n • y : { x : α // 0 ≤ x }) by simp [*, -nsmul_eq_mul, nsmul_coe]⟩⟩
                                                       -- 🎉 no goals
#align nonneg.archimedean Nonneg.archimedean

instance floorSemiring [OrderedSemiring α] [FloorSemiring α] :
    FloorSemiring { r : α // 0 ≤ r } where
  floor a := ⌊(a : α)⌋₊
  ceil a := ⌈(a : α)⌉₊
  floor_of_neg ha := FloorSemiring.floor_of_neg ha
  gc_floor ha := FloorSemiring.gc_floor (Subtype.coe_le_coe.2 ha)
  gc_ceil a n := FloorSemiring.gc_ceil (a : α) n
#align nonneg.floor_semiring Nonneg.floorSemiring

@[norm_cast]
theorem nat_floor_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) :
    ⌊(a : α)⌋₊ = ⌊a⌋₊ :=
  rfl
#align nonneg.nat_floor_coe Nonneg.nat_floor_coe

@[norm_cast]
theorem nat_ceil_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) :
    ⌈(a : α)⌉₊ = ⌈a⌉₊ :=
  rfl
#align nonneg.nat_ceil_coe Nonneg.nat_ceil_coe
