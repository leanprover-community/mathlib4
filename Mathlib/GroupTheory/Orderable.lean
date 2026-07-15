/-
Copyright (c) 2026 Hang Lu Su, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Orderable

/-!
# Left- and right-orderable groups

Building on the monoid-level classes `IsLeftOrderable`, `IsRightOrderable` and `IsBiOrderable` (see
`Mathlib/Algebra/Order/Monoid/Orderable.lean`), this file adds the theory specific to a group `G`,
where inverses make the left- and right-handed notions coincide.

## Main declarations

* `isLeftOrderable_iff_isRightOrderable`: a group is left-orderable iff it is right-orderable.

The strict formulation `a < b → c * a < c * b` is available for cancellative monoids (hence groups)
via `isLeftOrderable_iff_exists_linearOrder_mulLeftStrictMono`
(`Mathlib/Algebra/Order/Monoid/Orderable.lean`). Products of orderable monoids are handled — again
only assuming cancellativity — in `Mathlib/Algebra/Order/Monoid/Orderable/Prod.lean` (binary) and
`Mathlib/Algebra/Order/Monoid/Orderable/Pi.lean` (indexed).

## Implementation notes

Since `IsLeftOrderable` and `IsRightOrderable` coincide over a group, neither direction of
`isLeftOrderable_iff_isRightOrderable` is made an instance: they would loop.
-/

@[expose] public section

variable {G : Type*} [Group G]

/-- A group is left-orderable iff it is right-orderable. -/
theorem isLeftOrderable_iff_isRightOrderable : IsLeftOrderable G ↔ IsRightOrderable G := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono G
    refine ⟨LinearOrder.lift' (·⁻¹) inv_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change (a * c)⁻¹ ≤ (b * c)⁻¹
    rw [mul_inv_rev, mul_inv_rev]
    gcongr
    exact hab
  · obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono G
    refine ⟨LinearOrder.lift' (·⁻¹) inv_injective, ⟨fun c a b hab ↦ ?_⟩⟩
    change (c * a)⁻¹ ≤ (c * b)⁻¹
    rw [mul_inv_rev, mul_inv_rev]
    gcongr
    exact hab
