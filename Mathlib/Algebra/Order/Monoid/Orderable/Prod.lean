/-
Copyright (c) 2026 Hang Lu Su, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Monoid.Orderable.Defs
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Products of orderable monoids

The direct product `G × H` of two orderable monoids is orderable, provided the *first* factor is
cancellative. Ordering `G × H` lexicographically, left multiplication is monotone as soon as it is
*strictly* monotone on the first factor and monotone on the second (see
`Mathlib/Algebra/Order/Monoid/Prod.lean`); by `mulLeftStrictMono_iff_isLeftCancelMul` strictness on
the first factor is exactly cancellativity, so `IsLeftCancelMul` on the first factor is the only
hypothesis beyond orderability — the second factor needs no cancellation.
-/

@[expose] public section

variable {G H : Type*} [Monoid G] [Monoid H]

/-- The product of a left-cancellative left-orderable monoid `G` and a left-orderable monoid `H` is
left-orderable, via the lexicographic order (strict on `G`, monotone on `H`). -/
@[to_additive /-- The product of a left-cancellative left-orderable additive monoid `G` and a
left-orderable additive monoid `H` is left-orderable, via the lexicographic order
(strict on `G`, monotone on `H`). -/]
instance Prod.instIsLeftOrderable [IsLeftCancelMul G] [IsLeftOrderable G] [IsLeftOrderable H] :
    IsLeftOrderable (G × H) := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftStrictMono G
  obtain ⟨_, _⟩ := exists_linearOrder_mulLeftMono H
  exact .of_mulEquiv (ofLexMulEquiv (G × H))

/-- The product of a right-cancellative right-orderable monoid `G` and a right-orderable monoid `H`
is right-orderable, via the lexicographic order (strict on `G`, monotone on `H`). -/
@[to_additive /-- The product of a right-cancellative right-orderable additive monoid `G` and a
right-orderable additive monoid `H` is right-orderable, via the lexicographic order
(strict on `G`, monotone on `H`). -/]
instance Prod.instIsRightOrderable [IsRightCancelMul G] [IsRightOrderable G] [IsRightOrderable H] :
    IsRightOrderable (G × H) := by
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightStrictMono G
  obtain ⟨_, _⟩ := exists_linearOrder_mulRightMono H
  exact .of_mulEquiv (ofLexMulEquiv (G × H))
