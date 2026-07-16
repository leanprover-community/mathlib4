/-
Copyright (c) 2026 Hang Lu Su, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Algebra.Order.Monoid.Orderable
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Indexed products of orderable monoids

An arbitrary indexed product `∀ i, G i` of orderable monoids is orderable when *every* factor is
cancellative. Well-order the index (by Zermelo, `exists_wellFoundedLT`) and order the product
lexicographically: left multiplication is monotone as soon as it is *strictly* monotone on every
factor; strictness per factor is exactly cancellativity, `mulLeftStrictMono_iff_isLeftCancelMul`.

Unlike the binary product (`Mathlib/Algebra/Order/Monoid/Orderable/Prod.lean`), where only the first
factor need be strict, a well-order has no greatest index, so strictness is required everywhere.
-/

@[expose] public section

variable {ι : Type*} {G : ι → Type*}

/-- An indexed product of left-cancellative left-orderable monoids is left-orderable, via the
lexicographic order along a well-ordering of the index (strict on every factor). -/
@[to_additive /-- An indexed product of left-cancellative left-orderable additive monoids is
left-orderable, via the lexicographic order along a well-ordering of the index (strict on every
factor). -/]
instance Pi.instIsLeftOrderable [∀ i, Monoid (G i)] [∀ i, IsLeftCancelMul (G i)]
    [∀ i, IsLeftOrderable (G i)] : IsLeftOrderable (∀ i, G i) := by
  choose l hl using fun i ↦ exists_linearOrder_mulLeftStrictMono (G i)
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  exact .of_mulEquiv (ofLexMulEquiv (∀ i, G i))

/-- An indexed product of right-cancellative right-orderable monoids is right-orderable, via the
lexicographic order along a well-ordering of the index (strict on every factor). -/
@[to_additive /-- An indexed product of right-cancellative right-orderable additive monoids is
right-orderable, via the lexicographic order along a well-ordering of the index (strict on every
factor). -/]
instance Pi.instIsRightOrderable [∀ i, Monoid (G i)] [∀ i, IsRightCancelMul (G i)]
    [∀ i, IsRightOrderable (G i)] : IsRightOrderable (∀ i, G i) := by
  choose l hl using fun i ↦ exists_linearOrder_mulRightStrictMono (G i)
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  exact .of_mulEquiv (ofLexMulEquiv (∀ i, G i))
