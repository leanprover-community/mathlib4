/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public import Mathlib.Algebra.Group.SelfInv
public import Mathlib.Algebra.Ring.Int.Parity

/-!
# Powers of self-inverse elements

In a monoid in which every element is its own inverse, a power `a ^ n` depends only on the parity
of `n`. This file records that for natural and integer exponents.

As in `Mathlib/Algebra/Group/SelfInv.lean`, the lemmas are stated multiplicatively for
`IsSelfInvMonoid` and `to_additive`d into `IsSelfNegAddMonoid`. They live here rather than alongside
the rest of the API because `Even` and `Odd` are not available at that point in the hierarchy.

## Tags

involution, parity, exponent two, characteristic two
-/

@[expose] public section

namespace IsSelfInvMonoid

variable {M : Type*}

section Monoid
variable [Monoid M] [IsSelfInvMonoid M]

@[to_additive]
theorem pow_even {n : ℕ} (hn : Even n) (a : M) : a ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, IsSelfInvMonoid.sq, one_pow]

@[to_additive]
theorem pow_odd {n : ℕ} (hn : Odd n) (a : M) : a ^ n = a := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, pow_one, pow_even (even_two_mul k), one_mul]

@[to_additive]
theorem pow_eq_ite (a : M) (n : ℕ) : a ^ n = if Even n then 1 else a := by
  split
  · exact pow_even ‹_› a
  · exact pow_odd (Nat.not_even_iff_odd.1 ‹_›) a

end Monoid

section Group
variable [Group M] [IsSelfInvMonoid M] {a : M} {m n : ℤ}

@[to_additive]
theorem zpow_even (hn : Even n) (a : M) : a ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, zpow_mul, IsSelfInvMonoid.zpow_two, one_zpow]

@[to_additive]
theorem zpow_odd (hn : Odd n) (a : M) : a ^ n = a := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add, zpow_one, zpow_even (even_two_mul k), one_mul]

@[to_additive]
theorem zpow_eq_one_iff (ha : a ≠ 1) : a ^ n = 1 ↔ Even n :=
  ⟨fun h ↦ (Int.even_or_odd n).resolve_right fun hn ↦ ha ((zpow_odd hn a).symm.trans h),
    fun h ↦ zpow_even h a⟩

@[to_additive]
theorem zpow_eq_self_iff (ha : a ≠ 1) : a ^ n = a ↔ Odd n :=
  ⟨fun h ↦ (Int.even_or_odd n).resolve_left fun hn ↦ ha (h.symm.trans (zpow_even hn a)),
    fun h ↦ zpow_odd h a⟩

@[to_additive]
theorem zpow_eq_zpow_iff (ha : a ≠ 1) : a ^ m = a ^ n ↔ Even (m - n) := by
  rw [← zpow_eq_one_iff ha (n := m - n), zpow_sub, mul_inv_eq_one]

end Group

end IsSelfInvMonoid
