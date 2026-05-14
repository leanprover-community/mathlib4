/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Util.CompileInductive

/-!
# Definitions of Archimedean monoids

This file defines the archimedean property for ordered monoids.

## Main definitions

* `Archimedean` is a typeclass for an ordered additive commutative monoid to have the archimedean
  property.
* `MulArchimedean` is a typeclass for an ordered commutative monoid to have the "mul-archimedean
  property" where for `x` and `y > 1`, there exists a natural number `n` such that `x ≤ y ^ n`.
-/

public section

variable {R : Type*}

/-- An ordered additive commutative monoid is called `Archimedean` if for any two elements `x`, `y`
such that `0 < y`, there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (R) [AddCommMonoid R] [PartialOrder R] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : R) {y : R}, 0 < y → ∃ n : ℕ, x ≤ n • y

/-- An ordered commutative monoid is called `MulArchimedean` if for any two elements `x`, `y`
such that `1 < y`, there exists a natural number `n` such that `x ≤ y ^ n`. -/
@[to_additive Archimedean]
class MulArchimedean (R) [CommMonoid R] [PartialOrder R] : Prop where
  /-- For any two elements `x`, `y` such that `1 < y`, there exists a natural number `n`
  such that `x ≤ y ^ n`. -/
  arch : ∀ (x : R) {y : R}, 1 < y → ∃ n : ℕ, x ≤ y ^ n

section OrderedMonoid
variable [CommMonoid R] [PartialOrder R] [MulLeftStrictMono R] [MulArchimedean R]

@[to_additive]
theorem exists_lt_pow {a : R} (ha : 1 < a) (b : R) : ∃ n : ℕ, b < a ^ n :=
  let ⟨k, hk⟩ := MulArchimedean.arch b ha
  ⟨k + 1, hk.trans_lt <| pow_lt_pow_right' ha k.lt_succ_self⟩

end OrderedMonoid

section OrderedGroup
variable [CommGroup R] [LinearOrder R] [IsOrderedMonoid R] [MulArchimedean R]

@[to_additive]
theorem exists_pow_lt {a : R} (ha : a < 1) (b : R) : ∃ n : ℕ, a ^ n < b :=
  (exists_lt_pow (one_lt_inv'.mpr ha) b⁻¹).imp <| by simp

end OrderedGroup

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_nat_ge (x : R) : ∃ n : ℕ, x ≤ n := by
  nontriviality R
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

theorem exists_nat_gt (x : R) : ∃ n : ℕ, x < n :=
  (exists_lt_nsmul zero_lt_one x).imp fun n hn ↦ by rwa [← nsmul_one]

end StrictOrderedSemiring

section OrderedRing
variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_int_ge (x : R) : ∃ n : ℤ, x ≤ n := let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

theorem exists_int_le (x : R) : ∃ n : ℤ, n ≤ x :=
  let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

end OrderedRing

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem exists_int_gt (x : R) : ∃ n : ℤ, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

theorem exists_int_lt (x : R) : ∃ n : ℤ, (n : R) < x :=
  let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

end StrictOrderedRing
