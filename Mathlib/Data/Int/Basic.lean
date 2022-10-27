/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Std
import Mathlib.Tactic.Convert
import Mathlib.Init.Data.Int.Notation
import Mathlib.Algebra.Ring.Basic

/-!
# Basic operations on the integers

This file contains:
* instances on `ℤ`. The stronger one is `int.linear_ordered_comm_ring`.
* some basic lemmas about integers

## Recursors

* `int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values.
* `int.bit_cases_on`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.
* `int.induction_on`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `int.induction_on'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

namespace Int

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_elim] protected def inductionOn' {C : ℤ → Sort _}
    (z : ℤ) (b : ℤ) (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1))
    (Hp : ∀ k ≤ b, C k → C (k - 1)) : C z := by
  rw [← sub_add_cancel (G := ℤ) z b, add_comm]
  exact match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, C (b + n)
  | 0 => _root_.cast (by erw [add_zero]) H0
  | n+1 => _root_.cast (by rw [add_assoc]; rfl) <|
    Hs _ (Int.le_add_of_nonneg_right (ofNat_nonneg _)) (pos n)

  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, C (b + -[n+1])
  | 0 => Hp _ (Int.le_refl _) H0
  | n+1 => by
    refine _root_.cast (by rw [add_sub_assoc]; rfl) (Hp _ (Int.le_of_lt ?_) (neg n))
    conv => rhs; apply (add_zero b).symm
    rw [Int.add_lt_add_iff_left]; apply negSucc_lt_zero
