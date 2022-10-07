/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Order.Monotone

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`has_mul` or `mul_one_class`.

-/


-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.
open Function

variable {α β : Type _}

section Mul

variable [Mul α]

section LE

variable [LE α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
theorem mul_le_mul_left' [CovariantClass α α (· * ·) (· ≤ ·)] {b c : α} (bc : b ≤ c) (a : α) : a * b ≤ a * c :=
  CovariantClass.elim _ bc

@[to_additive le_of_add_le_add_left]
theorem le_of_mul_le_mul_left' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (bc : a * b ≤ a * c) : b ≤ c :=
  ContravariantClass.elim _ bc

@[simp, to_additive]
theorem mul_le_mul_iff_left [CovariantClass α α (· * ·) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α)
    {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov α α (· * ·) (· ≤ ·) a

@[simp, to_additive]
theorem mul_le_mul_iff_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [ContravariantClass α α (swap (· * ·)) (· ≤ ·)]
    (a : α) {b c : α} : b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a

end LE

section LT

variable [LT α]

@[simp, to_additive]
theorem mul_lt_mul_iff_left [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)] (a : α)
    {b c : α} : a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a

@[simp, to_additive]
theorem mul_lt_mul_iff_right [CovariantClass α α (swap (· * ·)) (· < ·)] [ContravariantClass α α (swap (· * ·)) (· < ·)]
    (a : α) {b c : α} : b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a

@[to_additive add_lt_add_left]
theorem mul_lt_mul_left' [CovariantClass α α (· * ·) (· < ·)] {b c : α} (bc : b < c) (a : α) : a * b < a * c :=
  CovariantClass.elim _ bc

@[to_additive lt_of_add_lt_add_left]
theorem lt_of_mul_lt_mul_left' [ContravariantClass α α (· * ·) (· < ·)] {a b c : α} (bc : a * b < a * c) : b < c :=
  ContravariantClass.elim _ bc

end LT
