/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Common

#align_import algebra.quotient from "leanprover-community/mathlib"@"d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d"

/-!
# Algebraic quotients

This file defines notation for algebraic quotients, e.g. quotient groups `G ⧸ H`,
quotient modules `M ⧸ N` and ideal quotients `R ⧸ I`.

The actual quotient structures are defined in the following files:
 * quotient group: `Mathlib/GroupTheory/QuotientGroup.lean`
 * quotient module: `Mathlib/LinearAlgebra/Quotient.lean`
 * quotient ring: `Mathlib/RingTheory/Ideal/Quotient.lean`

## Notations

The following notation is introduced:

* `G ⧸ H` stands for the quotient of the type `G` by some term `H`
  (for example, `H` can be a normal subgroup of `G`).
  To implement this notation for other quotients, you should provide a `HasQuotient` instance.
  Note that since `G` can usually be inferred from `H`, `_ ⧸ H` can also be used,
  but this is less readable.

## Tags

quotient, group quotient, quotient group, module quotient, quotient module, ring quotient,
ideal quotient, quotient ring
-/


universe u v

/-- `HasQuotient A B` is a notation typeclass that allows us to write `A ⧸ b` for `b : B`.
This allows the usual notation for quotients of algebraic structures,
such as groups, modules and rings.

`A` is a parameter, despite being unused in the definition below, so it appears in the notation.
-/
class HasQuotient (A : outParam <| Type u) (B : Type v) where
  /-- auxiliary quotient function, the one used will have `A` explicit -/
  quotient' : B → Type max u v
#align has_quotient HasQuotient

-- Will be provided by e.g. `Ideal.Quotient.inhabited`
/-- `HasQuotient.Quotient A b` (with notation `A ⧸ b`) is the quotient
 of the type `A` by `b`.

This differs from `HasQuotient.quotient'` in that the `A` argument is
 explicit, which is necessary to make Lean show the notation in the
 goal state.
-/
abbrev HasQuotient.Quotient (A : outParam <| Type u) {B : Type v}
    [HasQuotient A B] (b : B) : Type max u v :=
  HasQuotient.quotient' b
#align has_quotient.quotient HasQuotient.Quotient

/-- Quotient notation based on the `HasQuotient` typeclass -/
notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H
