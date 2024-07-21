/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Sums of squares

We introduce the type sums of squares in a semiring `R` as the subtype of `R` whose terms are
sums of squares in `R`. The associated predicate `isSumSq : R → Prop` is defined inductively:
`0 : R` is a sum of squares and if `S` is a sum of squares, then for all `a : R`, `a ^ 2 + S` is a
sum of squares in `R`.

## Main declaration

- The type `SumSqIn R`: it is the type of sums of squares in `R`, where `R` is a semiring.

## Auxiliary declarations

- The predicate `isSumSq : R → Prop`: the predicate used to define the type `SumSqIn R` as a subtype
of `R`.

## Theorems

- `isSumSq.add`: if `S₁` and `S₂` are sums of squares in a semiring `R`, then so is `S₁ + S₂`.
- `SumSq.nonneg`: sums of squares are non-negative.

## Instances

- An `Add` instance on the type of sums of squares in a semiring `R`.

-/

/--
In a semiring `R`, the property of being a sum of squares is an inductive predicate: `0 : R` is a
sum of squares and if `S` is a sum of squares, then for all `a : R`, `a ^ 2 + S` is a sum of squares
in `R`.
-/

@[mk_iff]
inductive isSumSq {R : Type*} [Add R] [Mul R] [Zero R] : R → Prop
  | zero                              : isSumSq 0
  | sq_add (x S : R) (pS : isSumSq S) : isSumSq (x * x + S)

/--
The type of sums of squares in a semiring `R` is the subtype of `R` defined by the predicate
`isSumSq : R → Prop`. It  can be defined as a structure whose terms are dependent pairs `⟨x, hx⟩`
where `x : R` and `hx` is a proof of  the proposition `isSumSq x`.
-/

structure SumSqIn (R : Type*) [Add R] [Mul R] [Zero R] where
  /-- `val` is a term in `R` and `ppty` is a proof of the proposition `isSumSq val` -/
  val  : R
  ppty : isSumSq val

/--
If `S1` and `S2` are sums of squares in a semiring `R`, then `S1 + S2` is a sum of squares in `R`.
-/

/-
*TODO*: `isSumSq.add` could be rewritten with weaker assumptions on `R` (we only need to
guarantee that we can use `AddZeroClass.zero_add` and `AddSemigroup.add_assoc`).
-/
theorem isSumSq.add {R : Type*} [Semiring R] {S1 S2 : R} (h1 : isSumSq S1) (h2 : isSumSq S2) :
    isSumSq (S1 + S2) := by
  induction h1 with
  | zero             => rewrite [zero_add]; exact h2
  | sq_add a S hS ih => rewrite [add_assoc]; exact isSumSq.sq_add a (S + S2) ih

/--
Given terms `(S₁ S₂ : SumSqIn R)` where `Sᵢ = ⟨xᵢ, hxᵢ⟩`, we define `S1 + S2` to be the dependent
pair `⟨x₁ + x₂, h⟩`, where `h` is a proof that `x₁ + x₂` is a sum of squares in `R`. The term `h` is
obtained by applying the function `isSumSq.add`.
-/

def SumSq.add {R : Type*} [Semiring R] (S₁ : SumSqIn R) (S₂ : SumSqIn R) : SumSqIn R :=
  ⟨S₁.val + S₂.val, isSumSq.add S₁.ppty S₂.ppty⟩

instance {R : Type*} [Semiring R] : Add (SumSqIn R) := ⟨SumSq.add⟩

/--
Let `R` be a linearly ordered semiring `R` in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used to show that
linearly ordered fields are semireal.
-/

theorem isSumSq.nonneg  {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : isSumSq S) : 0 ≤ S := by
  induction pS with
  | zero          => simp only [le_refl]
  | sq_add x S _ ih  =>
    apply add_nonneg ?_ ih
    simp only [← pow_two x, sq_nonneg]
