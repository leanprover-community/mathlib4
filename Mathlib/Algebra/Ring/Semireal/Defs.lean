/-
 Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Florent Schaffhauser
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Field.Defs

/-!
# Semireal rings

A semireal ring is a non-trivial commutative ring (with unit) in which `-1` is *not* a sum of
squares. Note that `-1` does not make sense in a semiring.

For instance, linearly ordered fields are semireal, because sums of squares are positive and `-1` is
not. More generally, linearly ordered semirings in which `a ≤ b → ∃ c, a + c = b` holds, are
semireal.

## Main declaration

- `isSemireal`: the predicate asserting that a commutative ring `R` is semireal.

## Auxiliary declarations

- The predicate `isSumSq : R → Prop`: an inducitve predicate used to define sums of squares in a
semiring `R`.
- The type `SumSqIn R`: a subtype of `R` whose terms are the sums of squares in `R`.

## Auxiliary theorems

- `SumSq_nonneg`: sums of squares are non-negative.
- `isSumSq_sum`: if `S₁` and `S₂` are sums of squares in a semiring `R`, then so is `S₁ + S₂`.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984). [DOI: 10.1216/RMJ-1984-14-4-767](https://projecteuclid.org/journals/rocky-mountain-journal-of-mathematics/volume-14/issue-4/An-introduction-to-real-algebra/10.1216/RMJ-1984-14-4-767.full).
-/

/--
In a semiring `R`, the property of being a sum of squares is an inductive predicate: `0 : R` is a
sum of squares and if `S` is a sum of squares, then for all `a : R`, `a ^ 2 + S` is a sum of squares
in `R`.
-/

inductive isSumSq.{u} {R : Type u} [Semiring R] : R → Prop
  | zero                           : isSumSq (0 : R)
  | add (x S : R) (pS : isSumSq S) : isSumSq (x ^ 2 + S)

/--
A semireal ring is a non-trivial commutative ring (with unit) in which `-1` is *not* a sum of
squares. Note that `-1` does not make sense in a semiring.
-/

@[class, mk_iff]
structure isSemireal.{u} (R : Type u) [CommRing R] : Prop where
  non_trivial        : (0 : R) ≠ 1
  neg_one_not_SumSq  : ¬isSumSq (-1 : R)

/--
Let `R` be a linearly ordered semiring `R` in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used to show that
linearly ordered fields are semireal.
-/

theorem SumSq_nonneg  {R : Type _} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R} :
    isSumSq S → 0 ≤ S := by
  intro pS
  induction pS with
  | zero          => simp only [le_refl]
  | add x S _ ih  =>
    apply add_nonneg ?_ ih
    simp only [sq_nonneg]

instance {R : Type _} [LinearOrderedField R] : isSemireal R where
  non_trivial := zero_ne_one
  neg_one_not_SumSq := by
    intro h
    have aux : (0 : R) ≤ -1 := SumSq_nonneg h
    apply absurd aux
    apply not_le.mpr
    exact neg_one_lt_zero

/--
The type of sums of squares in a semiring `R` is the subtype of `R` defined by the predicate
`isSumSq : R → Prop`. It  can be defined as a structure whose terms are dependent pairs `⟨x, hx⟩`
where `x : R` and `hx` is a proof of  the proposition `isSumSq x`.
-/

structure SumSqIn.{u} (R : Type u) [Semiring R] where
  /--Terms of type `SumSqIn R` are dependent pairs `⟨x, hx⟩` where `x : R` and `hx` is a proof of
  the proposition `isSumSq x`-/ --#
  val  : R
  ppty : isSumSq val

/--
If `S1` and `S2` are sums of squares in a semiring `R`, then `S1 + S2` is a sum of squares in `R`.
-/

theorem isSumSq_sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : isSumSq S1) (h2 : isSumSq S2) :
    isSumSq (S1 + S2) := by
  induction h1 with
  | zero => simp only [zero_add]; exact h2
  | add a S hS ih =>  rw [add_assoc]; exact isSumSq.add a (S + S2) ih

/--
Given terms `(S₁ S₂ : SumSqIn R)` where `Sᵢ = ⟨xᵢ, hxᵢ⟩`, we define `S1 + S2` to be the dependent
pair `⟨x₁ + x₂, h⟩`, where `h` is a proof that `x₁ + x₂` is a sum of squares in `R`. The term `h` is
obtained by applying the function `isSumSq_sum`.
-/

def add_SumSq {R : Type} [Semiring R] : SumSqIn R → SumSqIn R → SumSqIn R :=
  fun (S1 S2 : SumSqIn R) => ⟨S1.val + S2.val, isSumSq_sum S1.ppty S2.ppty⟩

instance {R : Type} [Semiring R] : Add (SumSqIn R) := ⟨add_SumSq⟩
