/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Algebra.Field.Defs

#align_import algebra.continued_fractions.basic from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Integer continued fractions (icfs)
5. Computation of convergents using the recurrence relation in `convergents`.
6. Computation of convergents by directly evaluating the fraction described by the gcf in
`convergents'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them `ContinuedFractions` in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

-- Fix a carrier `α`.
variable (α : Type*)

/-! ### Definitions -/

/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ, bᵢ⟩`. -/
structure GeneralizedContinuedFraction.Pair where
  /-- Partial numerator -/
  protected a : α
  /-- Partial denominator -/
  protected b : α
  deriving Inhabited
#align generalized_continued_fraction.pair GeneralizedContinuedFraction.Pair

open GeneralizedContinuedFraction

namespace GeneralizedContinuedFraction.Pair

variable {α}

/-- Make a `GCF.Pair` printable. -/
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ ↦ "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

/-- Maps a function `f` on both components of a given pair. -/
@[simps]
def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩
#align generalized_continued_fraction.pair.map GeneralizedContinuedFraction.Pair.map

end GeneralizedContinuedFraction.Pair

/-- A *generalised continued fraction* (gcf) is a potentially infinite expression of the form
$$
  h + \dfrac{a_0}
            {b_0 + \dfrac{a_1}
                         {b_1 + \dfrac{a_2}
                                      {b_2 + \dfrac{a_3}
                                                   {b_3 + \dots}}}}
$$
where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf.
We store the sequence of partial numerators and denominators in a sequence of
`GeneralizedContinuedFraction.Pair`s `s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
@[ext]
structure GeneralizedContinuedFraction where
  /-- Head term -/
  protected h : α
  /-- Sequence of partial numerator and denominator pairs. -/
  protected s : Stream'.Seq (Pair α)
#align generalized_continued_fraction GeneralizedContinuedFraction
#align generalized_continued_fraction.ext_iff GeneralizedContinuedFraction.ext_iff
#align generalized_continued_fraction.ext GeneralizedContinuedFraction.ext

variable {α}

namespace GeneralizedContinuedFraction

/-- Constructs a generalized continued fraction without fractional part. -/
@[simps]
def ofInteger (a : α) : GeneralizedContinuedFraction α :=
  ⟨a, Stream'.Seq.nil⟩
#align generalized_continued_fraction.of_integer GeneralizedContinuedFraction.ofInteger

instance [Inhabited α] : Inhabited (GeneralizedContinuedFraction α) :=
  ⟨ofInteger default⟩

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partialNumerators (g : GeneralizedContinuedFraction α) : Stream'.Seq α :=
  g.s.map Pair.a
#align generalized_continued_fraction.partial_numerators GeneralizedContinuedFraction.partialNumerators

/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partialDenominators (g : GeneralizedContinuedFraction α) : Stream'.Seq α :=
  g.s.map Pair.b
#align generalized_continued_fraction.partial_denominators GeneralizedContinuedFraction.partialDenominators

/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def TerminatedAt (g : GeneralizedContinuedFraction α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n
#align generalized_continued_fraction.terminated_at GeneralizedContinuedFraction.TerminatedAt

/-- It is decidable whether a gcf terminated at a given position. -/
instance terminatedAtDecidable (g : GeneralizedContinuedFraction α) (n : ℕ) :
    Decidable (g.TerminatedAt n) := by
  unfold TerminatedAt
  infer_instance
#align generalized_continued_fraction.terminated_at_decidable GeneralizedContinuedFraction.terminatedAtDecidable

/-- A gcf terminates if its sequence terminates. -/
def Terminates (g : GeneralizedContinuedFraction α) : Prop :=
  g.s.Terminates
#align generalized_continued_fraction.terminates GeneralizedContinuedFraction.Terminates

/-- A generalized continued fraction is a *simple continued fraction* if all partial numerators are
equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
-/
class IsSimpleContinuedFraction [One α]
    (g : GeneralizedContinuedFraction α) : Prop where
  /- All partial numerators are equal to one. -/
  partNum_eq_one : ∀ {n aₙ}, g.partialNumerators.get? n = some aₙ → aₙ = 1
#align generalized_continued_fraction.is_simple_continued_fraction GeneralizedContinuedFraction.IsSimpleContinuedFraction

#noalign simple_continued_fraction

instance IsSimpleContinuedFraction.ofInteger [One α] (a : α) :
    (ofInteger a).IsSimpleContinuedFraction where
  partNum_eq_one h := nomatch h
#align simple_continued_fraction.of_integer GeneralizedContinuedFraction.IsSimpleContinuedFraction.ofInteger

#noalign simple_continued_fraction.inhabited

#noalign simple_continued_fraction.has_coe_to_generalized_continued_fraction

#noalign simple_continued_fraction.coe_to_generalized_continued_fraction

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if all partial denominators
`bᵢ` are positive, i.e. `0 < bᵢ`.
-/
class IsContinuedFraction [One α] [Zero α] [LT α]
    (g : GeneralizedContinuedFraction α) extends IsSimpleContinuedFraction g : Prop where
  /- All partial denominator are positive. -/
  zero_lt_partDenom : ∀ {n bₙ}, g.partialDenominators.get? n = some bₙ → 0 < bₙ
#align simple_continued_fraction.is_continued_fraction GeneralizedContinuedFraction.IsContinuedFraction

#noalign continued_fraction

instance IsContinuedFraction.ofInteger [One α] [Zero α] [LT α] (a : α) :
    (ofInteger a).IsContinuedFraction where
  zero_lt_partDenom h := nomatch h
#align continued_fraction.of_integer GeneralizedContinuedFraction.IsContinuedFraction.ofInteger

#noalign continued_fraction.inhabited

#noalign continued_fraction.has_coe_to_simple_continued_fraction

#noalign continued_fraction.coe_to_simple_continued_fraction

#noalign continued_fraction.has_coe_to_generalized_continued_fraction

#noalign continued_fraction.coe_to_generalized_continued_fraction

/--
A continued fraction is an *integer continued fraction* (icf) if the head term and all partial
denominators `bᵢ` are integer.
-/
class IsIntegerContinuedFraction [One α] [Zero α] [LT α] [IntCast α]
    (g : GeneralizedContinuedFraction α) extends IsContinuedFraction g : Prop where
  /- The head term is integer. -/
  h_eq_int : ∃ (m : ℤ), g.h = m
  /- All partial denominator are integer. -/
  partDenom_eq_int : ∀ {n bₙ}, g.partialDenominators.get? n = some bₙ → ∃ (m : ℤ), bₙ = m

instance IsIntegerContinuedFraction.ofInteger [One α] [Zero α] [LT α] [IntCast α] (n : ℤ) :
    (ofInteger (n : α)).IsIntegerContinuedFraction where
  h_eq_int := ⟨n, rfl⟩
  partDenom_eq_int h := nomatch h

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`Algebra.ContinuedFractions.ConvergentsEquiv`.
-/

-- Fix a division ring for the computations.
variable {K : Type*} [DivisionRing K]

/-!
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, Bₙ` are called the *nth continuants*, `Aₙ` the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/

#noalign generalized_continued_fraction.next_numerator

#noalign generalized_continued_fraction.next_denominator

#noalign generalized_continued_fraction.next_continuants

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def continuantsAux (g : GeneralizedContinuedFraction K) : ℕ → Pair K
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => continuantsAux g (n + 1)
    | some gp =>
      ⟨gp.b * (continuantsAux g (n + 1)).a + gp.a * (continuantsAux g n).a,
        gp.b * (continuantsAux g (n + 1)).b + gp.a * (continuantsAux g n).b⟩
#align generalized_continued_fraction.continuants_aux GeneralizedContinuedFraction.continuantsAux

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def continuants (g : GeneralizedContinuedFraction K) (n : ℕ) : Pair K :=
  g.continuantsAux (n + 1)
#align generalized_continued_fraction.continuants GeneralizedContinuedFraction.continuants

/-- Returns the numerators `Aₙ` of `g`. -/
def numerators (g : GeneralizedContinuedFraction K) (n : ℕ) : K :=
  (g.continuants n).a
#align generalized_continued_fraction.numerators GeneralizedContinuedFraction.numerators

/-- Returns the denominators `Bₙ` of `g`. -/
def denominators (g : GeneralizedContinuedFraction K) (n : ℕ) : K :=
  (g.continuants n).b
#align generalized_continued_fraction.denominators GeneralizedContinuedFraction.denominators

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convergents (g : GeneralizedContinuedFraction K) (n : ℕ) : K :=
  g.numerators n / g.denominators n
#align generalized_continued_fraction.convergents GeneralizedContinuedFraction.convergents

/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convergents'Aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convergents'Aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convergents'Aux : Stream'.Seq (Pair K) → ℕ → K
  | _, 0 => 0
  | s, n + 1 =>
    match s.head with
    | none => 0
    | some gp => gp.a / (gp.b + convergents'Aux s.tail n)
#align generalized_continued_fraction.convergents'_aux GeneralizedContinuedFraction.convergents'Aux

/-- Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convergents' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convergents' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convergents' (g : GeneralizedContinuedFraction K) (n : ℕ) : K :=
  g.h + convergents'Aux g.s n
#align generalized_continued_fraction.convergents' GeneralizedContinuedFraction.convergents'

end GeneralizedContinuedFraction
