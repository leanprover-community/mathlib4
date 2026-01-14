/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Data.Seq.Defs
import Mathlib.Algebra.Field.Defs

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convs`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in `convs'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them `ContFract` in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

-- Fix a carrier `α`.
variable (α : Type*)

/-!### Definitions -/

/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ, bᵢ⟩`. -/
structure GenContFract.Pair where
  /-- Partial numerator -/
  a : α
  /-- Partial denominator -/
  b : α
  deriving Inhabited

open GenContFract

/-! Interlude: define some expected coercions and instances. -/

namespace GenContFract.Pair

variable {α}

/-- Make a `GenContFract.Pair` printable. -/
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ ↦ "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

/-- Maps a function `f` on both components of a given pair. -/
def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩

section coe

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

/-- The coercion between numerator-denominator pairs happens componentwise. -/
@[coe]
def coeFn : Pair α → Pair β := map (↑)

/-- Coerce a pair by elementwise coercion. -/
instance : Coe (Pair α) (Pair β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) := rfl

end coe

end GenContFract.Pair

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
We store the sequence of partial numerators and denominators in a sequence of `GenContFract.Pair`s
`s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
@[ext]
structure GenContFract where
  /-- Head term -/
  h : α
  /-- Sequence of partial numerator and denominator pairs. -/
  s : Stream'.Seq <| Pair α

variable {α}

namespace GenContFract

/-- Constructs a generalized continued fraction without fractional part. -/
def ofInteger (a : α) : GenContFract α :=
  ⟨a, Stream'.Seq.nil⟩

instance [Inhabited α] : Inhabited (GenContFract α) :=
  ⟨ofInteger default⟩

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partNums (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.a

/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partDens (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.b

/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def TerminatedAt (g : GenContFract α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n

/-- It is decidable whether a gcf terminated at a given position. -/
instance terminatedAtDecidable (g : GenContFract α) (n : ℕ) :
    Decidable (g.TerminatedAt n) := by
  unfold TerminatedAt
  infer_instance

/-- A gcf terminates if its sequence terminates. -/
def Terminates (g : GenContFract α) : Prop :=
  g.s.Terminates

section coe

/-! Interlude: define some expected coercions. -/

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

/-- The coercion between `GenContFract` happens on the head term
and all numerator-denominator pairs componentwise. -/
@[coe]
def coeFn : GenContFract α → GenContFract β :=
  fun g ↦ ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

/-- Coerce a gcf by elementwise coercion. -/
instance : Coe (GenContFract α) (GenContFract β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toGenContFract {g : GenContFract α} :
    (g : GenContFract β) =
      ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩ := rfl

end coe

end GenContFract

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
def GenContFract.IsSimpContFract (g : GenContFract α)
    [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1

variable (α) in
/-- A *simple continued fraction* (scf) is a generalized continued fraction (gcf) whose partial
numerators are equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
For convenience, one often writes `[h; b₀, b₁, b₂,...]`.
It is encoded as the subtype of gcfs that satisfy `GenContFract.IsSimpContFract`.
-/
def SimpContFract [One α] :=
  { g : GenContFract α // g.IsSimpContFract }

-- Interlude: define some expected coercions.
namespace SimpContFract

variable [One α]

/-- Constructs a simple continued fraction without fractional part. -/
def ofInteger (a : α) : SimpContFract α :=
  ⟨GenContFract.ofInteger a, fun n aₙ h ↦ by cases h⟩

instance : Inhabited (SimpContFract α) :=
  ⟨ofInteger 1⟩

/-- Lift a scf to a gcf using the inclusion map. -/
instance : Coe (SimpContFract α) (GenContFract α) :=
  ⟨Subtype.val⟩

end SimpContFract

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if all partial denominators
`bᵢ` are positive, i.e. `0 < bᵢ`.
-/
def SimpContFract.IsContFract [One α] [Zero α] [LT α]
    (s : SimpContFract α) : Prop :=
  ∀ (n : ℕ) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ → 0 < bₙ

variable (α) in
/-- A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose partial
denominators are all positive. It is the subtype of scfs that satisfy `SimpContFract.IsContFract`.
-/
def ContFract [One α] [Zero α] [LT α] :=
  { s : SimpContFract α // s.IsContFract }

/-! Interlude: define some expected coercions. -/

namespace ContFract

variable [One α] [Zero α] [LT α]

/-- Constructs a continued fraction without fractional part. -/
def ofInteger (a : α) : ContFract α :=
  ⟨SimpContFract.ofInteger a, fun n bₙ h ↦ by cases h⟩

instance : Inhabited (ContFract α) :=
  ⟨ofInteger 0⟩

/-- Lift a cf to a scf using the inclusion map. -/
instance : Coe (ContFract α) (SimpContFract α) :=
  ⟨Subtype.val⟩

/-- Lift a cf to a scf using the inclusion map. -/
instance : Coe (ContFract α) (GenContFract α) :=
  ⟨fun c ↦ c.val⟩

end ContFract

namespace GenContFract

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

/-- Returns the next numerator `Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, where `predA` is `Aₙ₋₁`,
`ppredA` is `Aₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextNum (a b ppredA predA : K) : K :=
  b * predA + a * ppredA

/-- Returns the next denominator `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB

/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `nextNum` and `nextDen`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩`, `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def contsAux (g : GenContFract K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => contsAux g (n + 1)
    | some gp => nextConts gp.a gp.b (contsAux g n) (contsAux g (n + 1))

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def conts (g : GenContFract K) : Stream' (Pair K) :=
  g.contsAux.tail

/-- Returns the numerators `Aₙ` of `g`. -/
def nums (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.a

/-- Returns the denominators `Bₙ` of `g`. -/
def dens (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.b

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convs (g : GenContFract K) : Stream' K :=
  fun n : ℕ ↦ g.nums n / g.dens n

/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convs'Aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convs'Aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convs'Aux : Stream'.Seq (Pair K) → ℕ → K
  | _, 0 => 0
  | s, n + 1 =>
    match s.head with
    | none => 0
    | some gp => gp.a / (gp.b + convs'Aux s.tail n)

/-- Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convs' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convs' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convs' (g : GenContFract K) (n : ℕ) : K :=
  g.h + convs'Aux g.s n

end GenContFract
