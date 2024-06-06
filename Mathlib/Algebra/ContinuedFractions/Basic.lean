/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.PNat.Defs

#align_import algebra.continued_fractions.basic from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. Regular continued fractions (rcfs)
4. Computation of convergents using the recurrence relation in `convs`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in `convs'`.

## Implementation notes

We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

-- Fix a carrier `α`.
variable (α : Type*)

/-!### Definitions-/

-- Porting note: Originally `protected structure GCF.Pair`
/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ, bᵢ⟩`. -/
structure GCF.Pair where
  /-- Partial numerator -/
  a : α
  /-- Partial denominator -/
  b : α
  deriving Inhabited
#align generalized_continued_fraction.pair GCF.Pair

open GCF

/-! Interlude: define some expected coercions and instances. -/

namespace GCF.Pair

variable {α}

/-- Make a `GCF.Pair` printable. -/
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ ↦ "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

/-- Maps a function `f` on both components of a given pair. -/
def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩
#align generalized_continued_fraction.pair.map GCF.Pair.map

section coe

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

-- Porting note: added so we can add the `@[coe]` attribute
/-- The coercion between numerator-denominator pairs happens componentwise. -/
@[coe]
def coeFn : Pair α → Pair β := map (↑)

/-- Coerce a pair by elementwise coercion. -/
instance : Coe (Pair α) (Pair β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) := rfl
#align generalized_continued_fraction.pair.coe_to_generalized_continued_fraction_pair GCF.Pair.coe_toPair

end coe

end GCF.Pair

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
We store the sequence of partial numerators and denominators in a sequence of `GCF.Pair`s `s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
@[ext]
structure GCF where
  /-- Head term -/
  h : α
  /-- Sequence of partial numerator and denominator pairs. -/
  s : Stream'.Seq <| Pair α
#align generalized_continued_fraction GCF
#align generalized_continued_fraction.ext_iff GCF.ext_iff
#align generalized_continued_fraction.ext GCF.ext

variable {α}

namespace GCF

/-- Constructs a generalized continued fraction without fractional part. -/
def ofInteger (a : α) : GCF α :=
  ⟨a, Stream'.Seq.nil⟩
#align generalized_continued_fraction.of_integer GCF.ofInteger

instance [Inhabited α] : Inhabited (GCF α) :=
  ⟨ofInteger default⟩

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partNums (g : GCF α) : Stream'.Seq α :=
  g.s.map Pair.a
#align generalized_continued_fraction.partial_numerators GCF.partNums

/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partDens (g : GCF α) : Stream'.Seq α :=
  g.s.map Pair.b
#align generalized_continued_fraction.partial_denominators GCF.partDens

/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def TerminatedAt (g : GCF α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n
#align generalized_continued_fraction.terminated_at GCF.TerminatedAt

/-- It is decidable whether a gcf terminated at a given position. -/
instance terminatedAtDecidable (g : GCF α) (n : ℕ) :
    Decidable (g.TerminatedAt n) := by
  unfold TerminatedAt
  infer_instance
#align generalized_continued_fraction.terminated_at_decidable GCF.terminatedAtDecidable

/-- A gcf terminates if its sequence terminates. -/
def Terminates (g : GCF α) : Prop :=
  g.s.Terminates
#align generalized_continued_fraction.terminates GCF.Terminates

section coe

/-! Interlude: define some expected coercions. -/

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

-- Porting note: Added to put `@[coe]` attr on it.
/-- The coercion between `GCF` happens on the head term
and all numerator-denominator pairs componentwise. -/
@[coe]
def coeFn : GCF α → GCF β :=
  fun g ↦ ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

/-- Coerce a gcf by elementwise coercion. -/
instance : Coe (GCF α) (GCF β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toGCF {g : GCF α} :
    (g : GCF β) =
      ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩ := rfl
#align generalized_continued_fraction.coe_to_generalized_continued_fraction GCF.coe_toGCF

end coe

end GCF

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
def GCF.IsSCF (g : GCF α)
    [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1
#align generalized_continued_fraction.is_simple_continued_fraction GCF.IsSCF

variable (α)

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
It is encoded as the subtype of gcfs that satisfy `GCF.IsSCF`.
 -/
def SCF [One α] :=
  { g : GCF α // g.IsSCF }
#align simple_continued_fraction SCF

variable {α}

-- Interlude: define some expected coercions.
namespace SCF

variable [One α]

/-- Constructs a simple continued fraction without fractional part. -/
def ofInteger (a : α) : SCF α :=
  ⟨GCF.ofInteger a, fun n aₙ h ↦ by cases h⟩
#align simple_continued_fraction.of_integer SCF.ofInteger

instance : Inhabited (SCF α) :=
  ⟨ofInteger 1⟩

/-- Lift a scf to a gcf using the inclusion map. -/
instance : Coe (SCF α) (GCF α) :=
  -- Porting note: originally `by unfold SCF; infer_instance`
  ⟨Subtype.val⟩

-- Porting note: Syntactic tautology due to change in `Coe` above.
-- theorem coe_toGCF {s : SCF α} :
--     (↑s : GCF α) = s.val := rfl
#noalign simple_continued_fraction.coe_to_generalized_continued_fraction

end SCF

/--
A simple continued fraction is a *regular continued fraction* (rcf) if the head term is integer and
all partial denominators `bᵢ` are positive naturals.
-/
def SCF.IsRCF [One α] [NatCast α] [IntCast α]
    (s : SCF α) : Prop :=
  (∃ n : ℤ, (↑s : GCF α).h = ↑n) ∧
    ∀ (n : ℕ) (bₙ : α), (↑s : GCF α).partDens.get? n = some bₙ → ∃ n : ℕ+, bₙ = ↑n
#align simple_continued_fraction.is_continued_fraction SCF.IsRCF

variable (α)

/-- A *regular continued fraction* (rcf) is a simple continued fraction (scf) whose head term is
integer and all partial denominators are positive naturals. It is the subtype of scfs that satisfy
`SCF.IsRCF`.
 -/
def RCF [One α] [NatCast α] [IntCast α] :=
  { s : SCF α // s.IsRCF }
#align continued_fraction RCF

variable {α}

/-! Interlude: define some expected coercions. -/

namespace RCF

variable [One α] [NatCast α] [IntCast α]

/-- Constructs a continued fraction without fractional part. -/
def ofInteger (n : ℤ) : RCF α :=
  ⟨SCF.ofInteger (↑n : α), ⟨n, rfl⟩, fun n bₙ h ↦ by cases h⟩
#align continued_fraction.of_integer RCF.ofInteger

instance : Inhabited (RCF α) :=
  ⟨ofInteger 0⟩

/-- Lift a rcf to a scf using the inclusion map. -/
instance : Coe (RCF α) (SCF α) :=
  -- Porting note: originally `by unfold RCF; infer_instance`
  ⟨Subtype.val⟩

-- Porting note: Syntactic tautology due to change of `Coe` above.
-- theorem coe_to_simpleRCF {c : RCF α} :
--     (↑c : SCF α) = c.val := rfl
#noalign continued_fraction.coe_to_simple_continued_fraction

/-- Lift a rcf to a scf using the inclusion map. -/
instance : Coe (RCF α) (GCF α) :=
  ⟨fun c ↦ c.val⟩
  -- Porting note: was `fun c ↦ ↑(↑c : SCF α)`

-- Porting note: Syntactic tautology due to change of `Coe` above.
-- theorem coe_toGCF {c : RCF α} :
--     (↑c : GCF α) = c.val := rfl
#noalign continued_fraction.coe_to_generalized_continued_fraction

end RCF

namespace GCF

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For rcfs, these computations are equivalent as shown in
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
#align generalized_continued_fraction.next_numerator GCF.nextNum

/-- Returns the next denominator `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB
#align generalized_continued_fraction.next_denominator GCF.nextDen

/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `nextNum` and `nextDen`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩`, `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩
#align generalized_continued_fraction.next_continuants GCF.nextConts

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def contsAux (g : GCF K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => contsAux g (n + 1)
    | some gp => nextConts gp.a gp.b (contsAux g n) (contsAux g (n + 1))
#align generalized_continued_fraction.continuants_aux GCF.contsAux

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def conts (g : GCF K) : Stream' (Pair K) :=
  g.contsAux.tail
#align generalized_continued_fraction.continuants GCF.conts

/-- Returns the numerators `Aₙ` of `g`. -/
def nums (g : GCF K) : Stream' K :=
  g.conts.map Pair.a
#align generalized_continued_fraction.numerators GCF.nums

/-- Returns the denominators `Bₙ` of `g`. -/
def dens (g : GCF K) : Stream' K :=
  g.conts.map Pair.b
#align generalized_continued_fraction.denominators GCF.dens

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convs (g : GCF K) : Stream' K :=
  fun n : ℕ ↦ g.nums n / g.dens n
#align generalized_continued_fraction.convergents GCF.convs

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
#align generalized_continued_fraction.convergents'_aux GCF.convs'Aux

/-- Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convs' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convs' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convs' (g : GCF K) (n : ℕ) : K :=
  g.h + convs'Aux g.s n
#align generalized_continued_fraction.convergents' GCF.convs'

end GCF
