/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Data.Int.CharZero

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
4. Computation of convergents using the recurrence relation in `convergents`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in
`convergents'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them continued fraction in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

/-! ### Definitions -/

#align generalized_continued_fraction.pair Prod
#align generalized_continued_fraction.pair.has_repr instReprProdₓ
#align generalized_continued_fraction.pair.map Prod.mapₓ
#noalign generalized_continued_fraction.pair.has_coe_to_generalized_continued_fraction_pair
#noalign generalized_continued_fraction.pair.coe_to_generalized_continued_fraction_pair

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
We store the sequence of partial numerators and denominators in a sequence of pairs `s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
@[ext]
structure GCF (α : Type*) where
  /-- Head term -/
  protected h : α
  /-- Sequence of partial numerator and denominator pairs. -/
  protected s : Stream'.Seq (α × α)
#align generalized_continued_fraction GCF
#align generalized_continued_fraction.ext_iff GCF.ext_iff
#align generalized_continued_fraction.ext GCF.ext

variable {α : Type*}

namespace GCF

/-- Constructs a generalized continued fraction without fractional part. -/
@[simps]
def ofInteger (a : α) : GCF α where
  h := a
  s := Stream'.Seq.nil
#align generalized_continued_fraction.of_integer GCF.ofInteger

instance [Inhabited α] : Inhabited (GCF α) where
  default := ofInteger default

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partNums (g : GCF α) : Stream'.Seq α :=
  g.s.map Prod.fst
#align generalized_continued_fraction.partial_numerators GCF.partNums

/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partDenoms (g : GCF α) : Stream'.Seq α :=
  g.s.map Prod.snd
#align generalized_continued_fraction.partial_denominators GCF.partDenoms

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

end GCF

open GCF

/-- Partial numerators and denominators of a *finite generalised continued fraction* (fgcf) are
represented using list `l`. We use this type to define a value of a gcf by extending the operation
for fgcfs.
-/
@[ext]
structure FGCF (α : Type*) where
  /-- Head term -/
  protected h : α
  /-- List of partial numerator and denominator pairs. -/
  protected l : List (α × α)

namespace FGCF

/-- Constructs a finite generalized continued fraction without fractional part. -/
@[simps]
def ofInteger (a : α) : FGCF α where
  h := a
  l := []

instance [Inhabited α] : Inhabited (FGCF α) where
  default := ofInteger default

/-- Lift a fgcf to a gcf by casting a list to a sequence. -/
@[coe, simps]
def toGCF (f : FGCF α) : GCF α where
  h := f.h
  s := ↑f.l

instance : Coe (FGCF α) (GCF α) where
  coe := toGCF

/-- Take the head and the first `n` partial numerator and denominator pairs of the gcf. -/
@[simps]
def _root_.GCF.take (g : GCF α) (n : ℕ) : FGCF α where
  h := g.h
  l := g.s.take n

end FGCF

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
def GCF.IsSCF [One α] (g : GCF α) : Prop := ∀ aₙ ∈ g.partNums, aₙ = 1
#align generalized_continued_fraction.is_simple_continued_fraction GCF.IsSCFₓ

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
In contrast to generalized continued fraction, We store only partial denominators in a sequence
`sb`.
 -/
@[ext]
structure SCF (α : Type*) where
  /-- Head term -/
  protected h : α
  /-- Sequence of partial denominators. -/
  protected sb : Stream'.Seq α
#align simple_continued_fraction SCF

namespace SCF

variable [One α]

/-- Constructs a simple continued fraction without fractional part. -/
@[simps]
def ofInteger (a : α) : SCF α where
  h  := a
  sb := Stream'.Seq.nil
#align simple_continued_fraction.of_integer SCF.ofInteger

instance [Inhabited α] : Inhabited (SCF α) where
  default := ofInteger default

/-- Lift a scf to a gcf by adding `1`s as partial numerators. -/
@[coe, simps]
def toGCF (s : SCF α) : GCF α where
  h := s.h
  s := s.sb.map ((1, ·))

instance : Coe (SCF α) (GCF α) where
  coe := toGCF

theorem toGCF_injective : Function.Injective ((↑) : SCF α → GCF α) := by
  rintro ⟨h₁, s₁⟩ ⟨h₂, s₂⟩ h
  have hi : Function.Injective (Stream'.Seq.map (((1, ·)) : α → α × α)) :=
    Stream'.Seq.map_injective (Prod.mk.inj_left 1)
  simpa [hi.eq_iff, toGCF] using h

@[simp, norm_cast]
theorem toGCF_inj {s₁ s₂ : SCF α} : (↑s₁ : GCF α) = ↑s₂ ↔ s₁ = s₂ :=
  toGCF_injective.eq_iff

@[simp]
theorem toGCF_isSCF (s : SCF α) : (↑s : GCF α).IsSCF := by simp [IsSCF, partNums]

theorem _root_.GCF.exists_eq_SCF_iff {g : GCF α} : (∃ s : SCF α, ↑s = g) ↔ g.IsSCF where
  mp  := by rintro ⟨s, rfl⟩; exact s.toGCF_isSCF
  mpr := by
    intro hg; rcases g with ⟨h, s⟩
    use ⟨h, s.map Prod.snd⟩
    simp [Function.comp, toGCF]
    convert Stream'.Seq.map_id s using 1
    symm; apply Stream'.Seq.map_congr
    simpa [IsSCF, partNums] using hg

instance : CanLift (GCF α) (SCF α) (↑) IsSCF where
  prf _ h := GCF.exists_eq_SCF_iff.mpr h

@[simp, norm_cast]
theorem toGCF_ofInteger (a : α) : (↑(SCF.ofInteger a) : GCF α) = GCF.ofInteger a := by
  ext1 <;> simp

#noalign simple_continued_fraction.coe_to_generalized_continued_fraction

end SCF

open SCF

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if the head term is integer
and all partial denominators `bᵢ` are positive naturals.
-/
def SCF.IsCF [NatCast α] [IntCast α] (s : SCF α) : Prop :=
  (∃ n : ℤ, ↑n = s.h) ∧ (∀ bₙ ∈ s.sb, ∃ p : ℕ+, ↑p = bₙ)
#align simple_continued_fraction.is_continued_fraction SCF.IsCF

/-- A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose head term
is integer and all partial denominators are positive naturals.
We represent this by an integer `h` and a sequence of positive naturals `sb`.
-/
@[ext]
structure CF (α : Type*) where
  /-- Head term -/
  protected h : ℤ
  /-- Sequence of partial denominators. -/
  protected sb : Stream'.Seq ℕ+
#align continued_fraction CF

namespace CF

/-- Constructs a continued fraction without fractional part. -/
@[simps]
def ofInteger (a : ℤ) : CF α where
  h  := a
  sb := Stream'.Seq.nil
#align continued_fraction.of_integer CF.ofInteger

instance : Inhabited (CF α) where
  default := ofInteger 0

/-- Lift a scf to a gcf by casting. -/
@[coe, simps]
def toSCF [NatCast α] [IntCast α] (c : CF α) : SCF α where
  h  := ↑c.h
  sb := c.sb.map (↑)

instance [NatCast α] [IntCast α] : Coe (CF α) (SCF α) where
  coe := toSCF

theorem toSCF_injective [AddGroupWithOne α] [CharZero α] :
    Function.Injective ((↑) : CF α → SCF α) := by
  rintro ⟨h₁, sb₁⟩ ⟨h₂, sb₂⟩ h
  have hi : Function.Injective (Stream'.Seq.map (((↑)) : ℕ+ → α)) :=
    Stream'.Seq.map_injective (Nat.cast_injective.comp Subtype.val_injective)
  simpa [Int.cast_inj, hi.eq_iff, toSCF] using h

@[simp, norm_cast]
theorem toSCF_inj [AddGroupWithOne α] [CharZero α] {c₁ c₂ : CF α} :
    (↑c₁ : SCF α) = ↑c₂ ↔ c₁ = c₂ :=
  toSCF_injective.eq_iff

@[simp]
theorem toSCF_isCF [NatCast α] [IntCast α] (c : CF α) : (↑c : SCF α).IsCF := by simp [IsCF]

theorem _root_.SCF.exists_eq_CF_iff [AddGroupWithOne α] [CharZero α] {s : SCF α} :
    (∃ c : CF α, ↑c = s) ↔ s.IsCF where
  mp  := by rintro ⟨c, rfl⟩; exact c.toSCF_isCF
  mpr := by
    rcases s with ⟨h, sb⟩; rintro ⟨⟨sh, rfl⟩, hs⟩
    use ⟨sh, sb.map (Function.invFun (↑))⟩
    simp [Function.comp, toSCF]
    convert Stream'.Seq.map_id sb using 1
    symm; apply Stream'.Seq.map_congr; intro a ha
    simp [Function.invFun_eq (hs a ha)]

instance [AddGroupWithOne α] [CharZero α] : CanLift (SCF α) (CF α) (↑) IsCF where
  prf _ h := SCF.exists_eq_CF_iff.mpr h

@[simp, norm_cast]
theorem toSCF_ofInteger [NatCast α] [IntCast α] (a : ℤ) :
    (↑(CF.ofInteger a : CF α) : SCF α) = SCF.ofInteger ↑a := by
  ext1 <;> simp

#noalign continued_fraction.coe_to_simple_continued_fraction
#noalign continued_fraction.has_coe_to_generalized_continued_fraction
#noalign continued_fraction.coe_to_generalized_continued_fraction

end CF

open CF

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the fgcf or using a recurrence relation.
These computations are equivalent as shown in
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
def continuantsAux (g : GCF K) : ℕ → Pair K
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => continuantsAux g (n + 1)
    | some gp =>
      ⟨gp.b * (continuantsAux g (n + 1)).a + gp.a * (continuantsAux g n).a,
        gp.b * (continuantsAux g (n + 1)).b + gp.a * (continuantsAux g n).b⟩
#align generalized_continued_fraction.continuants_aux GCF.continuantsAux

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def continuants (g : GCF K) (n : ℕ) : Pair K :=
  g.continuantsAux (n + 1)
#align generalized_continued_fraction.continuants GCF.continuants

/-- Returns the numerators `Aₙ` of `g`. -/
def numerators (g : GCF K) (n : ℕ) : K :=
  (g.continuants n).a
#align generalized_continued_fraction.numerators GCF.numerators

/-- Returns the denominators `Bₙ` of `g`. -/
def denominators (g : GCF K) (n : ℕ) : K :=
  (g.continuants n).b
#align generalized_continued_fraction.denominators GCF.denominators

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convergents (g : GCF K) (n : ℕ) : K :=
  g.numerators n / g.denominators n
#align generalized_continued_fraction.convergents GCF.convergents

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
#align generalized_continued_fraction.convergents'_aux GCF.convergents'Aux

/-- Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convergents' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convergents' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convergents' (g : GCF K) (n : ℕ) : K :=
  g.h + convergents'Aux g.s n
#align generalized_continued_fraction.convergents' GCF.convergents'

end GCF
