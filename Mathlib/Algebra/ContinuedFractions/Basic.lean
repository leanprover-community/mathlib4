/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann, Miyahara Kō
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Order.Filter.Partial
import Mathlib.Topology.Basic

#align_import algebra.continued_fractions.basic from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs) and finite gcfs
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of finite gcfs using the recurrence relation in `eval?`
5. Computation of finite gcfs by directly evaluating the fraction in `evalF?`
6. Computation of potentially infinite gcfs

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

universe u v w

open Function Stream'.Seq Filter

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
For convenience, one often writes `CF[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
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

#noalign generalized_continued_fraction.of_integer

instance [Inhabited α] : Inhabited (GCF α) where
  default := ⟨default, nil⟩

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

instance [Inhabited α] : Inhabited (FGCF α) where
  default := ⟨default, []⟩

/-- Lift a fgcf to a gcf by casting a list to a sequence. -/
@[coe, simps]
def toGCF (f : FGCF α) : GCF α where
  h := f.h
  s := ↑f.l

instance : Coe (FGCF α) (GCF α) where
  coe := toGCF

theorem toGCF_injective : Injective ((↑) : FGCF α → GCF α) := by
  rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ h
  simpa [toGCF] using h

@[simp, norm_cast]
theorem toGCF_inj {f₁ f₂ : FGCF α} : (↑f₁ : GCF α) = ↑f₂ ↔ f₁ = f₂ :=
  toGCF_injective.eq_iff

@[simp]
theorem toGCF_terminates (f : FGCF α) : (↑f : GCF α).Terminates := by simp [GCF.Terminates]

theorem _root_.GCF.exists_eq_FGCF_iff {g : GCF α} : (∃ f : FGCF α, ↑f = g) ↔ g.Terminates where
  mp  := by rintro ⟨f, rfl⟩; exact f.toGCF_terminates
  mpr := by
    intro hg; rcases g with ⟨h, s⟩
    use ⟨h, s.toList hg⟩
    simp [comp, toGCF]

instance : CanLift (GCF α) (FGCF α) (↑) GCF.Terminates where
  prf _ h := GCF.exists_eq_FGCF_iff.mpr h

/-- Take the head term and the first `n` pairs of a partial numerator and denominator. -/
@[simps]
def _root_.GCF.take (g : GCF α) (n : ℕ) : FGCF α where
  h := g.h
  l := g.s.take n

open Std in
instance [Repr α] : Repr (FGCF α) where
  reprPrec a _ :=
    let _ : ToFormat α := ⟨repr⟩
    match a with
    | { h, l := [] } => Format.bracket "CF[" (format h) "]"
    | { h, l := as } =>
      Format.bracket "CF["
        (format h ++ (";" ++ Format.line) ++ Format.joinSep as ("," ++ Format.line)) "]"

end FGCF

open FGCF hiding toGCF

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
#align generalized_continued_fraction.is_simple_continued_fraction GCF.IsSCF

/-- A *simple continued fraction* (scf) is a generalized continued fraction (gcf) whose partial
numerators are equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
For convenience, one often writes `CF[h; b₀, b₁, b₂,...]`.
In contrast to generalized continued fraction, We store only partial denominators in a sequence `s`.
 -/
@[ext]
structure SCF (α : Type*) where
  /-- Head term -/
  protected h : α
  /-- Sequence of partial denominators. -/
  protected s : Stream'.Seq α
#align simple_continued_fraction SCF

namespace SCF

variable [One α]

#noalign simple_continued_fraction.of_integer

instance [Inhabited α] : Inhabited (SCF α) where
  default := ⟨default, nil⟩

/-- Lift a scf to a gcf by adding `1`s as partial numerators. -/
@[coe, simps]
def toGCF (s : SCF α) : GCF α where
  h := s.h
  s := s.s.map ((1, ·))

instance : Coe (SCF α) (GCF α) where
  coe := toGCF

theorem toGCF_injective : Injective ((↑) : SCF α → GCF α) := by
  rintro ⟨h₁, s₁⟩ ⟨h₂, s₂⟩ h
  have hi : Injective (Stream'.Seq.map (((1, ·)) : α → α × α)) :=
    map_injective (Prod.mk.inj_left 1)
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
    simp [comp, toGCF]
    convert Stream'.Seq.map_id s using 1
    symm; apply Stream'.Seq.map_congr
    simpa [IsSCF, partNums] using hg

instance : CanLift (GCF α) (SCF α) (↑) IsSCF where
  prf _ h := GCF.exists_eq_SCF_iff.mpr h

#noalign simple_continued_fraction.coe_to_generalized_continued_fraction

end SCF

open SCF

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if the head term is integer
and all partial denominators `bᵢ` are positive naturals.
-/
def SCF.IsCF [NatCast α] [IntCast α] (s : SCF α) : Prop :=
  (∃ n : ℤ, ↑n = s.h) ∧ (∀ bₙ ∈ s.s, ∃ p : ℕ+, ↑p = bₙ)
#align simple_continued_fraction.is_continued_fraction SCF.IsCF

/-- A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose head term
is integer and all partial denominators are positive naturals.
We represent this by an integer `h` and a sequence of positive naturals `s`.
-/
@[ext]
structure CF (α : Type*) where
  /-- Head term -/
  protected h : ℤ
  /-- Sequence of partial denominators. -/
  protected s : Stream'.Seq ℕ+
#align continued_fraction CF

namespace CF

#noalign continued_fraction.of_integer

instance : Inhabited (CF α) where
  default := ⟨0, nil⟩

/-- Lift a scf to a gcf by casting. -/
@[coe, simps]
def toSCF [NatCast α] [IntCast α] (c : CF α) : SCF α where
  h  := ↑c.h
  s := c.s.map (↑)

instance [NatCast α] [IntCast α] : Coe (CF α) (SCF α) where
  coe := toSCF

theorem toSCF_injective [AddGroupWithOne α] [CharZero α] : Injective ((↑) : CF α → SCF α) := by
  rintro ⟨h₁, s₁⟩ ⟨h₂, s₂⟩ h
  have hi : Injective (Stream'.Seq.map (((↑)) : ℕ+ → α)) :=
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
    rcases s with ⟨h, s⟩; rintro ⟨⟨sh, rfl⟩, hs⟩
    use ⟨sh, s.map (invFun (↑))⟩
    simp [comp, toSCF]
    convert Stream'.Seq.map_id s using 1
    symm; apply Stream'.Seq.map_congr; intro a ha
    simp [invFun_eq (hs a ha)]

instance [AddGroupWithOne α] [CharZero α] : CanLift (SCF α) (CF α) (↑) IsCF where
  prf _ h := SCF.exists_eq_CF_iff.mpr h

#noalign continued_fraction.coe_to_simple_continued_fraction
#noalign continued_fraction.has_coe_to_generalized_continued_fraction
#noalign continued_fraction.coe_to_generalized_continued_fraction

end CF

open CF

variable {K : Type*} [DivisionRing K]

/-!
### Computation of finite generalized continued fractions

We now define how to evaluate finite gcfs. There are two standard ways to do this:
directly evaluating the fraction described by the gcf or using a recurrence relation.
These computations are equivalent as shown in `Algebra.ContinuedFractions.EvalEquiv`.
-/

namespace FGCF

/-!
We start with the definition of the recurrence relation. Given a finite gcf `f`, for all `n ≥ 1`,
we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

The value of `f` is given by `Aₙ / Bₙ` where `Aₙ, Bₙ` are the last values.
-/

#noalign generalized_continued_fraction.next_numerator
#noalign generalized_continued_fraction.next_denominator

/--
Returns the next continuants `((Aₙ₋₁, Bₙ₋₁), (Aₙ, Bₙ))` using these:
- `Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`
- `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`
where `c` is `(aₙ₋₁, bₙ₋₁)` and `p` is `((Aₙ₋₂, Bₙ₋₂), (Aₙ₋₁, Bₙ₋₁))`.
We should give previous continuants because it is used in the next calculation.
-/
@[simps]
def nextContinuants (p : (K × K) × (K × K)) (c : K × K) : (K × K) × (K × K) :=
  (p.2, (c.2 * p.2.1 + c.1 * p.1.1, c.2 * p.2.2 + c.1 * p.1.2))
#align generalized_continued_fraction.next_continuants FGCF.nextContinuantsₓ

#noalign generalized_continued_fraction.continuants_aux

/-- Returns the last continuant `(Aₙ, Bₙ)` of `f`. -/
def continuant (f : FGCF K) : K × K :=
  Prod.snd (f.l.foldl nextContinuants ((1, 0), (f.h, 1)))
#align generalized_continued_fraction.continuants FGCF.continuantₓ

/-- Returns the last numerator `Aₙ` of `f`. -/
abbrev numerator (f : FGCF K) : K :=
  f.continuant.1
#align generalized_continued_fraction.numerators FGCF.numeratorₓ

/-- Returns the last denominator `Bₙ` of `f`. -/
abbrev denominator (f : FGCF K) : K :=
  f.continuant.2
#align generalized_continued_fraction.denominators FGCF.denominatorₓ

/-- Returns the value of `f` using a recurrence relation.
This is not defined if the denominator is `0` because the convergence of gcfs is given by discarding
convergents whose denominator is `0`. -/
def eval? [DecidableEq K] (f : FGCF K) : Option K :=
  if f.denominator = 0 then
    none
  else
    some (f.numerator / f.denominator)

/-- Returns the value of the fraction part of fgcf by directly evaluating the fraction. For example:
```lean
  evalF? CF[9; (1, 2), (3, 4), (5, 6)]
= 9 + 1 / (2 + 3 / (4 + 5 / 6))
= 713 / 76
```
A `0` in denominators is handled specially to match the value to `eval?`, and the value can be
undefined by this. Refer to `evalF?.loop` for more detail.
-/
def evalF? [DecidableEq K] (f : FGCF K) : Option K :=
  (loop f.l).join.map (f.h + ·)
where
  /-- Returns the value of `f` by directly evaluating the fraction.
  If `0` is appreared in the denominator and its numerator isn't `0`, the fraction is dealed as
  infinity (`some none`), if its numerator is also `0`, the fraction is dealed as undefined (`none`)
  and stop latter calculations. For example:
  ```lean
    evalF?.loop [(1, 2), (3, 4), (5, 6)]
  = 1 / (2 + 3 / (4 + 5 / 6))
  = 29 / 76
    evalF?.loop [(1, 2), (3, 4), (5, 0)]
  = 1 / (2 + 3 / (4 + 5 / 0))
  = 1 / (2 + 3 / ∞)
  = 1 / 2
    evalF?.loop [(1, 2), (0, 4), (-4, 1)]
  = 1 / (2 + 0 / (4 + -4 / 1))
  = 1 / (2 + 0 / 0)
  = undefined
  ```
  -/
  @[simp]
  loop [DecidableEq K] : List (K × K) → Option (Option K)
    | []     => some (some 0)
    | p :: l =>
      (loop l).bind
        fun
        | some k =>
          if p.2 + k = 0 then
            if p.1 = 0 then
              none
            else
              some none
          else
            some (some (p.1 / (p.2 + k)))
        | none   => some (some 0)
#align generalized_continued_fraction.convergents' FGCF.evalF?ₓ
#align generalized_continued_fraction.convergents'_aux FGCF.evalF?.loopₓ

end FGCF

/-!
### Computation of potentially infinite gcfs

The value of potentially infinite gcfs is given by the limit of the value of its head finite gcfs.
If the gcf is finite, the value given by this way coincides with the value as finite gcfs as shown
in `Algebra.ContinuedFractions.Computation.CorrectnessTerminating`.
-/

namespace GCF

/-- Returns the convergents of `g` by the value of `g.take n`. This should be partial function
because the convergence of gcfs is given by discarding convergents whose denominator is `0`. -/
def convergents [DecidableEq K] (g : GCF K) : ℕ →. K :=
  fun n => ↑(g.take n).eval?
#align generalized_continued_fraction.convergents GCF.convergentsₓ

/-- The value of potentially infinite gcfs is given by the limit of the value of its head finite
gcfs. -/
def HasValue [DecidableEq K] [TopologicalSpace K] (g : GCF K) (v : K) : Prop :=
  PTendsto g.convergents atTop (nhds v)

end GCF
