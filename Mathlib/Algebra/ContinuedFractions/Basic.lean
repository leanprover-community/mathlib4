/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann, Miyahara Kō
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Order.Filter.Partial
import Mathlib.Topology.Basic
import Mathlib.Data.Int.CharZero

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

open Function Seq' Filter

/-! ### Definitions -/

#align generalized_continued_fraction.pair Prod
#align generalized_continued_fraction.pair.has_repr instReprProdOfReprTupleₓ
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
  protected s : Seq' (α × α)
#align generalized_continued_fraction GCF
#align generalized_continued_fraction.ext_iff GCF.ext_iff
#align generalized_continued_fraction.ext GCF.ext

variable {α : Type*}

namespace GCF

#noalign generalized_continued_fraction.of_integer

instance [Inhabited α] : Inhabited (GCF α) where
  default := ⟨default, nil⟩

#noalign generalized_continued_fraction.partial_numerators

#noalign generalized_continued_fraction.partial_denominators

#noalign generalized_continued_fraction.terminated_at

#noalign generalized_continued_fraction.terminated_at_decidable

#noalign generalized_continued_fraction.terminates

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

@[simp, norm_cast]
theorem toGCF_mk (h : α) (l : List (α × α)) : (↑(⟨h, l⟩ : FGCF α) : GCF α) = ⟨h, ↑l⟩ :=
  rfl

theorem toGCF_injective : Injective ((↑) : FGCF α → GCF α) := by
  rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ h
  simpa using h

@[simp, norm_cast]
theorem toGCF_inj {f₁ f₂ : FGCF α} : (↑f₁ : GCF α) = ↑f₂ ↔ f₁ = f₂ :=
  toGCF_injective.eq_iff

theorem _root_.GCF.exists_eq_FGCF_iff {g : GCF α} : (∃ f : FGCF α, ↑f = g) ↔ g.s.Terminates where
  mp  := by rintro ⟨f, rfl⟩; simp
  mpr := by
    intro hg; rcases g with ⟨h, s⟩
    use ⟨h, s.toList hg⟩
    simp [comp]

instance : CanLift (GCF α) (FGCF α) (↑) (·.s.Terminates) where
  prf _ h := GCF.exists_eq_FGCF_iff.mpr h

/-- Take the head term and the first `n` pairs of a partial numerator and denominator. -/
@[simps]
def _root_.GCF.take (n : ℕ) (g : GCF α) : FGCF α where
  h := g.h
  l := g.s.take n

@[simp]
theorem _root_.GCF.take_mk (n : ℕ) (h : α) (s : Seq' (α × α)) : GCF.take n ⟨h, s⟩ = ⟨h, s.take n⟩ :=
  rfl

def hAppend (f : FGCF α) (l : List (α × α)) : FGCF α where
  h := f.h
  l := f.l ++ l

instance : HAppend (FGCF α) (List (α × α)) (FGCF α) where
  hAppend := hAppend

theorem hAppend_def (f : FGCF α) (l : List (α × α)) : f ++ l = ⟨f.h, f.l ++ l⟩ :=
  rfl

@[simp]
theorem hAppend_h (f : FGCF α) (l : List (α × α)) : (f ++ l).h = f.h :=
  rfl

@[simp]
theorem hAppend_l (f : FGCF α) (l : List (α × α)) : (f ++ l).l = f.l ++ l :=
  rfl

@[simp]
theorem mk_hAppend (h : α) (l₁ l₂ : List (α × α)) : (⟨h, l₁⟩ : FGCF α) ++ l₂ = ⟨h, l₁ ++ l₂⟩ :=
  rfl

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
def GCF.IsSCF [One α] (g : GCF α) : Prop := ∀ ⦃a b⦄, (a, b) ∈ g.s → a = 1
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
  protected s : Seq' α
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

@[simp]
theorem toGCF_mk (h : α) (s : Seq' α) : (↑(⟨h, s⟩ : SCF α) : GCF α) = ⟨h, s.map ((1, ·))⟩ :=
  rfl

theorem toGCF_injective : Injective ((↑) : SCF α → GCF α) := by
  rintro ⟨h₁, s₁⟩ ⟨h₂, s₂⟩ h
  have hi : Injective (Seq'.map (((1, ·)) : α → α × α)) :=
    Seq'.map_injective (Prod.mk.inj_left 1)
  simpa [hi.eq_iff] using h

@[simp, norm_cast]
theorem toGCF_inj {s₁ s₂ : SCF α} : (↑s₁ : GCF α) = ↑s₂ ↔ s₁ = s₂ :=
  toGCF_injective.eq_iff

@[simp]
theorem toGCF_isSCF (s : SCF α) : (↑s : GCF α).IsSCF := by simp [IsSCF]

theorem _root_.GCF.exists_eq_SCF_iff {g : GCF α} : (∃ s : SCF α, ↑s = g) ↔ g.IsSCF where
  mp  := by rintro ⟨s, rfl⟩; exact s.toGCF_isSCF
  mpr := by
    intro hg; rcases g with ⟨h, s⟩
    use ⟨h, s.map Prod.snd⟩
    simp [comp]
    convert Seq'.map_id s using 1
    symm; apply Seq'.map_congr
    simpa [IsSCF] using hg

instance : CanLift (GCF α) (SCF α) (↑) IsSCF where
  prf _ h := GCF.exists_eq_SCF_iff.mpr h

#noalign simple_continued_fraction.coe_to_generalized_continued_fraction

end SCF

open SCF

@[ext]
structure FSCF (α : Type*) where
  protected h : α
  protected l : List α

namespace FSCF

variable [One α]

instance [Inhabited α] : Inhabited (FSCF α) where
  default := ⟨default, []⟩

@[coe, simps]
def toSCF (f : FSCF α) : SCF α where
  h := f.h
  s := ↑f.l

instance : Coe (FSCF α) (SCF α) where
  coe := toSCF

@[simp, norm_cast]
theorem toSCF_mk (h : α) (l : List α) : (↑(⟨h, l⟩ : FSCF α) : SCF α) = ⟨h, ↑l⟩ :=
  rfl

theorem toSCF_injective : Injective ((↑) : FSCF α → SCF α) := by
  rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ h
  simpa using h

@[simp, norm_cast]
theorem toSCF_inj {f₁ f₂ : FSCF α} : (↑f₁ : SCF α) = ↑f₂ ↔ f₁ = f₂ :=
  toSCF_injective.eq_iff

theorem _root_.SCF.exists_eq_FSCF_iff {s : SCF α} : (∃ f : FSCF α, ↑f = s) ↔ s.s.Terminates where
  mp  := by rintro ⟨f, rfl⟩; simp
  mpr := by
    intro hs; rcases s with ⟨h, s⟩
    use ⟨h, s.toList hs⟩
    simp [comp]

instance : CanLift (SCF α) (FSCF α) (↑) (·.s.Terminates) where
  prf _ h := SCF.exists_eq_FSCF_iff.mpr h

@[coe, simps]
def toFGCF (f : FSCF α) : FGCF α where
  h := f.h
  l := f.l.map ((1, ·))

instance : Coe (FSCF α) (FGCF α) where
  coe := toFGCF

@[simp]
theorem toFGCF_mk (h : α) (l : List α) : (↑(⟨h, l⟩ : FSCF α) : FGCF α) = ⟨h, l.map ((1, ·))⟩ :=
  rfl

theorem toFGCF_injective : Injective ((↑) : FSCF α → FGCF α) := by
  rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ h
  have hi : Injective (List.map (((1, ·)) : α → α × α)) :=
    List.map_injective_iff.mpr (Prod.mk.inj_left 1)
  simpa [hi.eq_iff] using h

@[simp, norm_cast]
theorem toFGCF_inj {f₁ f₂ : FSCF α} : (↑f₁ : FGCF α) = ↑f₂ ↔ f₁ = f₂ :=
  toFGCF_injective.eq_iff

theorem toFGCF_toGCF_eq_toSCF_toGCF (f : FSCF α) :
    (↑(↑f : FGCF α) : GCF α) = (↑(↑f : SCF α) : GCF α) := by
  rcases f with ⟨h, l⟩
  simp

theorem _root_.FGCF.exists_eq_FSCF_iff {f : FGCF α} :
    (∃ f' : FSCF α, ↑f' = f) ↔ (↑f : GCF α).IsSCF where
  mp  := by
    rintro ⟨f', rfl⟩
    rw [toFGCF_toGCF_eq_toSCF_toGCF]
    exact (↑f' : SCF α).toGCF_isSCF
  mpr := by
    intro hf; rcases f with ⟨h, l⟩
    use ⟨h, l.map Prod.snd⟩
    simp [comp]
    convert List.map_id l using 1
    symm; apply List.map_congr
    simpa [IsSCF] using hf

instance : CanLift (FGCF α) (FSCF α) (↑) (fun f => (↑f : GCF α).IsSCF) where
  prf _ h := FGCF.exists_eq_FSCF_iff.mpr h

@[simps]
def _root_.SCF.take (n : ℕ) (s : SCF α) : FSCF α where
  h := s.h
  l := s.s.take n

@[simp]
theorem _root_.SCF.take_mk (n : ℕ) (h : α) (s : Seq' α) : SCF.take n ⟨h, s⟩ = ⟨h, s.take n⟩ :=
  rfl

@[simp, norm_cast]
theorem _root_.SCF.take_toGCF (n : ℕ) (s : SCF α) :
    GCF.take n (↑s : GCF α) = ↑(SCF.take n s) := by
  simp [GCF.take, SCF.take]

def hAppend (f : FSCF α) (l : List α) : FSCF α where
  h := f.h
  l := f.l ++ l

instance : HAppend (FSCF α) (List α) (FSCF α) where
  hAppend := hAppend

theorem hAppend_def (f : FSCF α) (l : List α) : f ++ l = ⟨f.h, f.l ++ l⟩ :=
  rfl

@[simp]
theorem hAppend_h (f : FSCF α) (l : List α) : (f ++ l).h = f.h :=
  rfl

@[simp]
theorem hAppend_l (f : FSCF α) (l : List α) : (f ++ l).l = f.l ++ l :=
  rfl

@[simp]
theorem mk_hAppend (h : α) (l₁ l₂ : List α) : (⟨h, l₁⟩ : FSCF α) ++ l₂ = ⟨h, l₁ ++ l₂⟩ :=
  rfl

@[simp]
theorem toFGCF_hAppend (f : FSCF α) (l : List α) :
    (↑(f ++ l) : FGCF α) = (↑f : FGCF α) ++ l.map (((1 : α), ·)) := by
  simp [FGCF.hAppend_def, FSCF.hAppend_def]

open Std in
instance [Repr α] : Repr (FSCF α) where
  reprPrec a _ :=
    let _ : ToFormat α := ⟨repr⟩
    match a with
    | { h, l := [] } => Format.bracket "CF[" (format h) "]"
    | { h, l := as } =>
      Format.bracket "CF["
        (format h ++ (";" ++ Format.line) ++ Format.joinSep as ("," ++ Format.line)) "]"

end FSCF

open FSCF hiding toSCF toFGCF

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if the head term is integer
and all partial denominators `bᵢ` are positive naturals.
-/
def SCF.IsCF [NatCast α] [IntCast α] (s : SCF α) : Prop :=
  (∃ n : ℤ, ↑n = s.h) ∧ (∀ {b}, b ∈ s.s → ∃ p : ℕ+, ↑p = b)
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
  protected s : Seq' ℕ+
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

@[simp]
theorem toSCF_mk [NatCast α] [IntCast α] (h : ℤ) (s : Seq' ℕ+) :
    (↑(⟨h, s⟩ : CF α) : SCF α) = ⟨h, s.map (↑)⟩ :=
  rfl

theorem toSCF_injective [AddGroupWithOne α] [CharZero α] : Injective ((↑) : CF α → SCF α) := by
  rintro ⟨h₁, s₁⟩ ⟨h₂, s₂⟩ h
  have hi : Injective (Seq'.map (((↑)) : ℕ+ → α)) :=
    Seq'.map_injective (Nat.cast_injective.comp Subtype.val_injective)
  simpa [Int.cast_inj, hi.eq_iff] using h

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
    simp [comp]
    convert Seq'.map_id s using 1
    symm; apply Seq'.map_congr; intro a ha
    simp [invFun_eq (hs ha)]

instance [AddGroupWithOne α] [CharZero α] : CanLift (SCF α) (CF α) (↑) IsCF where
  prf _ h := SCF.exists_eq_CF_iff.mpr h

#noalign continued_fraction.coe_to_simple_continued_fraction
#noalign continued_fraction.has_coe_to_generalized_continued_fraction
#noalign continued_fraction.coe_to_generalized_continued_fraction

end CF

open CF

@[ext]
structure FCF (α : Type*) where
  protected h : ℤ
  protected l : List ℕ+

namespace FCF

variable [One α]

instance [Inhabited α] : Inhabited (FCF α) where
  default := ⟨default, []⟩

@[coe, simps]
def toCF (f : FCF α) : CF α where
  h := f.h
  s := ↑f.l

instance : Coe (FCF α) (CF α) where
  coe := toCF

@[simp, norm_cast]
theorem toCF_mk (h : ℤ) (l : List ℕ+) : (↑(⟨h, l⟩ : FCF α) : CF α) = ⟨↑h, ↑l⟩ :=
  rfl

theorem toCF_injective : Injective ((↑) : FCF α → CF α) := by
  rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ h
  simpa using h

@[simp, norm_cast]
theorem toCF_inj {f₁ f₂ : FCF α} : (↑f₁ : CF α) = ↑f₂ ↔ f₁ = f₂ :=
  toCF_injective.eq_iff

theorem _root_.CF.exists_eq_FCF_iff {c : CF α} : (∃ f : FCF α, ↑f = c) ↔ c.s.Terminates where
  mp  := by rintro ⟨f, rfl⟩; simp
  mpr := by
    intro hc; rcases c with ⟨h, s⟩
    use ⟨h, s.toList hc⟩
    simp [comp]

instance : CanLift (CF α) (FCF α) (↑) (·.s.Terminates) where
  prf _ h := CF.exists_eq_FCF_iff.mpr h

@[coe, simps]
def toFSCF [NatCast α] [IntCast α] (f : FCF α) : FSCF α where
  h := ↑f.h
  l := f.l.map (↑)

instance [NatCast α] [IntCast α] : Coe (FCF α) (FSCF α) where
  coe := toFSCF

@[simp]
theorem toFSCF_mk [NatCast α] [IntCast α] (h : ℤ) (l : List ℕ+) :
    (↑(⟨h, l⟩ : FCF α) : FSCF α) = ⟨↑h, l.map (↑)⟩ :=
  rfl

theorem toFSCF_injective [AddGroupWithOne α] [CharZero α] : Injective ((↑) : FCF α → FSCF α) := by
  rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ h
  have hi : Injective (List.map ((↑) : ℕ+ → α)) :=
    List.map_injective_iff.mpr (Nat.cast_injective.comp PNat.coe_injective)
  simpa [hi.eq_iff] using h

@[simp, norm_cast]
theorem toFSCF_inj [AddGroupWithOne α] [CharZero α] {f₁ f₂ : FCF α} :
    (↑f₁ : FSCF α) = ↑f₂ ↔ f₁ = f₂ :=
  toFSCF_injective.eq_iff

theorem toFSCF_toSCF_eq_toCF_toSCF [NatCast α] [IntCast α] (f : FCF α) :
    (↑(↑f : FSCF α) : SCF α) = (↑(↑f : CF α) : SCF α) := by
  rcases f with ⟨h, l⟩
  simp

theorem _root_.FSCF.exists_eq_FCF_iff [AddGroupWithOne α] [CharZero α] {f : FSCF α} :
    (∃ f' : FCF α, ↑f' = f) ↔ (↑f : SCF α).IsCF where
  mp  := by
    rintro ⟨f', rfl⟩
    rw [toFSCF_toSCF_eq_toCF_toSCF]
    exact (↑f' : CF α).toSCF_isCF
  mpr := by
    rcases f with ⟨h, l⟩; rintro ⟨⟨lh, rfl⟩, hl⟩
    use ⟨lh, l.map (invFun (↑))⟩
    simp [comp]
    convert List.map_id l using 1
    symm; apply List.map_congr; intro a ha
    simp [invFun_eq (hl (Seq'.mem_ofList.mpr ha))]

instance [AddGroupWithOne α] [CharZero α] :
    CanLift (FSCF α) (FCF α) (↑) (fun f => (↑f : SCF α).IsCF) where
  prf _ h := FSCF.exists_eq_FCF_iff.mpr h

@[simps]
def _root_.CF.take (n : ℕ) (c : CF α) : FCF α where
  h := c.h
  l := c.s.take n

@[simp]
theorem _root_.CF.take_mk (n : ℕ) (h : ℤ) (s : Seq' ℕ+) :
    CF.take n (⟨h, s⟩ : CF α) = ⟨h, s.take n⟩ :=
  rfl

@[simp, norm_cast]
theorem _root_.CF.take_toSCF [NatCast α] [IntCast α] (n : ℕ) (c : CF α) :
    SCF.take n (↑c : SCF α) = ↑(CF.take n c) := by
  simp [SCF.take, CF.take]

def hAppend (f : FCF α) (l : List ℕ+) : FCF α where
  h := f.h
  l := f.l ++ l

instance : HAppend (FCF α) (List ℕ+) (FCF α) where
  hAppend := hAppend

theorem hAppend_def (f : FCF α) (l : List ℕ+) : f ++ l = ⟨f.h, f.l ++ l⟩ :=
  rfl

@[simp]
theorem hAppend_h (f : FCF α) (l : List ℕ+) : (f ++ l).h = f.h :=
  rfl

@[simp]
theorem hAppend_l (f : FCF α) (l : List ℕ+) : (f ++ l).l = f.l ++ l :=
  rfl

@[simp]
theorem mk_hAppend (h : ℤ) (l₁ l₂ : List ℕ+) : (⟨h, l₁⟩ : FCF α) ++ l₂ = ⟨h, l₁ ++ l₂⟩ :=
  rfl

@[simp]
theorem toFSCF_hAppend [NatCast α] [IntCast α] (f : FCF α) (l : List ℕ+) :
    (↑(f ++ l) : FSCF α) = (↑f : FSCF α) ++ l.map ((↑) : ℕ+ → α) := by
  simp [FSCF.hAppend_def, FCF.hAppend_def]

open Std in
instance : Repr (FCF α) where
  reprPrec a _ :=
    let _ : ToFormat ℕ+ := ⟨repr⟩
    match a with
    | { h, l := [] } => Format.bracket "CF[" (format h) "]"
    | { h, l := as } =>
      Format.bracket "CF["
        (format h ++ (";" ++ Format.line) ++ Format.joinSep as ("," ++ Format.line)) "]"

end FCF

open FCF hiding toCF toFSCF

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
@[simp]
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
undefined by this. Refer to `evalF?.next?` for more detail.
-/
def evalF? [DecidableEq K] (f : FGCF K) : Option K :=
  (f.l.foldrM next? (some 0)).join.map (f.h + ·)
where
  /-- Returns the value of `f` by directly evaluating the fraction.
  If `0` is appreared in the denominator and its numerator isn't `0`, the fraction is dealed as
  infinity (`some none`), if its numerator is also `0`, the fraction is dealed as undefined (`none`)
  and stop latter calculations. For example:
  ```lean
    [(1, 2), (3, 4), (5, 6)].foldrM evalF?.next? (some 0)
  = 1 / (2 + 3 / (4 + 5 / 6))
  = 29 / 76
    [(1, 2), (3, 4), (5, 0)].foldrM evalF?.next? (some 0)
  = 1 / (2 + 3 / (4 + 5 / 0))
  = 1 / (2 + 3 / ∞)
  = 1 / 2
    [(1, 2), (0, 4), (-4, 1)].foldrM evalF?.next? (some 0)
  = 1 / (2 + 0 / (4 + -4 / 1))
  = 1 / (2 + 0 / 0)
  = undefined
  ```
  -/
  @[simp]
  next? [DecidableEq K] (p : K × K) : Option K → Option (Option K)
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
#align generalized_continued_fraction.convergents'_aux FGCF.evalF?.next?ₓ

end FGCF

namespace FCF

theorem nextContinuants.proof (k m : ℕ+) (n : ℕ) : 0 < ↑k * ↑m + n := calc
  (0 : ℕ) < ↑(k * m)    := PNat.pos _
  _       = ↑k * ↑m     := PNat.mul_coe _ _
  _       ≤ ↑k * ↑m + n := Nat.le_add_right _ _

@[simps]
def nextContinuants (p : (ℤ × ℕ) × (ℤ × ℕ+)) (n : ℕ+) : (ℤ × ℕ) × (ℤ × ℕ+) :=
  ((p.2.1, ↑p.2.2), (↑n * p.2.1 + p.1.1, ⟨↑n * ↑p.2.2 + p.1.2, nextContinuants.proof _ _ _⟩))

def continuant (f : FCF K) : ℤ × ℕ+ :=
  Prod.snd (f.l.foldl nextContinuants ((1, 0), (f.h, 1)))

abbrev numerator (f : FCF K) : ℤ :=
  f.continuant.1

abbrev denominator (f : FCF K) : ℕ+ :=
  f.continuant.2

def eval (f : FCF K) : ℚ :=
  mkRat f.numerator f.denominator

end FCF

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

namespace CF

def convergents (c : CF K) : ℕ → K :=
  fun n => ↑(c.take n).eval

end CF
