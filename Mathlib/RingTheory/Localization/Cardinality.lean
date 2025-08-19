/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.MonoidLocalization.Cardinality
import Mathlib.RingTheory.OreLocalization.Cardinality

/-!
# Cardinality of localizations

In this file, we establish the cardinality of localizations. In most cases, a localization has
cardinality equal to the base ring. If there are zero-divisors, however, this is no longer true -
for example, `ZMod 6` localized at `{2, 4}` is equal to `ZMod 3`, and if you have zero in your
submonoid, then your localization is trivial (see `IsLocalization.uniqueOfZeroMem`).

## Main statements

* `IsLocalization.cardinalMk_le`: A localization has cardinality no larger than the base ring.
* `IsLocalization.cardinalMk`: If you don't localize at zero-divisors, the localization of a ring
  has cardinality equal to its base ring.

-/


open Cardinal nonZeroDivisors

universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L] [Algebra R L]

namespace IsLocalization

theorem lift_cardinalMk_le (S : Submonoid R) [IsLocalization S L] :
    Cardinal.lift.{u} #L ≤ Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk_le S
  rwa [← lift_le.{v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

/-- A localization always has cardinality less than or equal to the base ring. -/
theorem cardinalMk_le {L : Type u} [CommSemiring L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] : #L ≤ #R := by
  simpa using lift_cardinalMk_le (L := L) S

end IsLocalization

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]

namespace Localization

theorem cardinalMk {S : Submonoid R} (hS : S ≤ R⁰) : #(Localization S) = #R := by
  apply OreLocalization.cardinalMk
  rwa [nonZeroDivisorsLeft_eq_nonZeroDivisors]

end Localization

namespace IsLocalization

variable (L)

theorem lift_cardinalMk (S : Submonoid R) [IsLocalization S L] (hS : S ≤ R⁰) :
    Cardinal.lift.{u} #L = Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk hS
  rwa [← lift_inj.{u, v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

/-- If you do not localize at any zero-divisors, localization preserves cardinality. -/
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] (hS : S ≤ R⁰) : #L = #R := by
  simpa using lift_cardinalMk L S hS

end IsLocalization

@[simp]
theorem Cardinal.mk_fractionRing (R : Type u) [CommRing R] : #(FractionRing R) = #R :=
  IsLocalization.cardinalMk (FractionRing R) R⁰ le_rfl

alias FractionRing.cardinalMk := Cardinal.mk_fractionRing

namespace IsFractionRing

variable (R L)

theorem lift_cardinalMk [IsFractionRing R L] : Cardinal.lift.{u} #L = Cardinal.lift.{v} #R :=
  IsLocalization.lift_cardinalMk L _ le_rfl

theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L] [IsFractionRing R L] : #L = #R :=
  IsLocalization.cardinalMk L _ le_rfl

end IsFractionRing

end CommRing
