/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu
-/
module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The Legendre Symbol for Local Rings with Finite Reside Field

This file contains results about Legendre symbols for local rings with finite residue fields.

## Main definitions

For a local ring `R` with finite residue field, we define `IsLocalRing.legendreSym a` as the
composition of the reduction map to `ResidueField R` and the quadratic character of
`ResidueField R`.

## Main results

The main results are

* `IsLocalRing.legendreSym.eq_one_or_neg_one` shows the Legendre symbol of a unit `a` is 1 or -1.

* `IsLocalRing.legendreSym.eq_zero_iff` shows the Legendre symbol is 0 if and only if `a` is not
a unit.

* `IsLocalRing.legendreSym.eq_one_iff` shows that if `a` is a unit, then the Legendre symbol is 1
  if and only if `a` is a square in `ResidueField R`.

* `IsLocalRing.legendreSym.eq_pow` shows that if `ringChar R` is odd, then `legendreSym a` can
be computed in terms of `a ^ (Fintype.card (ResidueField R) / 2)`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [Fintype (ResidueField R)]
  [DecidableEq (ResidueField R)]

-- TODO: Switch over to Finite and Nat.card once the rest of the finite field material has been
-- switched over
/-- We define the `legendreSym` for a local ring with finite residue field. -/
noncomputable def legendreSym : MulChar R ℤ :=
  (quadraticChar (ResidueField R)).compLocalHom (residue R)

namespace legendreSym

variable {a b : R}

/-- If `a` is a unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 :=
  Int.isUnit_eq_one_or (IsUnit.map ((quadraticChar (ResidueField R)).compLocalHom (residue R)) ha)

/-- If `a` is a unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by
  have := eq_one_or_neg_one ha
  lia

/-- The Legendre symbol of `a` is zero iff `a` is not a unit. -/
theorem eq_zero_iff : legendreSym a = 0 ↔ ¬ IsUnit a :=
  ⟨fun _ h ↦ by have := eq_one_or_neg_one h; lia, fun h ↦ by rw [MulChar.map_nonunit
  legendreSym h]⟩

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simp]
noncomputable abbrev hom : R →*₀ ℤ := legendreSym.toMonoidWithZeroHom

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := MonoidWithZeroHom.sq_one hom ha

-- TODO: move (wrong file)
omit [DecidableEq (ResidueField R)] in
/-- The residue of an element is `0` in `ResidueField R` if and only if its reduction in
`ZMod p` is `0`. -/
lemma residue_eq_zero_iff_zmod {p : ℕ} [Fact (Nat.Prime p)]
    (hp : p ∣ Fintype.card (ResidueField R)) {z : ℤ} :
    residue R z = 0 ↔ (z : ZMod p) = 0 := by
  have hchar : CharP (ResidueField R) p := by
    rw [← prime_dvd_char_iff_dvd_card] at hp
    refine ringChar.of_eq ?_
    have : (ringChar (ResidueField R)).Prime := by apply (CharP.prime_ringChar)
    have hp2 : Prime p := by
      rw [← @Nat.prime_iff]
      rw [Nat.prime_iff_card_units]
      exact ZMod.card_units p
    rw [Nat.Prime.dvd_iff_eq this (Prime.ne_one hp2)] at hp
    exact hp
  rw [show residue R z = (z : ResidueField R) by rfl, CharP.intCast_eq_zero_iff,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

-- TODO: move (wrong file)
omit [DecidableEq (ResidueField R)] in
/-- The residue of an element is a square in `ResidueField R` if and only if its reduction in
`ZMod p` is a square. -/
lemma isSquare_residue_iff {p : ℕ} [Fact (Nat.Prime p)]
    (hp : Fintype.card (ResidueField R) = p) {z : ℤ} :
    IsSquare (residue R z) ↔ IsSquare (z : ZMod p) := by
  subst hp
  have : CharP (ResidueField R) (Fintype.card (ResidueField R)) := charP_of_card_eq_prime rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show (z : ZMod (Fintype.card (ResidueField R))) = (ZMod.ringEquiv _ rfl).symm (residue R z)
      by simp]
    exact IsSquare.map _ h
  · rw [show residue R z = ZMod.ringEquiv _ rfl (z : ZMod (Fintype.card (ResidueField R))) by simp]
    exact IsSquare.map _ h

/-- The Legendre symbol for local rings with finite residue fields agrees with the classical
Legendre symbol on ℤ. -/
lemma intCast {p : ℕ} [Fact (Nat.Prime p)]
    (hp : Fintype.card (ResidueField R) = p) (z : ℤ) :
    legendreSym (z : R) = _root_.legendreSym p z := by
  have hp1 : p = Fintype.card (ResidueField R) := by exact Eq.symm hp
  have hp2 : (p ∣ Fintype.card (ResidueField R)) := by
    apply (dvd_of_eq) at hp1
    exact hp1
  simp only [legendreSym, _root_.legendreSym, quadraticChar_apply, quadraticCharFun]
  split_ifs with h0 hsq
  · simp [MulChar.compLocalHom_apply, (residue_eq_zero_iff_zmod hp2).mpr h0]
  all_goals
    simp only [MulChar.compLocalHom_apply, quadraticChar_apply, quadraticCharFun,
      isSquare_residue_iff hp]
  · rw [ite_eq_right (by rwa [residue_eq_zero_iff_zmod hp2]), ite_eq_left hsq]
  · rw [ite_eq_right (by rwa [residue_eq_zero_iff_zmod hp2]), ite_eq_right hsq]

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square in `ResidueField R`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare (residue R a) := by
  rw [legendreSym, MulChar.compLocalHom_apply, quadraticChar_one_iff_isSquare]
  simpa using ha

/-- `legendreSym a = -1` iff `a` is a nonsquare in `ResidueField R`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare (residue R a) := by
  rw [IsLocalRing.legendreSym.eq_neg_one_iff_not_one ha, eq_one_iff ha]

/-- If `ringChar R` is odd, then `legendreSym a` can be computed in terms of
`(residue R a) ^ (Fintype.card (ResidueField R) / 2)`. -/
theorem eq_pow (hR : ringChar (ResidueField R) ≠ 2) :
    legendreSym a = residue R a ^ (Fintype.card (ResidueField R) / 2) := by
  rw [legendreSym, MulChar.compLocalHom_apply]
  by_cases h0 : (residue R) a = 0
  · rw [h0, zero_pow (by simp [Fintype.one_lt_card])]
    simp
  · simp only [quadraticChar_eq_pow_of_char_ne_two hR h0, Int.reduceNeg, Int.cast_ite,
      Int.cast_one, Int.cast_neg]
    split_ifs with h
    · rw [h]
    · grind [FiniteField.pow_dichotomy hR h0]

end legendreSym

end IsLocalRing
