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
# The Legendre Symbol for `p`-adic Integers

This file contains results about Legendre symbols for local rings with finite residue fields.

## Main definitions

We define `IsLocalRing.legendreSym p a`, where `p` is a prime and `a : ℤ_[p]ˣ`, as the composition
of the reduction map modulo `p` and the usual Legendre symbol `legendreSym`, which is defined
over `ℤ`.

## Main results

The main results are

* `IsLocalRing.legendreSym.eq_one_or_neg_one` shows the Legendre symbol of a unit is 1 or -1.

* `IsLocalRing.legendreSym.eq_zero_iff` shows the Legendre symbol is 0 if and only if `p` divides
`a`.

* `IsLocalRing.legendreSym.eq_one_iff` shows that if `a` is a unit, then the Legendre symbol is 1
  if and only if `a` is a square mod `p`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [Fintype (ResidueField R)]
  [DecidableEq (ResidueField R)]

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

/-- The Legendre symbol of `a` is zero iff `p ∣ a`. -/
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
lemma residue_eq_zero_iff_of_prime {p : ℕ} [Fact (Nat.Prime p)]
    (hp : Fintype.card (ResidueField R) = p) {z : ℤ} :
    residue R z = 0 ↔ (z : ZMod p) = 0 := by
  subst hp
  have : CharP (ResidueField R) (Fintype.card (ResidueField R)) := charP_of_card_eq_prime rfl
  rw [show residue R z = ZMod.ringEquiv _ rfl (z : ZMod (Fintype.card (ResidueField R))) by simp,
    RingEquiv.map_eq_zero_iff _]

-- TODO: move (wrong file)
omit [DecidableEq (ResidueField R)] in
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

/-- The `p`-adic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast {p : ℕ} [Fact (Nat.Prime p)]
    (hp : Fintype.card (ResidueField R) = p) (z : ℤ) :
    legendreSym (z : R) = _root_.legendreSym p z := by
  simp only [legendreSym, _root_.legendreSym, quadraticChar_apply, quadraticCharFun]
  split_ifs with h0 hsq
  · simp [MulChar.compLocalHom_apply, (residue_eq_zero_iff_of_prime hp).mpr h0]
  all_goals
    simp only [MulChar.compLocalHom_apply, quadraticChar_apply, quadraticCharFun,
      isSquare_residue_iff hp]
  · rw [ite_eq_right (by rwa [residue_eq_zero_iff_of_prime hp]), ite_eq_left hsq]
  · rw [ite_eq_right (by rwa [residue_eq_zero_iff_of_prime hp]), ite_eq_right hsq]

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare (residue R a) := by
  rw [legendreSym, MulChar.compLocalHom_apply, quadraticChar_one_iff_isSquare]
  simpa using ha

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare (residue R a) := by
  rw [IsLocalRing.legendreSym.eq_neg_one_iff_not_one ha, eq_one_iff ha]

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow {p : ℕ} [Fact (Nat.Prime p)] (hp : Fintype.card (ResidueField R) = p) :
    residue R (legendreSym a) = (residue R a) ^ (p / 2) := by
    simp only [map_intCast]
    simp only [legendreSym]
    simp only [MulChar.compLocalHom_apply, quadraticChar_apply]
    simp only [quadraticCharFun]
    split_ifs with h1 h2
    · rw [h1]
      rw [zero_pow]
      · lia
      · simp only [ne_eq, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, Order.lt_two_iff, false_or,
        not_le]
        rw [← hp]
        exact Fintype.one_lt_card
    · obtain ⟨w, h⟩ := h2
      rw [h]
      simp only [Int.cast_one]
      rw [← pow_two]
      rw [← pow_mul']
      rw [← hp]
      rw [pow_mul]
      by_cases h3 : w ^ (Fintype.card (ResidueField R) / 2) = 1
      · rw [h3]
        simp only [one_pow]
      · sorry
    · push Not at h1
      rw [IsLocalRing.residue_ne_zero_iff_isUnit] at h1
      rw [← eq_neg_one_iff h1] at h2
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one]
      sorry

end legendreSym

end IsLocalRing
