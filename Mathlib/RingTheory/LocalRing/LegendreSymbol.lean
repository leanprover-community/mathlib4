/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu
-/
module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The Legendre Symbol for Local Rings with Finite Reside Field

This file contains results about Legendre symbols for local rings with finite residue fields.

## Main definitions

For a local ring `R` with finite residue field, we define `IsLocalRing.legendreSym a` as the
composition of the reduction map to `ResidueField R` and the quadratic character of
`ResidueField R`.

## Main results

* `IsLocalRing.legendreSym.eq_one_or_neg_one` shows the Legendre symbol of a unit `a` is 1 or -1.

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

-- TODO: Can we remove the noncomputable flag here?
/-- We define the `legendreSym` for a local ring with finite residue field. -/
noncomputable def legendreSym : MulChar R ℤ := open scoped Classical in
  (quadraticChar (ResidueField R)).compLocalHom (residue R)

namespace legendreSym

variable {a b : R}

/-- If `a` is a unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 :=
   Int.isUnit_eq_one_or (ha.map _)

/-- If `a` is a unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by
  lia [eq_one_or_neg_one ha]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simp]
noncomputable abbrev hom : R →*₀ ℤ := legendreSym.toMonoidWithZeroHom

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := MonoidWithZeroHom.sq_one hom ha

/-- The residue of an element is a square in `ResidueField R` if and only if its reduction in
`ZMod p` is a square. -/
lemma isSquare_residue_iff {p : ℕ} [Fact (Nat.Prime p)]
    (hp : Fintype.card (ResidueField R) = p) {z : ℤ} :
    IsSquare (residue R z) ↔ IsSquare (z : ZMod p) := by
  subst hp
  have : CharP (ResidueField R) (Fintype.card (ResidueField R)) := charP_of_card_eq_prime rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [show z = (ZMod.ringEquiv _ rfl).symm (residue R z) by simp, IsSquare.map _ h]
  · simp_rw [show residue R z = ZMod.ringEquiv _ rfl z by simp, IsSquare.map _ h]

/-- The Legendre symbol for local rings with finite residue fields agrees with the classical
Legendre symbol on ℤ. -/
lemma intCast {p : ℕ} [Fact (Nat.Prime p)]
    (hp : Fintype.card (ResidueField R) = p) (z : ℤ) :
    legendreSym (z : R) = _root_.legendreSym p z := by
  have : residue R z = 0 ↔ (z : ZMod p) = 0 := by
    have : CharP (ResidueField R) p := charP_of_card_eq_prime hp
    rw [show residue R z = (z : ResidueField R) by rfl, CharP.intCast_eq_zero_iff,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [legendreSym, _root_.legendreSym, quadraticChar_apply, quadraticCharFun]
  grind [MulChar.compLocalHom_apply, quadraticChar_apply, quadraticCharFun,
      isSquare_residue_iff]

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square in `ResidueField R`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare (residue R a) := by
  open scoped Classical in rw [legendreSym, MulChar.compLocalHom_apply,
    quadraticChar_one_iff_isSquare]
  simpa using ha

/-- `legendreSym a = -1` iff `a` is a nonsquare in `ResidueField R`. -/
theorem eq_neg_one_iff :
    legendreSym a = -1 ↔ ¬ IsSquare (residue R a) := by
 classical exact quadraticChar_neg_one_iff_not_isSquare

/-- If `ringChar R` is odd, then `legendreSym a` can be computed in terms of
`(residue R a) ^ (Fintype.card (ResidueField R) / 2)`. -/
theorem eq_pow (hR : ringChar (ResidueField R) ≠ 2) :
    legendreSym a = residue R a ^ (Fintype.card (ResidueField R) / 2) := by
  classical exact quadraticChar_eq_pow_of_char_ne_two' hR _

end legendreSym

end IsLocalRing
