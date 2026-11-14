/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The Legendre Symbol for `p`-adic Integers

This file contains results about Legendre symbols for `p`-adic integers.

## Main definitions

We define `PadicInt.legendreSym p a`, where `p` is a prime and `a : ℤ_[p]ˣ`, as the composition
of the reduction map modulo `p` and the usual Legendre symbol `legendreSym`, which is defined
over `ℤ`.

## Main results

The main results are

* `PadicInt.legendreSym.eq_one_or_neg_one` shows the Legendre symbol of a `p`-adic unit is 1 or -1.

* `PadicInt.legendreSym.eq_zero_iff` shows the Legendre symbol is 0 if and only if `p` divides `a`.

* `PadicInt.legendreSym.eq_one_iff` shows that if `a` is a unit, then the Legendre symbol is 1
  if and only if `a` is a square mod `p`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

@[expose] public section

namespace IsLocalRing

variable {K : Type*} [CommRing K] [IsLocalRing K] [Fintype (ResidueField K)]
  [DecidableEq (ResidueField K)]

noncomputable def legendreSym : MulChar K ℤ :=
  (quadraticChar (ResidueField K)).compLocalHom (residue K)

namespace legendreSym

variable {a b : K}

/-- If `a` is a `p`-adic unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 :=
  Int.isUnit_eq_one_or (IsUnit.map ((quadraticChar (ResidueField K)).compLocalHom (residue K)) ha)

/-- If a is a `p`-adic unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by
  have := eq_one_or_neg_one ha
  lia

/-- The Legendre symbol of a `p`-adic integer `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff : legendreSym a = 0 ↔ ¬ IsUnit a :=
  ⟨fun _ h ↦ by have := eq_one_or_neg_one h; lia, fun h ↦ by rw [MulChar.map_nonunit
  legendreSym h]⟩

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simp]
noncomputable abbrev hom : K →*₀ ℤ := legendreSym.toMonoidWithZeroHom

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := MonoidWithZeroHom.sq_one hom ha

end legendreSym

end IsLocalRing

namespace PadicInt

variable {p : ℕ} [Fact (Nat.Prime p)]

noncomputable instance : Fintype (IsLocalRing.ResidueField ℤ_[p]) :=
  Fintype.ofEquiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv

noncomputable instance : DecidableEq (IsLocalRing.ResidueField ℤ_[p]) :=
  Equiv.decidableEq (PadicInt.residueField (p := p)).toEquiv

noncomputable abbrev legendreSym := IsLocalRing.legendreSym (K := ℤ_[p])

namespace legendreSym

variable {a : ℤ_[p]}

lemma auxzero {z : ℤ} : (z : ZMod p) = 0 ↔ (z : IsLocalRing.ResidueField ℤ_[p]) = 0 :=
  ⟨fun h ↦ (by apply ((PadicInt.residueField (p := p)).injective); simpa using h),
    fun h ↦ by simpa using (congrArg (PadicInt.residueField (p := p)) h)⟩

lemma auxsquare {z : ℤ} : IsSquare (z : ZMod p) ↔ IsSquare (z : IsLocalRing.ResidueField ℤ_[p]) :=
by
  constructor
  · refine fun h ↦ ?_
    rw [isSquare_iff_exists_sq] at h
    obtain ⟨w, h⟩ := h
    have := ((PadicInt.residueField (p := p)).surjective) w
    obtain ⟨w', h'⟩ := this
    rw [isSquare_iff_exists_sq]
    use w'
    apply ((PadicInt.residueField (p := p)).injective)
    simp only [map_intCast, map_pow, h']
    exact h
  · refine fun h ↦ ?_
    apply (IsSquare.map PadicInt.residueField) at h
    simp only [map_intCast] at h
    exact h

/-- The `p`-adic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast (z : ℤ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by
  simp only [legendreSym, _root_.legendreSym, quadraticChar_apply, quadraticCharFun, Int.reduceNeg]
  split_ifs with h h'
  · simp [IsLocalRing.legendreSym.eq_zero_iff, not_isUnit_iff, norm_lt_one_iff_dvd,
      ← zmodRepr_eq_zero_iff_dvd, ← val_toZMod_eq_zmodRepr, h]
  all_goals
    simp [IsLocalRing.legendreSym, quadraticCharFun]
    split_ifs
    all_goals try simp [auxzero, auxsquare] at *; tauto
    rfl

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym a : ZMod p) = (a.toZMod) ^ (p / 2) := by sorry

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare a.toZMod  := by
  rw [legendreSym, IsLocalRing.legendreSym]
  rw [@MulChar.compLocalHom_apply]
  constructor
  · intro a_1
    rw [quadraticChar_one_iff_isSquare] at a_1
    · apply (IsSquare.map PadicInt.residueField) at a_1
      exact even_ofMul_iff.mp a_1
    · simp only [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff, not_not]
      exact ha
  · intro a_1
    rw [← quadraticChar_one_iff_isSquare] at a_1
    · sorry
    · rw [PadicInt.isUnit_iff] at ha
      rw [← PadicInt.norm_natCast_zmodRepr_eq_one_iff] at ha
      rw [PadicInt.norm_natCast_zmodRepr_eq_one_iff_ne] at ha
      simp only [ne_eq] at ha
      refine (ZMod.val_ne_zero (toZMod a)).mp ?_
      simp only [val_toZMod_eq_zmodRepr, ne_eq]
      exact ha


/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare a.toZMod := by
  rw [IsLocalRing.legendreSym.eq_neg_one_iff_not_one ha, eq_one_iff ha]

end legendreSym

end PadicInt
