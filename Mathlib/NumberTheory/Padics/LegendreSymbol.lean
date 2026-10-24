/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Catherine Hsu
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The Legendre Symbol for `p`-adic Integers

This file contains results about Legendre symbols for `p`-adic integers.

## Main definitions

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ is `PadicInt.legendreSym p a`, which defines
the Legendre symbol for a `p`-adic integer `a` as the composition of reduction map modulo `p` and
the usual Legendre symbol for the integers.

## Main results

The main results are

`PadicInt.legendreSym.eq_one_or_neg_one` shows the Legendre symbol is 1 or -1.

`PadicInt.legendreSym.eq_zero_iff` shows the Legendre symbol is 0 if and only if `p` divides `a`.

`PadicInt.legendreSym.sq_one` shows square of the symbol is 1 if `a` is a unit.

`PadicInt.legendreSym.eq_one_iff` shows that if `a` is a unit, then the Legendre symbol is 1
if and only if `a` is a square mod `p`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The Legendre symbol of a `p`-adic integer is the quadratic character on ℤ_[p] precomposed with
the reduction modulo p. -/
noncomputable
def legendreSym : MulChar ℤ_[p] ℤ := (quadraticChar (ZMod p)).compMonoidHom toZMod

variable {a b : ℤ_[p]}
namespace legendreSym

/-- The `p`-adic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast (z : ℤ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by
  simp [legendreSym, _root_.legendreSym, quadraticCharFun]

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym a : ZMod p) = (a.toZMod) ^ (p / 2) := by
  calc (legendreSym a : ZMod p)
    _ = (legendreSym (a.zmodRepr : ℤ_[p]) : ZMod p) := by
      simp [legendreSym, (ZMod.intCast_eq_intCast_iff' (quadraticCharFun (ZMod p) (toZMod a))
        (quadraticCharFun (ZMod p) a.zmodRepr) p).mpr rfl]
    _ = _root_.legendreSym p (a.zmodRepr) := by simp [legendreSym, _root_.legendreSym]
    _ = (a.zmodRepr) ^ (p / 2) := by simp [_root_.legendreSym.eq_pow]
    _ = (a.toZMod) ^ (p / 2) := ZMod.valMinAbs_inj.mp rfl

/-- If `a` is a `p`-adic unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 :=
  Int.isUnit_eq_one_or (IsUnit.map ((quadraticChar (ZMod p)).compMonoidHom toZMod) ha)

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
noncomputable abbrev hom : ℤ_[p] →*₀ ℤ := legendreSym.toMonoidWithZeroHom

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := MonoidWithZeroHom.sq_one hom ha

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare (a.toZMod) := by
  rw [legendreSym, MulChar.compMonoidHom_apply, quadraticChar_one_iff_isSquare]
  rw [← (toZMod a).val_ne_zero, val_toZMod_eq_zmodRepr, ← norm_natCast_zmodRepr_eq_one_iff_ne,
    norm_natCast_zmodRepr_eq_one_iff.mpr (isUnit_iff.mp ha)]

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare (a.toZMod) := by
  rw [eq_neg_one_iff_not_one ha, eq_one_iff ha]

end legendreSym

end PadicInt
