/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.Polynomial.Hex.Basic
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.GCDMonoid.Nat
public import HexPolyZ

/-!
Equivalence between `Hex.ZPoly` and Mathlib's `Polynomial ℤ`.

This module specializes the generic dense-polynomial correspondence to integer
coefficients so downstream libraries can work directly with the `ZPoly`
abbreviation and the corresponding `Polynomial ℤ` equivalence.
-/

public section

namespace HexPolyZMathlib

noncomputable section

/-- Interpret an executable integer polynomial as a Mathlib polynomial. -/
abbrev toPolynomial (p : Hex.ZPoly) : Polynomial ℤ :=
  HexPolyMathlib.toPolynomial p

/-- Rebuild an executable integer polynomial from a Mathlib polynomial. -/
abbrev ofPolynomial (p : Polynomial ℤ) : Hex.ZPoly :=
  HexPolyMathlib.ofPolynomial p

/-- Coefficients of the embedded Mathlib polynomial agree with the executable
coefficients. -/
@[simp, grind =]
theorem coeff_toPolynomial (p : Hex.ZPoly) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n :=
  HexPolyMathlib.coeff_toPolynomial p n

/-- `ofPolynomial` sends the zero polynomial to the zero `ZPoly`. -/
@[simp, grind =]
theorem ofPolynomial_zero :
    ofPolynomial (0 : Polynomial ℤ) = 0 :=
  HexPolyMathlib.ofPolynomial_zero

/-- `toPolynomial` sends the zero `ZPoly` to the zero polynomial. -/
@[simp, grind =]
theorem toPolynomial_zero :
    toPolynomial (0 : Hex.ZPoly) = 0 :=
  HexPolyMathlib.toPolynomial_zero

/-- `toPolynomial` sends the executable constant `C c` to Mathlib's `Polynomial.C c`. -/
@[simp, grind =]
theorem toPolynomial_C (c : ℤ) :
    toPolynomial (Hex.DensePoly.C c) = Polynomial.C c :=
  HexPolyMathlib.toPolynomial_C c

/-- `toPolynomial` is additive. -/
@[simp, grind =]
theorem toPolynomial_add (p q : Hex.ZPoly) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q :=
  HexPolyMathlib.toPolynomial_add p q

/-- `toPolynomial` is multiplicative. -/
@[simp, grind =]
theorem toPolynomial_mul (p q : Hex.ZPoly) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q :=
  HexPolyMathlib.toPolynomial_mul p q

/-- `toPolynomial` sends the executable `1` to Mathlib's `1`. -/
@[simp, grind =]
theorem toPolynomial_one :
    toPolynomial (1 : Hex.ZPoly) = 1 :=
  HexPolyMathlib.toPolynomial_one

/-- `toPolynomial` commutes with negation. -/
@[simp, grind =]
theorem toPolynomial_neg (p : Hex.ZPoly) :
    toPolynomial (-p) = -toPolynomial p :=
  HexPolyMathlib.toPolynomial_neg p

/-- `toPolynomial` commutes with subtraction. -/
@[simp, grind =]
theorem toPolynomial_sub (p q : Hex.ZPoly) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q :=
  HexPolyMathlib.toPolynomial_sub p q

/-- `toPolynomial` is a left inverse of `ofPolynomial`: embedding a rebuilt
polynomial recovers it. -/
@[simp, grind =]
theorem toPolynomial_ofPolynomial (p : Polynomial ℤ) :
    toPolynomial (ofPolynomial p) = p :=
  HexPolyMathlib.toPolynomial_ofPolynomial p

/-- `ofPolynomial` is a left inverse of `toPolynomial`: rebuilding an embedded
`ZPoly` recovers it. -/
@[simp, grind =]
theorem ofPolynomial_toPolynomial (p : Hex.ZPoly) :
    ofPolynomial (toPolynomial p) = p :=
  HexPolyMathlib.ofPolynomial_toPolynomial p

/-- The executable `ZPoly` representation is ring-equivalent to Mathlib
polynomials over `ℤ`. -/
abbrev equiv : Hex.ZPoly ≃+* Polynomial ℤ :=
  HexPolyMathlib.equiv

/-- The ring equivalence acts as `toPolynomial` in the forward direction. -/
@[simp, grind =]
theorem equiv_apply (p : Hex.ZPoly) :
    equiv p = toPolynomial p := by
  rfl

/-- The inverse ring equivalence acts as `ofPolynomial`. -/
@[simp, grind =]
theorem equiv_symm_apply (p : Polynomial ℤ) :
    equiv.symm p = ofPolynomial p := by
  rfl

/-- The Mathlib-free `ZPoly` unit predicate agrees with Mathlib units after
transport to `Polynomial ℤ`. -/
theorem isUnit_iff_toPolynomial_isUnit (f : Hex.ZPoly) :
    Hex.ZPoly.IsUnit f ↔ IsUnit (toPolynomial f) := by
  constructor
  · rintro (rfl | rfl)
    · simp
    · simp
  · intro h
    rcases Polynomial.isUnit_iff.mp h with ⟨r, hr, hpoly⟩
    have hf : f = Hex.DensePoly.C r := by
      exact equiv.injective (by
        simpa using hpoly.symm)
    rcases Int.isUnit_iff.mp hr with hr | hr
    · left
      simp [hf, hr]
    · right
      simp [hf, hr]

/-! # Gauss content/primitive-part correspondence

The executable `Hex.ZPoly.content`/`primitivePart` carry their own Gauss theory
(`content_mul`, `content_mul_primitivePart`, `primitivePart_primitive`). These
lemmas relate that theory to Mathlib's `Polynomial.content`/`primPart`, so the
recombination recovery proof can lean on Mathlib's Gauss lemma machinery. -/

/-- The Mathlib content of the embedded polynomial agrees with the executable
integer content. Both are the normalized (nonnegative) gcd of the coefficients,
so this is the Gauss correspondence between the two content theories. -/
theorem toPolynomial_content (f : Hex.ZPoly) :
    (toPolynomial f).content = Hex.ZPoly.content f := by
  have hnonneg : 0 ≤ Hex.ZPoly.content f := by
    unfold Hex.ZPoly.content Hex.DensePoly.content
    exact Int.natCast_nonneg _
  refine dvd_antisymm_of_normalize_eq Polynomial.normalize_content
    (Int.normalize_of_nonneg hnonneg) ?_ ?_
  · rw [← Int.natAbs_dvd]
    refine Hex.ZPoly.dvd_content_of_nat_dvd_coeff f _ (fun n => ?_)
    rw [Int.natAbs_dvd, ← coeff_toPolynomial]
    exact Polynomial.content_dvd_coeff n
  · rw [Polynomial.dvd_content_iff_C_dvd, Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [coeff_toPolynomial]
    exact Hex.ZPoly.content_dvd_coeff f n

/-- Gauss content decomposition transported to Mathlib: the embedded polynomial
is its content times the embedded primitive part. -/
theorem toPolynomial_eq_C_content_mul_primitivePart (f : Hex.ZPoly) :
    toPolynomial f =
      Polynomial.C (Hex.ZPoly.content f) *
        toPolynomial (Hex.ZPoly.primitivePart f) := by
  conv_lhs => rw [← Hex.ZPoly.content_mul_primitivePart f]
  rw [← Hex.ZPoly.C_mul_eq_scale, toPolynomial_mul, toPolynomial_C]

/-- A primitive executable polynomial embeds to a Mathlib-primitive polynomial. -/
theorem isPrimitive_toPolynomial_of_primitive (f : Hex.ZPoly)
    (hf : Hex.ZPoly.Primitive f) : (toPolynomial f).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one, toPolynomial_content]
  exact hf

/-- A nonzero executable polynomial has nonzero content. -/
theorem content_ne_zero (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.content f ≠ 0 := by
  intro hz
  apply hf
  have hz' : (toPolynomial f).content = 0 := by rw [toPolynomial_content]; exact hz
  rw [Polynomial.content_eq_zero_iff] at hz'
  rw [← ofPolynomial_toPolynomial f, hz', ofPolynomial_zero]


end

end HexPolyZMathlib
