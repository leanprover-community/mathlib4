/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import HexRealRoots.Prec
public import Mathlib.Algebra.Polynomial.Hex.Int

/-!
# Real and complex interpretations of executable integer polynomials and dyadic numbers
-/

public section

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-- Real value of a dyadic number, through `Dyadic.toRat`. -/
def Dyadic.toReal (x : Dyadic) : ℝ := (x.toRat : ℝ)

/-- `Dyadic.toReal` is the rational cast of `toRat`. A plain-import restatement
of the definition, so downstream modules that do not `import all` this file can
still bridge `Dyadic.toReal` to the `ℚ`-valued endpoints of an isolation. -/
@[simp] theorem toReal_eq_cast_toRat (x : Dyadic) : Dyadic.toReal x = (x.toRat : ℝ) := by
  unfold Dyadic.toReal
  rfl

/-- The real cast of an executable integer polynomial. -/
abbrev toPolyℝ (p : Hex.ZPoly) : Polynomial ℝ :=
  (toPolynomial p).map (Int.castRingHom ℝ)

/-- The complex cast of an executable integer polynomial. -/
abbrev toPolyℂ (p : Hex.ZPoly) : Polynomial ℂ :=
  (toPolynomial p).map (Int.castRingHom ℂ)

/-! # Dyadic casts -/

/-- `toRat` turns a left shift into multiplication by a power of two. -/
theorem toRat_shiftLeft (x : Dyadic) (i : Int) :
    (x <<< i).toRat = x.toRat * (2 : ℚ) ^ i := by
  cases x with
  | zero => simp [HShiftLeft.hShiftLeft, Dyadic.shiftLeft]
  | ofOdd n k hn =>
    change (Dyadic.ofOdd n (k - i) hn).toRat = _
    rw [Dyadic.toRat_ofOdd_eq_mul_two_pow, Dyadic.toRat_ofOdd_eq_mul_two_pow,
      show -(k - i) = -k + i by ring, zpow_add₀ (by norm_num)]
    ring

/-- `toRat` turns a right shift into multiplication by a negative power of two. -/
theorem toRat_shiftRight (x : Dyadic) (i : Int) :
    (x >>> i).toRat = x.toRat * (2 : ℚ) ^ (-i) := by
  cases x with
  | zero => simp [HShiftRight.hShiftRight, Dyadic.shiftRight]
  | ofOdd n k hn =>
    change (Dyadic.ofOdd n (k + i) hn).toRat = _
    rw [Dyadic.toRat_ofOdd_eq_mul_two_pow, Dyadic.toRat_ofOdd_eq_mul_two_pow,
      show -(k + i) = -k + -i by ring, zpow_add₀ (by norm_num)]
    ring

/-- The real value of an integer dyadic is the integer cast. -/
@[simp] theorem toReal_ofInt (n : Int) : Dyadic.toReal (Dyadic.ofInt n) = (n : ℝ) := by
  unfold Dyadic.toReal
  rw [show Dyadic.ofInt n = ((n : Int) : Dyadic) from rfl, Dyadic.toRat_intCast]
  push_cast; ring

/-- `Hex.twoPow k` has real value `2 ^ k`. -/
@[simp] theorem toReal_twoPow (k : Int) : Dyadic.toReal (Hex.twoPow k) = (2 : ℝ) ^ k := by
  have h1 : (1 : Dyadic).toRat = 1 := by
    rw [show (1 : Dyadic) = ((1 : Int) : Dyadic) from rfl, Dyadic.toRat_intCast]; norm_num
  unfold Dyadic.toReal Hex.twoPow
  rw [toRat_shiftLeft, h1, one_mul]
  push_cast
  norm_cast

/-- The real value of a left shift is multiplication by a power of two. -/
theorem toReal_shiftLeft (x : Dyadic) (i : Int) :
    Dyadic.toReal (x <<< i) = Dyadic.toReal x * (2 : ℝ) ^ i := by
  unfold Dyadic.toReal
  rw [toRat_shiftLeft]; push_cast; ring

/-- The real value of a right shift is multiplication by a negative power of two. -/
theorem toReal_shiftRight (x : Dyadic) (i : Int) :
    Dyadic.toReal (x >>> i) = Dyadic.toReal x * (2 : ℝ) ^ (-i) := by
  unfold Dyadic.toReal
  rw [toRat_shiftRight]; push_cast; ring

/-- The real value of the dyadic `n / 2ⁱ` (an integer shifted right by `i` bits). -/
@[simp] theorem toReal_ofInt_shiftRight (n i : Int) :
    Dyadic.toReal (Dyadic.ofInt n >>> i) = (n : ℝ) * (2 : ℝ) ^ (-i) := by
  rw [toReal_shiftRight, toReal_ofInt]

/-! # Cast bridges to the executable polynomial -/

@[simp] theorem coeff_toPolyℝ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℝ p).coeff n = (p.coeff n : ℝ) := by
  simp [toPolyℝ]

/-- Evaluating the real cast at `x` is the degree-indexed sum of the integer
coefficients cast to `ℝ`. For a literal `ofCoeffs` this unfolds via
`Finset.sum_range_succ` into an explicit polynomial in `x`; combined with
`Polynomial.IsRoot`, it turns a root goal into a plain equation
`ring`/`norm_num` can discharge. -/
theorem eval_toPolyℝ (p : Hex.ZPoly) (x : ℝ) :
    (toPolyℝ p).eval x = ∑ i ∈ Finset.range p.size, (p.coeff i : ℝ) * x ^ i := by
  rw [toPolyℝ, Polynomial.eval_map, HexPolyMathlib.eval₂_toPolynomial]
  simp

theorem natDegree_toPolyℝ (p : Hex.ZPoly) :
    (toPolyℝ p).natDegree = p.degree?.getD 0 := by
  rw [toPolyℝ, Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective_int (Int.castRingHom ℝ)),
    HexPolyMathlib.natDegree_toPolynomial]

/-- Coefficients of the complex cast are the complex casts of the integer
coefficients. -/
@[simp] theorem coeff_toPolyℂ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℂ p).coeff n = (p.coeff n : ℂ) := by
  simp [toPolyℂ]

/-- The complex cast preserves the natural degree. -/
theorem natDegree_toPolyℂ (p : Hex.ZPoly) :
    (toPolyℂ p).natDegree = p.degree?.getD 0 := by
  rw [toPolyℂ, Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective_int (Int.castRingHom ℂ)),
    HexPolyMathlib.natDegree_toPolynomial]

/-- The complex cast preserves the leading coefficient. -/
theorem leadingCoeff_toPolyℂ (p : Hex.ZPoly) :
    (toPolyℂ p).leadingCoeff = (p.leadingCoeff : ℂ) := by
  rw [toPolyℂ, Polynomial.leadingCoeff_map_of_injective
    (RingHom.injective_int (Int.castRingHom ℂ)), HexPolyMathlib.leadingCoeff_toPolynomial]
  simp

/-- The complex cast is the map of the integer polynomial. -/
theorem toPolyℂ_eq_map (p : Hex.ZPoly) :
    toPolyℂ p = (toPolynomial p).map (Int.castRingHom ℂ) := rfl

/-! # `rootBound` soundness -/

end

end HexRealRootsMathlib
