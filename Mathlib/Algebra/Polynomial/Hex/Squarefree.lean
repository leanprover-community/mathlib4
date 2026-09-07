/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Polynomial.Hex.Euclid
public import Mathlib.Algebra.Polynomial.Hex.Int

/-!
# Rational squarefreeness of executable integer polynomials

This module identifies the executable rational-gcd test with squarefreeness
after mapping the integer polynomial to `ℚ[X]`. The statement is deliberately
about the rational cast: integral-polynomial squarefreeness additionally sees
square factors in the content.
-/

public section

namespace HexPolyZMathlib

open Polynomial

noncomputable section

/-- The rational cast of an executable integer polynomial. -/
abbrev toPolyℚ (p : Hex.ZPoly) : Polynomial ℚ :=
  (toPolynomial p).map (Int.castRingHom ℚ)

/-- A dense polynomial stores at most one coefficient exactly when its
Mathlib image has natural degree zero. -/
theorem size_le_one_iff_natDegree_eq_zero {R : Type*} [Semiring R] [DecidableEq R]
    (g : Hex.DensePoly R) :
    g.size ≤ 1 ↔ (HexPolyMathlib.toPolynomial g).natDegree = 0 := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases h : g.size = 0
  · rw [(Hex.DensePoly.degree?_eq_none_iff g).mpr h]
    simp [h]
  · rw [Hex.DensePoly.degree?_eq_some_of_pos_size g (Nat.pos_of_ne_zero h),
      Option.getD_some]
    omega

/-- `toRatPoly` corresponds to the rational cast under `toPolynomial`. -/
theorem toPolynomial_toRatPoly (f : Hex.ZPoly) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) = toPolyℚ f := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.ZPoly.coeff_toRatPoly, toPolyℚ,
    Polynomial.coeff_map, coeff_toPolynomial]
  simp

/-- Coefficients of the rational cast are the rational casts of the integer
coefficients. -/
@[simp] theorem coeff_toPolyℚ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℚ p).coeff n = (p.coeff n : ℚ) := by
  simp [toPolyℚ]

/-- Evaluation of the rational cast is the degree-indexed coefficient sum. -/
theorem eval_toPolyℚ (p : Hex.ZPoly) (x : ℚ) :
    (toPolyℚ p).eval x = ∑ i ∈ Finset.range p.size, (p.coeff i : ℚ) * x ^ i := by
  rw [toPolyℚ, Polynomial.eval_map, HexPolyMathlib.eval₂_toPolynomial]
  simp

/-- The rational cast of a nonzero executable polynomial is nonzero. -/
theorem toPolyℚ_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) : toPolyℚ f ≠ 0 := by
  rw [toPolyℚ, Ne,
    Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℚ))]
  intro h
  exact hf (by have := congrArg ofPolynomial h; simpa using this)

/-- For a nonzero executable integer polynomial, the executable rational-gcd
test is equivalent to squarefreeness of its rational cast. -/
theorem squareFreeRat_iff (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.SquareFreeRat f ↔ Squarefree (toPolyℚ f) := by
  unfold Hex.ZPoly.SquareFreeRat
  set a := Hex.ZPoly.toRatPoly f with ha
  set a' := Hex.DensePoly.derivative a with ha'
  have hPa : HexPolyMathlib.toPolynomial a = toPolyℚ f :=
    toPolynomial_toRatPoly f
  have hPa' : HexPolyMathlib.toPolynomial a' = derivative (toPolyℚ f) := by
    rw [ha', HexPolyMathlib.toPolynomial_derivative, hPa]
  have hP0 : toPolyℚ f ≠ 0 := toPolyℚ_ne_zero hf
  rw [size_le_one_iff_natDegree_eq_zero]
  have hassoc := HexPolyMathlib.toPolynomial_gcd_associated a a'
  have hdeg : (HexPolyMathlib.toPolynomial (Hex.DensePoly.gcd a a')).natDegree
      = (EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f))).natDegree := by
    have h := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassoc)
    rw [hPa, hPa'] at h
    exact h
  rw [hdeg]
  set G := EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f)) with hG
  have hG0 : G ≠ 0 := by
    rw [hG, Ne, EuclideanDomain.gcd_eq_zero_iff]
    exact fun h => hP0 h.1
  have key : G.natDegree = 0 ↔ IsUnit G := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hG0]
    exact_mod_cast Iff.rfl
  rw [key, hG, EuclideanDomain.gcd_isUnit_iff, ← Polynomial.separable_def,
    PerfectField.separable_iff_squarefree]

end

end HexPolyZMathlib
