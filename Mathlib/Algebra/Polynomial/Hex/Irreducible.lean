/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.Polynomial.Hex.Int
public import HexBerlekampZassenhaus.FactorIrreducibility

/-!
# Irreducibility of executable integer polynomials

Transport Hex irreducibility certificates across the polynomial equivalence.
-/

public section

/--
The Mathlib-free executable irreducibility predicate agrees with Mathlib's
irreducibility predicate after transport to `Polynomial ℤ`.
-/
theorem Hex.ZPoly.irreducible_iff (f : Hex.ZPoly) :
    Hex.ZPoly.Irreducible f ↔ _root_.Irreducible (HexPolyZMathlib.toPolynomial f) := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro hunit
      exact hf.not_unit ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mpr hunit)
    · intro a b hfactor
      have hfactor_hex :
          f = HexPolyZMathlib.ofPolynomial a * HexPolyZMathlib.ofPolynomial b := by
        apply HexPolyZMathlib.equiv.injective
        simpa [HexPolyZMathlib.equiv_apply] using hfactor
      rcases hf.no_factors _ _ hfactor_hex with hunit | hunit
      · left
        simpa using
          (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit
            (HexPolyZMathlib.ofPolynomial a)).mp hunit
      · right
        simpa using
          (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit
            (HexPolyZMathlib.ofPolynomial b)).mp hunit
  · intro hf
    refine
      { not_zero := ?_
        not_unit := ?_
        no_factors := ?_ }
    · intro hzero
      exact hf.ne_zero (by simp [hzero])
    · intro hunit
      exact hf.not_isUnit ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mp hunit)
    · intro a b hfactor
      have hfactor_poly :
          HexPolyZMathlib.toPolynomial f =
            HexPolyZMathlib.toPolynomial a * HexPolyZMathlib.toPolynomial b := by
        simpa using congrArg HexPolyZMathlib.toPolynomial hfactor
      rcases hf.isUnit_or_isUnit hfactor_poly with hunit | hunit
      · left
        exact (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit a).mpr hunit
      · right
        exact (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit b).mpr hunit
