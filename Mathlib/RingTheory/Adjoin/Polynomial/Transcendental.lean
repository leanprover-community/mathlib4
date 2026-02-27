/-
Copyright (c) 2026 Xavier Généreux, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Polynomials and adjoining transcendental elements

## Main results

* `Polynomial.equivPolynomialAdjoin`:
  For a transcendental element over `R`, `x` we have `R[X] ≃ R[x]`.
-/

@[expose] public section

namespace Polynomial

noncomputable section Transcendental

open Algebra Transcendental

variable {R A : Type*} [CommRing R]
variable [Ring A] [Algebra R A]

/--
If `x` is a transcendental element over `R` then `R[X] ≃ (aeval (R := R) x).range`. -/
abbrev equivPolynomialRangeAEval (x : A) (hx : Transcendental R x) :
    R[X] ≃ₐ[R] (aeval (R := R) x).range :=
  AlgEquiv.ofInjective _ <| transcendental_iff_injective.mp hx

@[simp]
theorem equivPolynomialRangeAEval_def (x : A) (hx : Transcendental R x) (p : R[X]) :
    equivPolynomialRangeAEval x hx p = aeval x p := rfl

@[simp]
theorem equivPolynomialRangeAEval_def' (x : A) (hx : Transcendental R x) (p : R[X]) :
    equivPolynomialRangeAEval x hx p = (⟨aeval x p, by simp⟩ : (aeval x).range) := rfl

/--
If `x` is a transcendental element over `R` then `R[X] ≃ R[x]`. -/
def equivPolynomialAdjoin (x : A) (hx : Transcendental R x) :
    R[X] ≃ₐ[R] Algebra.adjoin R {x} :=
  (equivPolynomialRangeAEval x hx).trans (Algebra.equivRangeAevalAdjoinSingleton R x)

@[simp]
theorem equivPolynomialAdjoin_def (x : A) (hx : Transcendental R x) (p : R[X]) :
    equivPolynomialAdjoin x hx p = (⟨aeval x p, by simp⟩ : Algebra.adjoin R {x}) := rfl

@[simp]
theorem equivPolynomialAdjoin_coe_eq (x : A) (hx : Transcendental R x) (p : R[X]) :
    equivPolynomialAdjoin x hx p = aeval x p := rfl

theorem equivPolynomialAdjoin_apply_X (x : A) (hx : Transcendental R x) :
    equivPolynomialAdjoin x hx X = x := by simp

end Transcendental

end Polynomial
