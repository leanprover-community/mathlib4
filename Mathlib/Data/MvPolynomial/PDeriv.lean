/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.MvPolynomial.Derivation

#align_import data.mv_polynomial.pderiv from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `MvPolynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `MvPolynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/


noncomputable section

universe u v

namespace MvPolynomial

open Set Function Finsupp

open scoped BigOperators

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section PDeriv

variable [CommSemiring R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  letI := Classical.decEq σ
  mkDerivation R <| Pi.single i 1
#align mv_polynomial.pderiv MvPolynomial.pderiv

theorem pderiv_def [DecidableEq σ] (i : σ) : pderiv i = mkDerivation R (Pi.single i 1) := by
  unfold pderiv; congr!
  -- ⊢ mkDerivation R (Pi.single i 1) = mkDerivation R (Pi.single i 1)
                 -- 🎉 no goals
#align mv_polynomial.pderiv_def MvPolynomial.pderiv_def

@[simp]
theorem pderiv_monomial {i : σ} :
    pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  classical
    simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
      ← (monomial _).map_smul]
    refine' (Finset.sum_eq_single i (fun j _ hne => _) fun hi => _).trans _
    · simp [Pi.single_eq_of_ne hne]
    · rw [Finsupp.not_mem_support_iff] at hi; simp [hi]
    · simp
#align mv_polynomial.pderiv_monomial MvPolynomial.pderiv_monomial

theorem pderiv_C {i : σ} : pderiv i (C a) = 0 :=
  derivation_C _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_C MvPolynomial.pderiv_C

theorem pderiv_one {i : σ} : pderiv i (1 : MvPolynomial σ R) = 0 := pderiv_C
#align mv_polynomial.pderiv_one MvPolynomial.pderiv_one

@[simp]
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv i (X j : MvPolynomial σ R) = Pi.single (f := fun j => _) i 1 j := by
  rw [pderiv_def, mkDerivation_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_X MvPolynomial.pderiv_X

@[simp]
theorem pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ R) = 1 := by classical simp
                                                                            -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_X_self MvPolynomial.pderiv_X_self

@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ R) = 0 := by
  classical simp [h]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_X_of_ne MvPolynomial.pderiv_X_of_ne

theorem pderiv_eq_zero_of_not_mem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) :
    pderiv i f = 0 :=
  derivation_eq_zero_of_forall_mem_vars fun _ hj => pderiv_X_of_ne <| ne_of_mem_of_not_mem hj h
#align mv_polynomial.pderiv_eq_zero_of_not_mem_vars MvPolynomial.pderiv_eq_zero_of_not_mem_vars

theorem pderiv_monomial_single {i : σ} {n : ℕ} : pderiv i (monomial (single i n) a) =
    monomial (single i (n - 1)) (a * n) := by simp
                                              -- 🎉 no goals
#align mv_polynomial.pderiv_monomial_single MvPolynomial.pderiv_monomial_single

theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]
  -- 🎉 no goals
#align mv_polynomial.pderiv_mul MvPolynomial.pderiv_mul

-- @[simp] -- Porting note: simp can prove this
theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (C a * f) = C a * pderiv i f := by
  rw [C_mul', Derivation.map_smul, C_mul']
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_C_mul MvPolynomial.pderiv_C_mul

end PDeriv

end MvPolynomial
