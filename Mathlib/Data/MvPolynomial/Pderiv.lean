/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov

! This file was ported from Lean 3 source module data.mv_polynomial.pderiv
! leanprover-community/mathlib commit 2f5b500a507264de86d666a5f87ddb976e2d8de4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Variables
import Mathbin.Data.MvPolynomial.Derivation

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `mv_polynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/


noncomputable section

universe u v

namespace MvPolynomial

open Set Function Finsupp AddMonoidAlgebra

open scoped BigOperators

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section Pderiv

variable {R} [CommSemiring R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  letI := Classical.decEq σ
  mk_derivation R <| Pi.single i 1
#align mv_polynomial.pderiv MvPolynomial.pderiv

theorem pderiv_def [DecidableEq σ] (i : σ) : pderiv i = mkDerivation R (Pi.single i 1) := by
  convert rfl
#align mv_polynomial.pderiv_def MvPolynomial.pderiv_def

@[simp]
theorem pderiv_monomial {i : σ} : pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) :=
  by
  classical
    simp only [pderiv_def, mk_derivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
      ← (monomial _).map_smul]
    refine' (Finset.sum_eq_single i (fun j hj hne => _) fun hi => _).trans _
    · simp [Pi.single_eq_of_ne hne]
    · rw [Finsupp.not_mem_support_iff] at hi ; simp [hi]
    · simp
#align mv_polynomial.pderiv_monomial MvPolynomial.pderiv_monomial

theorem pderiv_c {i : σ} : pderiv i (C a) = 0 :=
  derivation_c _ _
#align mv_polynomial.pderiv_C MvPolynomial.pderiv_c

theorem pderiv_one {i : σ} : pderiv i (1 : MvPolynomial σ R) = 0 :=
  pderiv_c
#align mv_polynomial.pderiv_one MvPolynomial.pderiv_one

@[simp]
theorem pderiv_x [DecidableEq σ] (i j : σ) :
    pderiv i (X j : MvPolynomial σ R) = @Pi.single _ _ _ _ i 1 j := by
  rw [pderiv_def, mk_derivation_X]
#align mv_polynomial.pderiv_X MvPolynomial.pderiv_x

@[simp]
theorem pderiv_x_self (i : σ) : pderiv i (X i : MvPolynomial σ R) = 1 := by classical simp
#align mv_polynomial.pderiv_X_self MvPolynomial.pderiv_x_self

@[simp]
theorem pderiv_x_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ R) = 0 := by
  classical simp [h]
#align mv_polynomial.pderiv_X_of_ne MvPolynomial.pderiv_x_of_ne

theorem pderiv_eq_zero_of_not_mem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) :
    pderiv i f = 0 :=
  derivation_eq_zero_of_forall_mem_vars fun j hj => pderiv_x_of_ne <| ne_of_mem_of_not_mem hj h
#align mv_polynomial.pderiv_eq_zero_of_not_mem_vars MvPolynomial.pderiv_eq_zero_of_not_mem_vars

theorem pderiv_monomial_single {i : σ} {n : ℕ} :
    pderiv i (monomial (single i n) a) = monomial (single i (n - 1)) (a * n) := by simp
#align mv_polynomial.pderiv_monomial_single MvPolynomial.pderiv_monomial_single

theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]
#align mv_polynomial.pderiv_mul MvPolynomial.pderiv_mul

@[simp]
theorem pderiv_c_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (C a * f) = C a * pderiv i f :=
  (derivation_c_mul _ _ _).trans C_mul'.symm
#align mv_polynomial.pderiv_C_mul MvPolynomial.pderiv_c_mul

end Pderiv

end MvPolynomial

