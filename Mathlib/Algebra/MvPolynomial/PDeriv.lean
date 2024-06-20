/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.MvPolynomial.Homogeneous

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
#align mv_polynomial.pderiv_def MvPolynomial.pderiv_def

@[simp]
theorem pderiv_monomial {i : σ} :
    pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  classical
    simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
      ← (monomial _).map_smul]
    refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
    · simp [Pi.single_eq_of_ne hne]
    · rw [Finsupp.not_mem_support_iff] at hi; simp [hi]
    · simp
#align mv_polynomial.pderiv_monomial MvPolynomial.pderiv_monomial

lemma _root_.Finsupp.sub_add_single_one_cancel {m : σ →₀ ℕ} {i : σ} (hi : m i ≠ 0) :
    (m - single i 1) + single i 1 = m := by
  ext j; apply Nat.sub_add_cancel
  obtain rfl|hj := eq_or_ne i j
  · rw [Finsupp.single_eq_same]; omega
  · rw [Finsupp.single_eq_of_ne hj]; exact Nat.zero_le _

lemma X_mul_pderiv_monomial {i : σ} {m : σ →₀ ℕ} {r : R} :
    X i * pderiv i (monomial m r) = m i • monomial m r := by
  rw [pderiv_monomial, X, monomial_mul, smul_monomial]
  by_cases h : m i = 0
  · simp_rw [h, Nat.cast_zero, mul_zero, zero_smul, monomial_zero]
  rw [one_mul, mul_comm, nsmul_eq_mul, add_comm, sub_add_single_one_cancel h]

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
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_X MvPolynomial.pderiv_X

@[simp]
theorem pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ R) = 1 := by classical simp
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_X_self MvPolynomial.pderiv_X_self

@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ R) = 0 := by
  classical simp [h]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_X_of_ne MvPolynomial.pderiv_X_of_ne

theorem pderiv_eq_zero_of_not_mem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) :
    pderiv i f = 0 :=
  derivation_eq_zero_of_forall_mem_vars fun _ hj => pderiv_X_of_ne <| ne_of_mem_of_not_mem hj h
#align mv_polynomial.pderiv_eq_zero_of_not_mem_vars MvPolynomial.pderiv_eq_zero_of_not_mem_vars

theorem pderiv_monomial_single {i : σ} {n : ℕ} : pderiv i (monomial (single i n) a) =
    monomial (single i (n - 1)) (a * n) := by simp
#align mv_polynomial.pderiv_monomial_single MvPolynomial.pderiv_monomial_single

theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]
#align mv_polynomial.pderiv_mul MvPolynomial.pderiv_mul

theorem pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : ℕ} :
    pderiv i (f ^ n) = n * f ^ (n - 1) * pderiv i f := by
  rw [(pderiv i).leibniz_pow f n, nsmul_eq_mul, smul_eq_mul, mul_assoc]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (C a * f) = C a * pderiv i f := by
  rw [C_mul', Derivation.map_smul, C_mul']
set_option linter.uppercaseLean3 false in
#align mv_polynomial.pderiv_C_mul MvPolynomial.pderiv_C_mul

theorem pderiv_map {S} [CommSemiring S] {φ : R →+* S} {f : MvPolynomial σ R} {i : σ} :
    pderiv i (map φ f) = map φ (pderiv i f) := by
  apply induction_on f (fun r ↦ by simp) (fun p q hp hq ↦ by simp [hp, hq]) fun p j eq ↦ ?_
  obtain rfl | h := eq_or_ne j i
  · simp [eq]
  · simp [eq, h]

end PDeriv

lemma weightedDegree_sub_single_add {M} [AddCommMonoid M] {w : σ → M} {m : σ →₀ ℕ} {i : σ}
    (hi : m i ≠ 0) : (weightedDegree w) (m - .single i 1) + w i = weightedDegree w m := by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weightedDegree_apply]
  rw [sum_add_index', sum_single_index, one_smul, weightedDegree_apply]
  exacts [zero_smul .., fun _ ↦ zero_smul .., fun _ _ _ ↦ add_smul ..]

variable {M} [CommSemiring R] {φ : MvPolynomial σ R}

protected lemma IsWeightedHomogeneous.pderiv [AddCancelCommMonoid M] {w : σ → M} {n n' : M} {i : σ}
    (h : φ.IsWeightedHomogeneous w n) (h' : n' + w i = n) :
    (pderiv i φ).IsWeightedHomogeneous w n' := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    Finsupp.supported_eq_span_single] at h
  refine Submodule.span_induction h ?_ ?_ (fun p q hp hq ↦ ?_) fun r p h ↦ ?_
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i), h', ← hm, weightedDegree_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h

protected lemma IsHomogeneous.pderiv [AddCancelCommMonoid M] {n : ℕ} {i : σ}
    (h : φ.IsHomogeneous n) : (pderiv i φ).IsHomogeneous (n - 1) := by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff] at h
    rw [h, pderiv_C]; apply isHomogeneous_zero
  · exact IsWeightedHomogeneous.pderiv h rfl

variable [Fintype σ] {n : ℕ}

open Finset in
/-- Euler's identity for weighted homogeneous polynomials. -/
theorem IsWeightedHomogeneous.sum_weight_X_mul_pderiv {w : σ → ℕ}
    (h : φ.IsWeightedHomogeneous w n) : ∑ i : σ, w i • (X i * pderiv i φ) = n • φ := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    Finsupp.supported_eq_span_single] at h
  refine Submodule.span_induction h ?_ ?_ (fun p q hp hq ↦ ?_) fun r p h ↦ ?_
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← sum_smul, mul_comm (w _)]
    congr
    rwa [Set.mem_setOf, weightedDegree_apply, Finsupp.sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum, ← nsmul_eq_mul, h]

/-- Euler's identity for homogeneous polynomials. -/
theorem IsHomogeneous.sum_X_mul_pderiv (h : φ.IsHomogeneous n) :
    ∑ i : σ, X i * pderiv i φ = n • φ := by
  simp_rw [← h.sum_weight_X_mul_pderiv, Pi.one_apply, one_smul]

end MvPolynomial
